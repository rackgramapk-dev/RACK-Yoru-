import os
import re
import json
import time
import uuid
import hmac
import html
import random
import sqlite3
import hashlib
import threading
from urllib.parse import parse_qsl

import requests
from flask import request, jsonify, Response, send_file

BOT_USERNAME = "Kihoebot"
APP_SHORT_NAME = "play"
BASE_URL = os.environ.get("PUBLIC_URL") or "https://worker-production-0491.up.railway.app"

WIN_LINES = [
    (0, 1, 2), (3, 4, 5), (6, 7, 8),
    (0, 3, 6), (1, 4, 7), (2, 5, 8),
    (0, 4, 8), (2, 4, 6),
]

MAX_GAMES = 5000
GAME_TTL = 6 * 3600
ID_RE = re.compile(r"^[A-Za-z0-9_-]{4,64}$")

# ---- Bot difficulty (how often the bot plays smart) ----
BOT_WIN_CHANCE = 0.5      # takes a winning move only 50% of the time
BOT_BLOCK_CHANCE = 0.3    # blocks your winning move only 30% of the time
BOT_CENTER_CHANCE = 0.3   # grabs the centre only 30% of the time
BOT_DELAY = 0.8           # seconds the bot "thinks"

# ---- Leaderboard rules ----
PAIR_DAILY_LIMIT = 5      # max counted wins per day against the same player
IST = 5.5 * 3600          # day / week boundaries use Indian time
AVATAR_TTL = 24 * 3600


def _pick_data_dir():
    here = os.path.dirname(os.path.abspath(__file__))
    for p in ("/data", os.path.join(here, "data")):
        try:
            os.makedirs(p, exist_ok=True)
            probe = os.path.join(p, ".probe")
            open(probe, "w").close()
            os.remove(probe)
            return p
        except Exception:
            continue
    return here


DATA_DIR = _pick_data_dir()
DB_PATH = os.path.join(DATA_DIR, "games.db")
AV_DIR = os.path.join(DATA_DIR, "avatars")
try:
    os.makedirs(AV_DIR, exist_ok=True)
except Exception:
    pass

_games = {}
_lock = threading.Lock()
_cfg = {"token": None, "member_check": None}
_member_cache = {}


# ------------------------------------------------------------------ database

def _db():
    conn = sqlite3.connect(DB_PATH, timeout=10)
    return conn


def _db_init():
    conn = _db()
    try:
        c = conn.cursor()
        c.execute(
            "CREATE TABLE IF NOT EXISTS gplayers ("
            "uid INTEGER PRIMARY KEY, name TEXT, wins INTEGER DEFAULT 0, "
            "played INTEGER DEFAULT 0, streak INTEGER DEFAULT 0, best INTEGER DEFAULT 0)"
        )
        c.execute(
            "CREATE TABLE IF NOT EXISTS gresults ("
            "id INTEGER PRIMARY KEY AUTOINCREMENT, uid INTEGER, opp_uid INTEGER, "
            "opp_name TEXT, res TEXT, mode TEXT, counted INTEGER DEFAULT 0, ts REAL)"
        )
        c.execute("CREATE INDEX IF NOT EXISTS gr_uid ON gresults(uid, ts)")
        c.execute("CREATE INDEX IF NOT EXISTS gr_win ON gresults(res, counted, ts)")
        conn.commit()
    finally:
        conn.close()


def _day_start(now):
    day = int((now + IST) // 86400)
    return day * 86400 - IST


def _week_start(now):
    day = int((now + IST) // 86400)
    weekday = (day + 3) % 7  # 1970-01-01 was a Thursday; Monday = 0
    return (day - weekday) * 86400 - IST


def _record(uid, name, opp_uid, opp_name, res, mode):
    """Save one finished round for one player. res: W / L / D."""
    now = time.time()
    conn = _db()
    try:
        c = conn.cursor()
        counted = 0
        stats = {"mode": mode}
        if mode == "pvp":
            c.execute("INSERT OR IGNORE INTO gplayers (uid, name) VALUES (?, ?)", (uid, name))
            if res == "W":
                n = c.execute(
                    "SELECT COUNT(*) FROM gresults WHERE uid=? AND opp_uid=? AND res='W' "
                    "AND counted=1 AND ts>=?",
                    (uid, opp_uid, _day_start(now)),
                ).fetchone()[0]
                counted = 1 if n < PAIR_DAILY_LIMIT else 0
            wins, played, streak, best = c.execute(
                "SELECT wins, played, streak, best FROM gplayers WHERE uid=?", (uid,)
            ).fetchone()
            played += 1
            if res == "W":
                streak += 1
                wins += counted
            elif res == "L":
                streak = 0
            best = max(best, streak)
            c.execute(
                "UPDATE gplayers SET name=?, wins=?, played=?, streak=?, best=? WHERE uid=?",
                (name, wins, played, streak, best, uid),
            )
            rank = c.execute("SELECT COUNT(*) + 1 FROM gplayers WHERE wins>?", (wins,)).fetchone()[0]
            stats.update({"wins": wins, "streak": streak, "rank": rank, "counted": bool(counted)})
        c.execute(
            "INSERT INTO gresults (uid, opp_uid, opp_name, res, mode, counted, ts) VALUES (?,?,?,?,?,?,?)",
            (uid, opp_uid, opp_name, res, mode, counted, now),
        )
        conn.commit()
        return stats
    finally:
        conn.close()


def _board(uid, mode):
    now = time.time()
    conn = _db()
    try:
        c = conn.cursor()
        if mode == "wk":
            since = _week_start(now)
            rows = c.execute(
                "SELECT r.uid, p.name, COUNT(*) AS w FROM gresults r JOIN gplayers p ON p.uid=r.uid "
                "WHERE r.res='W' AND r.counted=1 AND r.ts>=? GROUP BY r.uid ORDER BY w DESC, r.uid LIMIT 20",
                (since,),
            ).fetchall()
            mine = c.execute(
                "SELECT COUNT(*) FROM gresults WHERE uid=? AND res='W' AND counted=1 AND ts>=?",
                (uid, since),
            ).fetchone()[0]
            rank = None
            if mine > 0:
                rank = c.execute(
                    "SELECT COUNT(*) + 1 FROM (SELECT uid, COUNT(*) AS w FROM gresults "
                    "WHERE res='W' AND counted=1 AND ts>=? GROUP BY uid HAVING w>?)",
                    (since, mine),
                ).fetchone()[0]
        else:
            rows = c.execute(
                "SELECT uid, name, wins FROM gplayers WHERE wins>0 ORDER BY wins DESC, uid LIMIT 20"
            ).fetchall()
            row = c.execute("SELECT wins FROM gplayers WHERE uid=?", (uid,)).fetchone()
            mine = row[0] if row else 0
            rank = None
            if mine > 0:
                rank = c.execute("SELECT COUNT(*) + 1 FROM gplayers WHERE wins>?", (mine,)).fetchone()[0]
        prow = c.execute("SELECT played, wins, streak FROM gplayers WHERE uid=?", (uid,)).fetchone()
        played, total_wins, streak = prow if prow else (0, 0, 0)
        rate = int(round(100.0 * total_wins / played)) if played else 0
        lst = [
            {"uid": r[0], "name": (r[1] or "Player")[:20], "wins": r[2],
             "avatar": _avatar_url(r[0]), "me": r[0] == uid}
            for r in rows
        ]
        me = {"rank": rank, "wins": mine, "played": played, "rate": rate, "streak": streak}
        return {"list": lst, "me": me}
    finally:
        conn.close()


def _history(uid):
    conn = _db()
    try:
        rows = conn.execute(
            "SELECT res, opp_name, mode, ts FROM gresults WHERE uid=? ORDER BY ts DESC LIMIT 40",
            (uid,),
        ).fetchall()
        return [{"res": r[0], "opp": r[1] or "Player", "mode": r[2], "ts": r[3]} for r in rows]
    finally:
        conn.close()


# ------------------------------------------------------------------ avatars

def _sig(uid):
    key = (_cfg["token"] or "").encode()
    return hmac.new(key, b"avatar:" + str(uid).encode(), hashlib.sha256).hexdigest()[:16]


def _avatar_url(uid):
    if not uid or not _cfg["token"]:
        return None
    return "/api/avatar/%d?s=%s" % (uid, _sig(uid))


def _fetch_avatar(uid, path):
    tok = _cfg["token"]
    base = "https://api.telegram.org/bot" + tok + "/"
    try:
        r = requests.get(base + "getUserProfilePhotos", params={"user_id": uid, "limit": 1}, timeout=8).json()
        photos = (r.get("result") or {}).get("photos") if r.get("ok") else None
        if not photos:
            return False
        sizes = photos[0]
        pick = next((s for s in sizes if s.get("width", 0) >= 160), sizes[-1])
        f = requests.get(base + "getFile", params={"file_id": pick["file_id"]}, timeout=8).json()
        fp = f["result"]["file_path"]
        img = requests.get("https://api.telegram.org/file/bot" + tok + "/" + fp, timeout=10)
        if img.status_code != 200 or not img.content:
            return False
        tmp = path + ".tmp"
        with open(tmp, "wb") as fh:
            fh.write(img.content)
        os.replace(tmp, path)
        return True
    except Exception:
        return False


def api_avatar(uid):
    if not hmac.compare_digest(request.args.get("s", ""), _sig(uid)):
        return Response("Forbidden", status=403)
    path = os.path.join(AV_DIR, "%d.jpg" % uid)
    none = path + ".none"
    now = time.time()

    def fresh(p, ttl):
        return os.path.exists(p) and now - os.path.getmtime(p) < ttl

    if not fresh(path, AVATAR_TTL):
        if fresh(none, 6 * 3600) and not os.path.exists(path):
            return Response("No photo", status=404)
        if not _fetch_avatar(uid, path):
            if not os.path.exists(path):
                try:
                    open(none, "w").close()
                except Exception:
                    pass
                return Response("No photo", status=404)
            os.utime(path, None)
    resp = send_file(path, mimetype="image/jpeg")
    resp.headers["Cache-Control"] = "private, max-age=3600"
    return resp


# ------------------------------------------------------------------ game state

def new_game_id():
    return uuid.uuid4().hex[:12]


def game_link(gid):
    return "https://t.me/" + BOT_USERNAME + "/" + APP_SHORT_NAME + "?startapp=" + gid


def _new_game(gid, mode="pvp"):
    return {
        "id": gid,
        "mode": mode,
        "board": [""] * 9,
        "players": {"X": None, "O": None},
        "turn": "X",
        "starter": "X",
        "winner": None,
        "line": None,
        "score": {"X": 0, "O": 0},
        "round": 1,
        "recorded": False,
        "stats": {},
        "bot_at": 0,
        "inline": None,
        "updated": time.time(),
    }


def _cleanup():
    now = time.time()
    old = [k for k, g in _games.items() if now - g["updated"] > GAME_TTL]
    for k in old:
        _games.pop(k, None)


def _name(user):
    n = user.get("first_name") or user.get("username") or "Player"
    return str(n)[:20]


def _sym_of(g, uid):
    for sym, p in g["players"].items():
        if p and p["id"] == uid:
            return sym
    return None


def _public(g, uid):
    sym = _sym_of(g, uid)
    players = {}
    for k, v in g["players"].items():
        if v:
            players[k] = {"name": v["name"], "avatar": _avatar_url(v["id"]), "bot": v["id"] == 0}
        else:
            players[k] = None
    return {
        "board": g["board"],
        "turn": g["turn"],
        "winner": g["winner"],
        "line": g["line"],
        "score": g["score"],
        "round": g["round"],
        "mode": g["mode"],
        "you": sym,
        "stats": g["stats"].get(uid),
        "players": players,
    }


def _verify(init_data, max_age=86400):
    token = _cfg["token"]
    if not init_data or not token:
        return None
    try:
        data = dict(parse_qsl(init_data, keep_blank_values=True))
        got = data.pop("hash", None)
        if not got:
            return None
        check = "\n".join(k + "=" + v for k, v in sorted(data.items()))
        secret = hmac.new(b"WebAppData", token.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, got):
            return None
        if time.time() - int(data.get("auth_date", "0")) > max_age:
            return None
        user = json.loads(data["user"])
        if not isinstance(user.get("id"), int):
            return None
        return user
    except Exception:
        return None


def _member_ok(uid):
    check = _cfg["member_check"]
    if check is None:
        return True
    now = time.time()
    hit = _member_cache.get(uid)
    if hit and now - hit[0] < (300 if hit[1] else 20):
        return hit[1]
    ok = False
    try:
        ok = bool(check(uid))
    except Exception:
        ok = False
    _member_cache[uid] = (now, ok)
    return ok


def _needs_seat(gid, uid):
    with _lock:
        g = _games.get(gid)
        if g is None:
            return True
        if _sym_of(g, uid):
            return False
        if g["mode"] == "bot":
            return False
        if g["players"]["X"] and g["players"]["O"]:
            return False
    return True


# ------------------------------------------------------------------ chat message

def _dash_link():
    return "https://t.me/" + BOT_USERNAME + "/" + APP_SHORT_NAME + "?startapp=dash"


def _caption_text(g):
    px, po = g["players"]["X"], g["players"]["O"]
    xn = html.escape(px["name"]) if px else "Player 1"
    if not po:
        text = "🎮 <b>Tic-Tac-Toe</b>\n" + xn + " is waiting for an opponent.\n\n<i>Tap Play to join this match.</i>"
        return text, [[("Play", game_link(g["id"]))]]
    on = html.escape(po["name"])
    sc = xn + " " + str(g["score"]["X"]) + " - " + str(g["score"]["O"]) + " " + on
    link = game_link(g["id"])
    if g["winner"] is None:
        text = (
            "🎮 <b>Tic-Tac-Toe</b>\n" + xn + " vs " + on +
            "\nStatus: In progress | Score: " + str(g["score"]["X"]) + " - " + str(g["score"]["O"]) +
            "\n\n<i>Tap Open game to make your move.</i>"
        )
        return text, [[("Open game", link)]]
    if g["winner"] == "draw":
        text = "🎮 <b>Tic-Tac-Toe</b>\nThis round ended in a draw.\n" + sc + "\n\n<i>Tap Open game to play a rematch.</i>"
    else:
        w = px if g["winner"] == "X" else po
        text = "🏆 <b>" + html.escape(w["name"]) + " won this round</b>\n" + sc + "\n\n<i>Tap Open game to play a rematch.</i>"
    return text, [[("Open game", link), ("🏆 Dashboard", _dash_link())]]


def _edit_payload(g):
    inline_id = g.get("inline")
    if not inline_id:
        return None
    text, rows = _caption_text(g)
    return {
        "inline_message_id": inline_id,
        "caption": text,
        "parse_mode": "HTML",
        "reply_markup": {"inline_keyboard": [[{"text": t, "url": u} for t, u in row] for row in rows]},
    }


def _send_edit(payload):
    if not payload or not _cfg["token"]:
        return

    def work():
        base = "https://api.telegram.org/bot" + _cfg["token"] + "/"
        try:
            r = requests.post(base + "editMessageCaption", json=payload, timeout=10)
            if not r.json().get("ok"):
                alt = dict(payload)
                alt["text"] = alt.pop("caption")
                requests.post(base + "editMessageText", json=alt, timeout=10)
        except Exception:
            pass

    threading.Thread(target=work, daemon=True).start()


def attach_inline(gid, inline_id, uid, name):
    with _lock:
        _cleanup()
        g = _games.get(gid)
        if g is None:
            g = _new_game(gid)
            _games[gid] = g
            g["players"]["X"] = {"id": uid, "name": name}
        g["inline"] = inline_id
        if g["players"]["X"] is None and _sym_of(g, uid) is None:
            g["players"]["X"] = {"id": uid, "name": name}
        g["updated"] = time.time()


# ------------------------------------------------------------------ rules + bot

def _finish(g, w):
    """Called once when a round ends. Saves results to the database."""
    if g["recorded"]:
        return
    g["recorded"] = True
    px, po = g["players"]["X"], g["players"]["O"]
    for sym, me, opp in (("X", px, po), ("O", po, px)):
        if not me or me["id"] == 0 or not opp:
            continue
        res = "D" if w == "draw" else ("W" if w == sym else "L")
        try:
            g["stats"][me["id"]] = _record(me["id"], me["name"], opp["id"], opp["name"], res, g["mode"])
        except Exception as e:
            print("games: could not save result:", e)


def _apply(g, cell, sym):
    g["board"][cell] = sym
    line = None
    for ln in WIN_LINES:
        if all(g["board"][i] == sym for i in ln):
            line = ln
            break
    if line:
        g["winner"] = sym
        g["line"] = list(line)
        g["score"][sym] += 1
        _finish(g, sym)
        return _edit_payload(g)
    if all(g["board"]):
        g["winner"] = "draw"
        _finish(g, "draw")
        return _edit_payload(g)
    g["turn"] = "O" if sym == "X" else "X"
    return None


def _bot_pick(board):
    empty = [i for i, v in enumerate(board) if v == ""]
    for sym, chance in (("O", BOT_WIN_CHANCE), ("X", BOT_BLOCK_CHANCE)):
        for ln in WIN_LINES:
            vals = [board[i] for i in ln]
            if vals.count(sym) == 2 and vals.count("") == 1 and random.random() < chance:
                return ln[vals.index("")]
    if board[4] == "" and random.random() < BOT_CENTER_CHANCE:
        return 4
    return random.choice(empty)


def _bot_tick(g):
    if g["mode"] != "bot" or g["winner"] is not None or g["turn"] != "O":
        return
    if time.time() < g["bot_at"]:
        return
    _apply(g, _bot_pick(g["board"]), "O")
    g["updated"] = time.time()


def _read_request():
    data = request.get_json(silent=True) or {}
    user = _verify(str(data.get("initData", "")))
    gid = str(data.get("game_id", ""))
    return data, user, gid


# ------------------------------------------------------------------ api

def api_state():
    data, user, gid = _read_request()
    if not user:
        return jsonify({"error": "bad_auth"})
    if not ID_RE.match(gid):
        return jsonify({"error": "no_game"})
    uid = user["id"]
    if _needs_seat(gid, uid) and not _member_ok(uid):
        return jsonify({"error": "join_required"})
    edit = None
    with _lock:
        g = _games.get(gid)
        if g is None:
            _cleanup()
            if len(_games) >= MAX_GAMES:
                return jsonify({"error": "busy"})
            g = _new_game(gid)
            _games[gid] = g
        _bot_tick(g)
        if _sym_of(g, uid) is None and g["mode"] == "pvp":
            seat = {"id": uid, "name": _name(user)}
            if g["players"]["X"] is None:
                g["players"]["X"] = seat
            elif g["players"]["O"] is None:
                g["players"]["O"] = seat
                edit = _edit_payload(g)
        g["updated"] = time.time()
        out = _public(g, uid)
    _send_edit(edit)
    return jsonify(out)


def api_move():
    data, user, gid = _read_request()
    if not user:
        return jsonify({"error": "bad_auth"})
    if not ID_RE.match(gid):
        return jsonify({"error": "no_game"})
    cell = data.get("cell")
    edit = None
    with _lock:
        g = _games.get(gid)
        if g is None:
            return jsonify({"error": "no_game"})
        _bot_tick(g)
        sym = _sym_of(g, user["id"])
        valid = (
            isinstance(cell, int) and not isinstance(cell, bool) and 0 <= cell <= 8
            and sym is not None
            and g["players"]["X"] and g["players"]["O"]
            and g["winner"] is None
            and g["turn"] == sym
            and g["board"][cell] == ""
        )
        if valid:
            edit = _apply(g, cell, sym)
            if g["mode"] == "bot" and g["winner"] is None:
                g["bot_at"] = time.time() + BOT_DELAY
            g["updated"] = time.time()
        out = _public(g, user["id"])
    _send_edit(edit)
    return jsonify(out)


def api_rematch():
    data, user, gid = _read_request()
    if not user:
        return jsonify({"error": "bad_auth"})
    if not ID_RE.match(gid):
        return jsonify({"error": "no_game"})
    edit = None
    with _lock:
        g = _games.get(gid)
        if g is None:
            return jsonify({"error": "no_game"})
        if _sym_of(g, user["id"]) and g["winner"] is not None:
            g["board"] = [""] * 9
            g["winner"] = None
            g["line"] = None
            g["recorded"] = False
            g["stats"] = {}
            g["round"] += 1
            g["starter"] = "O" if g["starter"] == "X" else "X"
            g["turn"] = g["starter"]
            if g["mode"] == "bot" and g["turn"] == "O":
                g["bot_at"] = time.time() + BOT_DELAY
            g["updated"] = time.time()
            edit = _edit_payload(g)
        out = _public(g, user["id"])
    _send_edit(edit)
    return jsonify(out)


def _create_room(user, mode):
    uid = user["id"]
    with _lock:
        _cleanup()
        if len(_games) >= MAX_GAMES:
            return None
        gid = new_game_id()
        g = _new_game(gid, mode)
        g["players"]["X"] = {"id": uid, "name": _name(user)}
        if mode == "bot":
            g["players"]["O"] = {"id": 0, "name": "Bot"}
        _games[gid] = g
    return gid


def api_bot_new():
    data, user, gid = _read_request()
    if not user:
        return jsonify({"error": "bad_auth"})
    if not _member_ok(user["id"]):
        return jsonify({"error": "join_required"})
    new = _create_room(user, "bot")
    if not new:
        return jsonify({"error": "busy"})
    return jsonify({"game_id": new})


def api_new():
    data, user, gid = _read_request()
    if not user:
        return jsonify({"error": "bad_auth"})
    if not _member_ok(user["id"]):
        return jsonify({"error": "join_required"})
    new = _create_room(user, "pvp")
    if not new:
        return jsonify({"error": "busy"})
    return jsonify({"game_id": new, "link": game_link(new)})


def api_board():
    data, user, gid = _read_request()
    if not user:
        return jsonify({"error": "bad_auth"})
    mode = "wk" if data.get("mode") == "wk" else "all"
    try:
        return jsonify(_board(user["id"], mode))
    except Exception as e:
        print("games: board failed:", e)
        return jsonify({"error": "busy"})


def api_history():
    data, user, gid = _read_request()
    if not user:
        return jsonify({"error": "bad_auth"})
    try:
        return jsonify({"items": _history(user["id"])})
    except Exception as e:
        print("games: history failed:", e)
        return jsonify({"error": "busy"})


# ------------------------------------------------------------------ pages

def page_game():
    body = GAME_HTML.replace("__APP_LINK__", "https://t.me/" + BOT_USERNAME + "/" + APP_SHORT_NAME)
    resp = Response(body, mimetype="text/html")
    resp.headers["Cache-Control"] = "no-store"
    return resp


def _static(name, mime):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), name)
    if not os.path.exists(path):
        return Response("Not found", status=404)
    return send_file(path, mimetype=mime)


def page_logo():
    return _static("logo.png", "image/png")


def page_photo():
    return _static("game.jpg", "image/jpeg")


def setup(flask_app, bot_token, member_check=None):
    _cfg["token"] = bot_token
    _cfg["member_check"] = member_check
    try:
        _db_init()
    except Exception as e:
        print("games: database init failed:", e)
    original_home = flask_app.view_functions.get("home")

    def root():
        if request.args.get("tgWebAppStartParam"):
            return page_game()
        return original_home() if original_home else "Bot is Alive!"

    if original_home:
        flask_app.view_functions["home"] = root
    else:
        flask_app.add_url_rule("/", "game_root", root, methods=["GET"])
    add = flask_app.add_url_rule
    add("/game", "game_page", page_game, methods=["GET"])
    add("/logo.png", "game_logo", page_logo, methods=["GET"])
    add("/game.jpg", "game_photo", page_photo, methods=["GET"])
    add("/api/avatar/<int:uid>", "game_avatar", api_avatar, methods=["GET"])
    add("/api/state", "game_state", api_state, methods=["POST"])
    add("/api/move", "game_move", api_move, methods=["POST"])
    add("/api/rematch", "game_rematch", api_rematch, methods=["POST"])
    add("/api/bot/new", "game_bot_new", api_bot_new, methods=["POST"])
    add("/api/new", "game_new", api_new, methods=["POST"])
    add("/api/board", "game_board", api_board, methods=["POST"])
    add("/api/history", "game_history", api_history, methods=["POST"])


def register_handlers(app, is_member, guard=None):
    from telegram import (
        InlineQueryResultArticle,
        InlineQueryResultPhoto,
        InputTextMessageContent,
        InlineKeyboardMarkup,
        InlineKeyboardButton,
    )
    from telegram import SwitchInlineQueryChosenChat
    from telegram.ext import InlineQueryHandler, ChosenInlineResultHandler, CommandHandler

    async def inline_query(update, context):
        q = update.inline_query
        user = q.from_user
        if not await is_member(user.id, context):
            res = InlineQueryResultArticle(
                id="join",
                title="Join required",
                description="Join our channels and groups to play",
                input_message_content=InputTextMessageContent(
                    "Join our channels and groups to use @" + BOT_USERNAME + ":\n"
                    "@racksun19\n@WEAYing\n@racksungroup\n@rackcraft"
                ),
            )
            await q.answer([res], cache_time=0, is_personal=True)
            return
        gid = new_game_id()
        name = (user.first_name or user.username or "Player")[:20]
        markup = InlineKeyboardMarkup([[InlineKeyboardButton("Play", url=game_link(gid))]])
        res = InlineQueryResultPhoto(
            id=gid,
            photo_url=BASE_URL + "/game.jpg",
            thumbnail_url=BASE_URL + "/game.jpg",
            photo_width=736,
            photo_height=460,
            title="Tic-Tac-Toe",
            description="Play with a friend",
            caption="🎮 <b>Tic-Tac-Toe</b>\n" + html.escape(name) +
                    " is waiting for an opponent.\n\n<i>Tap Play to join this match.</i>",
            parse_mode="HTML",
            reply_markup=markup,
        )
        await q.answer([res], cache_time=0, is_personal=True)

    async def chosen_inline(update, context):
        r = update.chosen_inline_result
        if not r or not r.inline_message_id or r.result_id == "join":
            return
        u = r.from_user
        attach_inline(
            r.result_id,
            r.inline_message_id,
            u.id,
            (u.first_name or u.username or "Player")[:20],
        )

    async def games_command(update, context):
        if guard is not None and not await guard(update, context):
            return
        markup = InlineKeyboardMarkup([
            [
                InlineKeyboardButton(
                    "Play Tic-Tac-Toe",
                    switch_inline_query_chosen_chat=SwitchInlineQueryChosenChat(
                        query="",
                        allow_user_chats=True,
                        allow_group_chats=True,
                        allow_channel_chats=False,
                        allow_bot_chats=False,
                    ),
                )
            ],
            [
                InlineKeyboardButton("Play vs Bot", url=game_link("bot")),
                InlineKeyboardButton("Leaderboard", url=game_link("dash")),
            ],
        ])
        await update.message.reply_text(
            "*Games*\n\nPick a game, then choose a friend or a group to play with.",
            reply_markup=markup,
            parse_mode="Markdown",
        )

    app.add_handler(CommandHandler("games", games_command))
    app.add_handler(InlineQueryHandler(inline_query))
    app.add_handler(ChosenInlineResultHandler(chosen_inline))


GAME_HTML = r"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no, viewport-fit=cover">
<title>Tic-Tac-Toe</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
:root{--bg:#eef0f4;--card:#fff;--fg:#14161a;--hint:#6b7280;--line:rgba(0,0,0,.09);--x:#3b82f6;--o:#f0643c;--acc:#3390ec}
@media(prefers-color-scheme:dark){:root:not([data-theme="light"]){--bg:#0e1014;--card:#1a1d24;--fg:#f2f3f5;--hint:#8b93a1;--line:rgba(255,255,255,.09)}}
:root[data-theme="dark"]{--bg:#0e1014;--card:#1a1d24;--fg:#f2f3f5;--hint:#8b93a1;--line:rgba(255,255,255,.09)}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html,body{height:100%;margin:0}
body{background:var(--bg);color:var(--fg);font:15px/1.4 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;overflow:hidden}
.bg{position:fixed;inset:0;overflow:hidden;pointer-events:none}.bg.off{display:none}
.blob{position:absolute;width:60vmax;height:60vmax;border-radius:50%;filter:blur(70px);opacity:.3;animation:drift 16s ease-in-out infinite alternate}
.b1{background:var(--x);left:-20vmax;top:-20vmax}.b2{background:var(--o);right:-25vmax;bottom:-25vmax;animation-delay:-8s}
.fl{position:absolute;bottom:-60px;opacity:.16;animation:up linear infinite}
@keyframes drift{to{transform:translate(12vmax,8vmax) scale(1.2)}}
@keyframes up{to{transform:translateY(-115vh) rotate(360deg)}}
@keyframes fade{from{opacity:0;transform:translateY(8px)}}
@keyframes pop{0%{transform:scale(.75);opacity:0}60%{transform:scale(1.07)}100%{transform:scale(1);opacity:1}}
@keyframes draw{to{stroke-dashoffset:0}}
@keyframes bob{50%{transform:translateY(-7px)}}
@keyframes jump{0%,100%{transform:translateY(0)}40%{transform:translateY(-14px)}}
@keyframes wave{50%{transform:rotate(-16deg)}}
@keyframes wave2{50%{transform:rotate(16deg)}}
@keyframes twinkle{0%,100%{transform:scale(.3);opacity:.2}50%{transform:scale(1);opacity:1}}
@keyframes orbit{to{transform:rotate(360deg)}}
@keyframes soul{0%{transform:translateY(8px);opacity:0}30%{opacity:.9}100%{transform:translateY(-34px);opacity:0}}
@keyframes grow{from{height:0}}
@keyframes wid{from{width:0}}
@keyframes shine{0%,100%{filter:drop-shadow(0 0 0 rgba(245,179,1,0))}50%{filter:drop-shadow(0 0 12px rgba(245,179,1,.9))}}
.app{position:relative;max-width:430px;margin:0 auto;height:100%;display:flex;flex-direction:column;padding-top:env(safe-area-inset-top,0px)}
.view{flex:1;overflow:auto;padding:14px 16px 16px;display:none}.view.on{display:block;animation:fade .35s}
.btn{font:inherit;font-weight:600;border:1px solid var(--line);border-radius:12px;padding:12px;background:var(--card);color:var(--fg);cursor:pointer;transition:transform .12s;display:flex;align-items:center;justify-content:center;gap:6px}
.btn:active{transform:scale(.94)}.btn[hidden]{display:none}.btn.p{background:var(--acc);color:#fff;border-color:transparent}.btn.s{padding:5px 11px;font-size:12px;border-radius:8px}
.card{background:var(--card);border:1px solid var(--line);border-radius:16px}
.ic{width:20px;height:20px;flex:none;transition:transform .15s}
.prow{display:grid;grid-template-columns:1fr auto 1fr;gap:8px;align-items:center;margin-bottom:16px}
.pl{display:flex;align-items:center;gap:8px;padding:8px 10px;min-width:0;border:1.5px solid var(--line);transition:all .3s}
.pl.onx{border-color:var(--x);box-shadow:0 0 16px -2px var(--x);transform:translateY(-2px)}.pl.ono{border-color:var(--o);box-shadow:0 0 16px -2px var(--o);transform:translateY(-2px)}
.av{position:relative;overflow:hidden;border-radius:50%;display:flex;align-items:center;justify-content:center;font-weight:700;flex:none;margin:0 auto 4px}
.av img{position:absolute;inset:0;width:100%;height:100%;object-fit:cover}
.pl .av{margin:0}.row .av{margin:0}
.nm{font-size:13px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.sy{font-size:12px;font-weight:700}
.sc{font-size:22px;font-weight:700;min-width:48px;text-align:center}
.board{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:10px}
.cell{aspect-ratio:1;padding:0;background:var(--card);border:1px solid var(--line);border-radius:16px;display:flex;align-items:center;justify-content:center;cursor:pointer;transition:transform .12s,opacity .3s,box-shadow .3s}
.cell:disabled{cursor:default}.cell:not(:disabled):active{transform:scale(.88)}.cell svg{width:56%;height:56%}.pop{animation:pop .3s ease-out}.dim{opacity:.35}
.winX{box-shadow:0 0 0 2px var(--x),0 0 20px var(--x)}.winO{box-shadow:0 0 0 2px var(--o),0 0 20px var(--o)}
.mark path,.mark circle{stroke-dasharray:1;stroke-dashoffset:1;animation:draw .3s ease-out forwards}
.st{text-align:center;font-size:17px;font-weight:700;margin:16px 0 2px}.sub{text-align:center;font-size:12px;color:var(--hint);min-height:17px}
.acts{display:flex;gap:8px;margin-top:12px}.acts .btn{flex:1;font-size:13px;padding:11px 6px}
.nav{display:flex;background:var(--card);border-top:1px solid var(--line);padding-bottom:env(safe-area-inset-bottom,0px)}
.tab{flex:1;border:0;background:none;color:var(--hint);font:inherit;font-size:12px;padding:9px 0;display:flex;flex-direction:column;align-items:center;gap:2px;cursor:pointer;transition:color .2s}.tab.on{color:var(--acc)}.tab:active .ic{transform:scale(.8)}
.ov{position:absolute;inset:0;z-index:20;display:none;align-items:center;justify-content:center;background:rgba(0,0,0,.6);backdrop-filter:blur(6px);padding:20px}.ov.on{display:flex;animation:fade .3s}
.res{width:100%;text-align:center;padding:18px 16px;animation:pop .5s cubic-bezier(.2,1.4,.4,1);position:relative}
.rt{font-size:32px;font-weight:800;margin:2px 0 2px;animation:pop .6s .15s cubic-bezier(.2,1.5,.4,1) both}
.chips{display:flex;flex-wrap:wrap;gap:6px;justify-content:center;margin:10px 0 4px;min-height:4px}
.chip{font-size:12px;font-weight:700;padding:4px 10px;border-radius:20px;animation:pop .4s both}
.won{background:rgba(34,197,94,.18);color:#16a34a}.lost{background:rgba(226,75,74,.18);color:#e24b4a}.dr{background:var(--line);color:var(--hint)}.warn{background:rgba(245,179,1,.2);color:#d99a00}.acc{background:rgba(51,144,236,.18);color:var(--acc)}
#cf{position:absolute;inset:0;width:100%;height:100%;pointer-events:none;z-index:21}
.seg{display:flex;background:var(--card);border:1px solid var(--line);border-radius:12px;padding:3px}.seg button{flex:1;border:0;background:none;color:var(--hint);padding:7px;border-radius:9px;font:inherit;font-weight:600;cursor:pointer;transition:all .2s}.seg .on{background:var(--acc);color:#fff}
.pod{display:flex;align-items:flex-end;gap:8px;margin:16px 0 14px}.pc{flex:1;text-align:center;min-width:0}
.step{border-radius:12px 12px 0 0;display:flex;align-items:center;justify-content:center;font-size:22px;font-weight:800;color:#fff;animation:grow .8s cubic-bezier(.2,.9,.3,1) both}
.row{display:flex;align-items:center;gap:10px;padding:10px 12px;margin-bottom:8px;animation:fade .4s both}.row .g{flex:1;min-width:0}.row>b{width:20px;color:var(--hint)}
.bar{display:block;height:5px;border-radius:3px;background:var(--line);margin-top:5px;overflow:hidden}.bar b{display:block;height:100%;background:var(--acc);border-radius:3px;animation:wid .9s both}
.me{border-color:var(--acc);box-shadow:0 0 14px -4px var(--acc)}
.hero{padding:14px;display:flex;align-items:center;gap:14px;margin:12px 0 0}.hero .big{font-size:34px;font-weight:800;color:var(--acc)}
.stats{display:flex;gap:14px;margin-left:auto;text-align:center;font-size:11px;color:var(--hint)}.stats b{display:block;font-size:16px;color:var(--fg)}
.set{display:flex;align-items:center;gap:12px;padding:14px;margin-bottom:8px;width:100%;text-align:left;font:inherit;color:var(--fg);cursor:pointer}
.set span{flex:1}.tg{width:44px;height:26px;border-radius:13px;background:var(--line);position:relative;transition:background .2s;flex:none}
.tg:after{content:"";position:absolute;top:3px;left:3px;width:20px;height:20px;border-radius:50%;background:#fff;transition:left .2s}.tg.on{background:var(--acc)}.tg.on:after{left:21px}
.h1{font-size:18px;font-weight:700;margin:4px 0 12px;display:flex;align-items:center;gap:8px}
.empty{text-align:center;color:var(--hint);padding:30px 10px}
.toast{position:fixed;left:50%;bottom:90px;transform:translateX(-50%);background:var(--fg);color:var(--bg);padding:8px 14px;border-radius:20px;font-size:13px;opacity:0;transition:opacity .3s;pointer-events:none;z-index:50;max-width:90%;text-align:center}.toast.on{opacity:1}
@media(prefers-reduced-motion:reduce){*{animation-duration:.01ms!important}}
</style></head><body>
<div class="bg" id="bg"><i class="blob b1"></i><i class="blob b2"></i></div>
<div class="app">
<div class="view on" id="vg">
<div class="prow"><div class="card pl" id="pX"></div><div class="sc" id="sc">0 : 0</div><div class="card pl" id="pO"></div></div>
<div class="board" id="bd"></div>
<div class="st" id="st">Loading…</div><div class="sub" id="sub"></div>
<div class="acts"><button class="btn p" id="rm" hidden>Rematch</button></div>
<div class="acts"><button class="btn" id="vb" data-i="r">Vs bot</button><button class="btn" id="inv" data-i="u">Invite</button><button class="btn" data-go="d" data-i="t">Leaderboard</button></div>
</div>
<div class="view" id="vd"><div class="seg" id="seg"><button class="on" data-m="all">All-time</button><button data-m="wk">This week</button></div><div id="dash"></div></div>
<div class="view" id="vs"><div class="h1">Settings</div>
<button class="card set" id="hb" data-i="c"><span>Match history</span><svg class="ic" viewBox="0 0 24 24" fill="none" stroke="var(--hint)" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M9 6l6 6-6 6"/></svg></button>
<div class="card set" data-k="bg"><span>Animated background</span><i class="tg"></i></div>
<div class="card set" data-k="snd"><span>Sound effects</span><i class="tg"></i></div>
<div class="card set" data-k="vib"><span>Vibration</span><i class="tg"></i></div>
<div class="seg" id="th" style="margin-top:12px"><button data-th="auto">Auto</button><button data-th="light">Light</button><button data-th="dark">Dark</button></div></div>
<div class="view" id="vh"><div class="h1"><button class="btn s" id="bk" data-i="b" style="padding:6px" aria-label="Back"></button>Match history</div><div id="hl"></div></div>
<nav class="nav"><button class="tab on" data-go="g" data-i="g"><span>Game</span></button><button class="tab" data-go="d" data-i="t"><span>Dashboard</span></button><button class="tab" data-go="s" data-i="s"><span>Settings</span></button></nav>
<div class="ov" id="ov"><canvas id="cf"></canvas><div class="card res" id="res"></div></div>
</div>
<div class="toast" id="ts"></div>
<script>
(function(){
var tg=window.Telegram&&window.Telegram.WebApp;
if(tg){try{tg.ready();tg.expand()}catch(e){}}
var initData=tg?tg.initData:"";
var gid="";
try{gid=(tg.initDataUnsafe&&tg.initDataUnsafe.start_param)||""}catch(e){}
if(!gid){var qs=new URLSearchParams(location.search);gid=qs.get("tgWebAppStartParam")||qs.get("g")||""}
var APP="__APP_LINK__";
var $=function(i){return document.getElementById(i)};
var esc=function(s){return String(s).replace(/[&<>"]/g,function(c){return{"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]})};
var set={bg:1,snd:1,vib:1,th:"auto"};
try{var sv=JSON.parse(localStorage.getItem("ttt_set")||"{}");for(var k0 in sv)set[k0]=sv[k0]}catch(e){}
function save(){try{localStorage.setItem("ttt_set",JSON.stringify(set))}catch(e){}}
function theme(){var m=set.th,r=document.documentElement;if(m==="auto")m=(tg&&tg.colorScheme)||"";if(m)r.setAttribute("data-theme",m);else r.removeAttribute("data-theme");try{if(tg){var c=m==="light"?"#eef0f4":"#0e1014";tg.setHeaderColor(c);tg.setBackgroundColor(c)}}catch(e){}}
var P={g:'<rect x="3" y="7" width="18" height="11" rx="4"/><path d="M8 10v5M5.5 12.5h5"/><circle cx="16" cy="11" r=".7"/><circle cx="18" cy="14" r=".7"/>',t:'<path d="M8 21h8M12 17v4M7 4h10v5a5 5 0 0 1-10 0zM17 5h3v2a3 3 0 0 1-3 3M7 5H4v2a3 3 0 0 0 3 3"/>',s:'<path d="M4 8h10M18 8h2M4 16h2M10 16h10"/><circle cx="16" cy="8" r="2"/><circle cx="8" cy="16" r="2"/>',c:'<circle cx="12" cy="12" r="9"/><path d="M12 7v5l3 2"/>',b:'<path d="M15 6l-6 6 6 6"/>',u:'<circle cx="9" cy="8" r="3"/><path d="M3 20c0-3 3-5 6-5s6 2 6 5M17 8v6M14 11h6"/>',r:'<rect x="5" y="8" width="14" height="11" rx="3"/><path d="M12 8V4M9 13h.01M15 13h.01M9 16h6"/>'};
document.querySelectorAll("[data-i]").forEach(function(e){e.insertAdjacentHTML("afterbegin",'<svg class="ic" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">'+P[e.dataset.i]+"</svg>")});
var SX='<svg viewBox="0 0 40 40" class="mark" style="color:var(--x)"><path pathLength="1" d="M9 9L31 31" stroke="currentColor" stroke-width="5" stroke-linecap="round" fill="none"/><path pathLength="1" d="M31 9L9 31" stroke="currentColor" stroke-width="5" stroke-linecap="round" fill="none" style="animation-delay:.1s"/></svg>';
var SO='<svg viewBox="0 0 40 40" class="mark" style="color:var(--o)"><circle pathLength="1" cx="20" cy="20" r="11.5" stroke="currentColor" stroke-width="5" fill="none"/></svg>';
var PAL=[["#B5D4F4","#0C447C"],["#F5C4B3","#712B13"],["#C0DD97","#27500A"],["#FAC775","#633806"],["#CECBF6","#3C3489"]];
function ini(n){var r=String(n).split(/\s+/).map(function(w){var m=w.match(/[A-Za-z0-9\u00C0-\uFFFF]/);return m?m[0]:""}).join("").slice(0,2);return(r||"?").toUpperCase()}
function av(n,url,z,bot){var p=PAL[String(n).length%5];return'<div class="av" style="background:'+p[0]+";color:"+p[1]+";width:"+z+"px;height:"+z+"px;font-size:"+Math.round(z*.38)+'px">'+(bot?"AI":esc(ini(n)))+(url?'<img src="'+url+'" alt="" onerror="this.remove()">':"")+"</div>"}
var AC;function beep(f,d,dl){if(!set.snd)return;try{AC=AC||new(window.AudioContext||window.webkitAudioContext)();var o=AC.createOscillator(),g=AC.createGain();o.frequency.value=f;g.gain.value=.05;o.connect(g);g.connect(AC.destination);var z=AC.currentTime+(dl||0);o.start(z);o.stop(z+d)}catch(e){}}
function buzz(kind){if(!set.vib)return;try{if(tg&&tg.HapticFeedback){if(kind)tg.HapticFeedback.notificationOccurred(kind);else tg.HapticFeedback.impactOccurred("light")}else if(navigator.vibrate)navigator.vibrate(12)}catch(e){}}
function toast(m){var e=$("ts");e.textContent=m;e.classList.add("on");setTimeout(function(){e.classList.remove("on")},2200)}
function post(path,extra){var body={initData:initData,game_id:gid};for(var k in extra)body[k]=extra[k];return fetch(path,{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(body)}).then(function(r){return r.json()})}
function share(text){var u="https://t.me/share/url?url="+encodeURIComponent(APP)+"&text="+encodeURIComponent(text);if(tg&&tg.openTelegramLink)tg.openTelegramLink(u);else window.open(u)}

for(var i=0;i<12;i++){var f=document.createElement("i");f.className="fl";f.style.cssText="left:"+Math.random()*95+"%;animation-duration:"+(14+Math.random()*16)+"s;animation-delay:-"+Math.random()*20+"s;width:"+(24+Math.random()*28)+"px";f.innerHTML=(i%2?SO:SX).replace(' class="mark"',"").replace(/pathLength="1"/g,"");$("bg").appendChild(f)}
$("bg").classList.toggle("off",!set.bg);

var cells=[],shown=Array(9).fill(""),last=null,busy=false,prevWin,pkey="",timer=null;
for(i=0;i<9;i++){var c=document.createElement("button");c.className="cell";c.setAttribute("aria-label","Cell "+(i+1));(function(n){c.onclick=function(){move(n)}})(i);$("bd").appendChild(c);cells.push(c)}

function setStatus(t,m){$("st").textContent=t;$("sub").textContent=m||""}
var ERR={bad_auth:["Open this game from Telegram.",""],no_game:["Game not found.","Ask your friend to send a new one."],join_required:["Join our channels first.","@racksun19  @WEAYing  @racksungroup  @rackcraft"],busy:["Server is busy.","Try again in a moment."]};
function pcard(p,sym,you){var col=sym==="X"?"var(--x)":"var(--o)";if(!p)return'<div class="av" style="background:var(--line);color:var(--hint);width:34px;height:34px">?</div><div style="min-width:0"><div class="nm">Waiting…</div><div class="sy" style="color:'+col+'">'+sym+"</div></div>";return av(p.name,p.avatar,34,p.bot)+'<div style="min-width:0"><div class="nm">'+esc(p.name)+(you===sym?" (you)":"")+'</div><div class="sy" style="color:'+col+'">'+sym+"</div></div>"}

function render(s){
 if(!s)return;
 if(s.error){var e=ERR[s.error]||["Something went wrong.",""];setStatus(e[0],e[1]);return}
 var first=!last;last=s;var pl=s.players;
 var key=JSON.stringify([pl,s.you]);
 if(key!==pkey){pkey=key;$("pX").innerHTML=pcard(pl.X,"X",s.you);$("pO").innerHTML=pcard(pl.O,"O",s.you)}
 $("sc").textContent=s.score.X+" : "+s.score.O;
 var live=!!pl.O&&!s.winner;
 $("pX").className="card pl"+(live&&s.turn==="X"?" onx":"");
 $("pO").className="card pl"+(live&&s.turn==="O"?" ono":"");
 var can=!!s.you&&live&&s.turn===s.you;
 for(var i=0;i<9;i++){var v=s.board[i],ch=v!==shown[i];
  if(ch){cells[i].innerHTML=v==="X"?SX:v==="O"?SO:"";if(v&&!first){beep(v==="X"?520:380,.08)}shown[i]=v}
  var cl="cell";if(ch&&v)cl+=" pop";
  if(s.line&&s.line.indexOf(i)>-1)cl+=" win"+s.winner;else if(s.winner&&s.winner!=="draw")cl+=" dim";
  cells[i].className=cl;cells[i].disabled=!(can&&!v)}
 var t,m="";
 if(!pl.O){t=s.you?"Waiting for an opponent":"Waiting for players";m=s.you?"Tap Invite or play against the bot":""}
 else if(s.winner==="draw"){t="It’s a draw";m="Nobody scores this round"}
 else if(s.winner){t=s.you?(s.winner===s.you?"You win this round":"You lose this round"):pl[s.winner].name+" wins";m=s.mode==="bot"?"Practice round":"Score updated"}
 else if(s.you){t=s.turn===s.you?"Your turn":(pl[s.turn].bot?"Bot is thinking…":pl[s.turn].name+" is thinking…");m=s.mode==="bot"?"Practice match vs bot":""}
 else{t="Watching the game"}
 setStatus(t,m);
 $("rm").hidden=!(s.you&&s.winner);
 if(prevWin===null&&s.winner&&s.you){setTimeout(function(){showRes(s)},s.winner==="draw"?500:900)}
 prevWin=s.winner;
 sched(s)
}
function sched(s){clearTimeout(timer);var wait=document.hidden?2500:(s.mode==="bot"&&s.turn==="O"&&!s.winner?800:1500);timer=setTimeout(poll,wait)}
function poll(){if(!gid){return}post("/api/state").then(render).catch(function(){sched(last||{})})}
function move(n){if(busy||!last)return;busy=true;buzz();post("/api/move",{cell:n}).then(render).catch(function(){toast("Connection problem")}).then(function(){busy=false})}
function newGame(url,extra){return post(url,extra).then(function(r){if(r.error){render(r);return null}gid=r.game_id;last=null;shown=Array(9).fill("");prevWin=undefined;pkey="";$("ov").classList.remove("on");show("g");return r})}
function startBot(){newGame("/api/bot/new").then(function(r){if(r)poll()})}
$("vb").onclick=startBot;
$("inv").onclick=function(){newGame("/api/new").then(function(r){if(!r)return;var u="https://t.me/share/url?url="+encodeURIComponent(r.link)+"&text="+encodeURIComponent("Join my Tic-Tac-Toe game");if(tg&&tg.openTelegramLink)tg.openTelegramLink(u);else window.open(u);poll()})};
$("rm").onclick=function(){$("ov").classList.remove("on");post("/api/rematch").then(render).catch(function(){})};

var WIN='<svg viewBox="0 0 170 150" width="170" style="overflow:visible"><ellipse cx="85" cy="142" rx="38" ry="5" fill="currentColor" opacity=".15"/><g style="animation:jump .9s ease-in-out infinite;transform-box:view-box"><g stroke="#2c3e5c" stroke-width="9" stroke-linecap="round"><path d="M72 112L66 136" style="animation:wave .45s ease-in-out infinite;transform-box:view-box;transform-origin:72px 112px"/><path d="M98 112L104 136" style="animation:wave2 .45s ease-in-out infinite;transform-box:view-box;transform-origin:98px 112px"/></g><rect x="62" y="80" width="46" height="40" rx="14" fill="#3b82f6"/><g stroke="#fbd9a8" stroke-width="9" stroke-linecap="round"><path d="M66 90L40 60" style="animation:wave .5s ease-in-out infinite;transform-box:view-box;transform-origin:66px 90px"/><path d="M104 90L128 62"/></g><circle cx="85" cy="54" r="23" fill="#fbd9a8"/><path d="M62 50q4-20 23-20t23 20q-10-9-23-9t-23 9z" fill="#4a3426"/><path d="M68 38l5-16 12 9 12-9 5 16z" fill="#f5b301"/><circle cx="85" cy="25" r="2.6" fill="#ef4444"/><path d="M73 52q4-6 8 0M89 52q4-6 8 0" stroke="#222" stroke-width="2.6" fill="none" stroke-linecap="round"/><path d="M73 61q12 14 24 0z" fill="#7a1f1f"/><circle cx="70" cy="60" r="4" fill="#f78fa7" opacity=".55"/><circle cx="100" cy="60" r="4" fill="#f78fa7" opacity=".55"/><g style="animation:shine 1.2s ease-in-out infinite"><path d="M118 22h22v14a11 11 0 0 1-22 0z" fill="#f5b301"/><path d="M118 26h-6a6 6 0 0 0 6 10M140 26h6a6 6 0 0 1-6 10" stroke="#e08a00" stroke-width="2.5" fill="none"/><rect x="126" y="46" width="6" height="8" fill="#e08a00"/><rect x="120" y="54" width="18" height="5" rx="2" fill="#e08a00"/></g></g><g fill="#f5b301"><path d="M20 30l2 5 5 2-5 2-2 5-2-5-5-2 5-2z" style="animation:twinkle 1.3s infinite;transform-box:fill-box;transform-origin:center"/><path d="M150 80l2 5 5 2-5 2-2 5-2-5-5-2 5-2z" style="animation:twinkle 1.3s .4s infinite;transform-box:fill-box;transform-origin:center"/><path d="M30 100l2 4 4 2-4 2-2 4-2-4-4-2 4-2z" style="animation:twinkle 1.3s .8s infinite;transform-box:fill-box;transform-origin:center"/></g></svg>';
var LOSE='<svg viewBox="0 0 180 130" width="190" style="overflow:visible"><path d="M10 112h160" stroke="currentColor" stroke-opacity=".25" stroke-width="3" stroke-linecap="round"/><g style="animation:soul 2.6s ease-in infinite"><path d="M26 66a9 9 0 0 1 18 0v14l-4.5-3.5-4.5 3.5-4.5-3.5-4.5 3.5z" fill="#fff" opacity=".85"/><circle cx="31" cy="64" r="1.6" fill="#555"/><circle cx="39" cy="64" r="1.6" fill="#555"/></g><g stroke="#2c3e5c" stroke-width="9" stroke-linecap="round" fill="none"><path d="M118 100l30-12M118 106l34 6"/></g><rect x="64" y="86" width="60" height="26" rx="12" fill="#3b82f6"/><g stroke="#fbd9a8" stroke-width="8" stroke-linecap="round" fill="none"><path d="M76 92L90 70"/><path d="M96 108L108 124"/></g><circle cx="46" cy="96" r="22" fill="#fbd9a8"/><path d="M26 90q4-18 24-18 12 0 18 10-12-4-24 0z" fill="#4a3426"/><path d="M36 90l7 7M43 90l-7 7M50 90l7 7M57 90l-7 7" stroke="#222" stroke-width="2.6" stroke-linecap="round"/><path d="M37 107q9-6 18 0" stroke="#222" stroke-width="2.6" fill="none" stroke-linecap="round"/><path d="M46 106v7" stroke="#e24b4a" stroke-width="4" stroke-linecap="round"/><ellipse cx="46" cy="66" rx="14" ry="4" fill="none" stroke="#f5b301" stroke-width="3.5" style="animation:bob 1.5s ease-in-out infinite"/><g style="transform-origin:46px 80px;animation:orbit 2s linear infinite;transform-box:view-box"><path d="M46 52l1.6 3.4 3.6.5-2.6 2.6.6 3.6-3.2-1.7-3.2 1.7.6-3.6-2.6-2.6 3.6-.5z" fill="#f5b301"/><path d="M80 80l1.2 2.6 2.8.4-2 2 .5 2.8-2.5-1.3-2.5 1.3.5-2.8-2-2 2.8-.4z" fill="#f5b301"/></g></svg>';
var DRW='<svg viewBox="0 0 150 100" width="150" style="overflow:visible"><g style="animation:bob 1.2s ease-in-out infinite"><circle cx="38" cy="46" r="22" fill="none" stroke="#f0643c" stroke-width="9"/><path d="M92 24l34 44M126 24L92 68" stroke="#3b82f6" stroke-width="9" stroke-linecap="round"/></g><path d="M62 88h26" stroke="currentColor" stroke-width="5" stroke-linecap="round" opacity=".5"/></svg>';
var LINES={W:["Smooth moves. That’s how it’s done.","Top of the board is calling."],L:["That one got away. Go again?","Even champions take an L. Rematch?"],D:["Evenly matched. Go again?"]};
function chip(t,c,d){return'<span class="chip '+c+'" style="animation-delay:'+(d||0)+'s">'+t+"</span>"}
function showRes(s){
 var me=s.you,res=s.winner==="draw"?"D":(s.winner===me?"W":"L"),st=s.stats||{},ch="",d=.35;
 var opp=s.players[me==="X"?"O":"X"],oppName=opp?opp.name:"opponent";
 if(res==="W"){
  if(s.mode==="bot")ch+=chip("Practice win","dr",d);
  else if(st.counted)ch+=chip("+1 win","won",d);
  else if(st.hasOwnProperty("counted"))ch+=chip("Daily limit with this player","dr",d);
  if(st.streak>1)ch+=chip(st.streak+" win streak","warn",d+.12);
  if(st.rank&&s.mode!=="bot")ch+=chip("Rank #"+st.rank,"acc",d+.24)}
 var T={W:["You win!","#f5b301"],L:["You lose","var(--o)"],D:["It’s a draw","var(--hint)"]}[res],L=LINES[res];
 $("res").innerHTML=(res==="W"?WIN:res==="L"?LOSE:DRW)+'<div class="rt" style="color:'+T[1]+'">'+T[0]+'</div><div style="color:var(--hint);font-size:13px">'+L[Math.floor(Math.random()*L.length)]+'</div><div class="chips">'+ch+'</div><div style="font-weight:700;margin:8px 0 12px">'+esc(s.players[me].name)+" "+s.score[me]+" – "+s.score[me==="X"?"O":"X"]+" "+esc(oppName)+'</div><div class="acts"><button class="btn p" data-a="rm">Rematch</button><button class="btn" data-a="d">Leaderboard</button></div><div class="acts" style="margin-top:8px"><button class="btn s" data-a="x" style="flex:1">View board</button>'+(res==="W"?'<button class="btn s" data-a="sh" style="flex:1">Share win</button>':"")+"</div>";
 $("res").dataset.n=oppName;
 $("ov").classList.add("on");
 if(res==="W"){confetti();beep(523,.12);beep(659,.12,.12);beep(784,.3,.24);buzz("success")}else if(res==="L"){beep(300,.2);beep(220,.4,.2);buzz("error")}
}
$("ov").onclick=function(e){var a=e.target.closest("[data-a]");if(!a)return;var k=a.dataset.a;if(k==="sh"){share("I just beat "+$("res").dataset.n+" in Tic-Tac-Toe. Think you can take me?");return}$("ov").classList.remove("on");if(k==="rm")$("rm").onclick();if(k==="d")show("d")};
function confetti(){var c=$("cf"),x=c.getContext("2d");c.width=c.offsetWidth;c.height=c.offsetHeight;var C=["#3b82f6","#f0643c","#f5b301","#22c55e","#ec4899","#a855f7"],p=[],f=0,w=c.width,h=c.height;
 for(var i=0;i<130;i++){var l=i%2;p.push({x:l?w:0,y:h,vx:(l?-1:1)*(Math.random()*9+3),vy:-(Math.random()*16+8),r:Math.random()*6+3,c:C[i%6],a:Math.random()*6,s:Math.random()*.3})}
 (function d(){x.clearRect(0,0,w,h);p.forEach(function(q){q.vy+=.4;q.vx*=.99;q.x+=q.vx;q.y+=q.vy;q.a+=.2+q.s;x.fillStyle=q.c;x.save();x.translate(q.x,q.y);x.rotate(q.a);x.fillRect(-q.r/2,-q.r/2,q.r,q.r*1.6);x.restore()});if(++f<200)requestAnimationFrame(d);else x.clearRect(0,0,w,h)})()}

var dm="all";
function fmtT(ts){var d=new Date(ts*1000),n=new Date(),t=d.toLocaleTimeString([],{hour:"numeric",minute:"2-digit"}),y=new Date(n.getTime()-864e5);if(d.toDateString()===n.toDateString())return"Today, "+t;if(d.toDateString()===y.toDateString())return"Yesterday, "+t;return d.toLocaleDateString([],{month:"short",day:"numeric"})+", "+t}
function board(){$("dash").innerHTML='<div class="empty">Loading…</div>';post("/api/board",{mode:dm}).then(function(r){
 if(r.error){$("dash").innerHTML='<div class="empty">Open this from Telegram.</div>';return}
 var L=r.list,me=r.me,mx=L.length?L[0].wins:1,h='<div class="card hero"><div class="big">'+(me.rank?"#"+me.rank:"–")+'</div><div><div style="font-weight:700">Your rank</div><div style="font-size:12px;color:var(--hint)">'+me.wins+' wins</div></div><div class="stats"><div><b>'+me.played+"</b>Played</div><div><b>"+me.rate+"%</b>Win rate</div><div><b>"+me.streak+"</b>Streak</div></div></div>";
 if(!L.length){$("dash").innerHTML=h+'<div class="empty">No wins yet. Be the first on the board.</div>';return}
 var G=["linear-gradient(#f5b301,#e08a00)","linear-gradient(#b8c0cc,#8892a0)","linear-gradient(#e29a63,#b0622e)"],H=[90,64,46];
 h+='<div class="pod">';
 [1,0,2].forEach(function(k){var e=L[k];if(!e)return;h+='<div class="pc">'+(k===0?'<svg viewBox="0 0 24 16" width="24" style="margin:0 auto 2px;display:block"><path d="M2 14l1-9 5 4 4-7 4 7 5-4 1 9z" fill="#f5b301"/></svg>':"")+av(e.name,e.avatar,k?44:56)+'<div class="nm">'+esc(e.name)+(e.me?" (you)":"")+'</div><div style="font-size:11px;color:var(--hint);margin-bottom:4px">'+e.wins+' wins</div><div class="step" style="height:'+H[k]+"px;background:"+G[k]+";animation-delay:"+(.1+k*.12)+'s">'+(k+1)+"</div></div>"});
 h+="</div>";
 L.slice(3).forEach(function(e,k){h+='<div class="card row'+(e.me?" me":"")+'" style="animation-delay:'+(.4+k*.05)+'s"><b>'+(k+4)+"</b>"+av(e.name,e.avatar,36)+'<div class="g"><div class="nm">'+esc(e.name)+(e.me?" (you)":"")+'</div><i class="bar"><b style="width:'+Math.round(e.wins/mx*100)+'%"></b></i></div><span style="font-size:13px;color:var(--hint)">'+e.wins+"</span></div>"});
 $("dash").innerHTML=h}).catch(function(){$("dash").innerHTML='<div class="empty">Couldn’t load the leaderboard.</div>'})}
function hist(){$("hl").innerHTML='<div class="empty">Loading…</div>';post("/api/history").then(function(r){
 var it=r.items||[];if(!it.length){$("hl").innerHTML='<div class="empty">No matches yet. Play a round and it shows up here.</div>';return}
 $("hl").innerHTML=it.map(function(e,k){var c=e.res==="W"?'won">Won':e.res==="L"?'lost">Lost':'dr">Draw';return'<div class="card row" style="animation-delay:'+Math.min(k,10)*.04+'s"><span class="chip '+c+'</span><div class="g"><div class="nm">vs '+esc(e.opp)+'</div><div style="font-size:12px;color:var(--hint)">'+fmtT(e.ts)+(e.mode==="bot"?" · practice":"")+"</div></div></div>"}).join("")}).catch(function(){$("hl").innerHTML='<div class="empty">Couldn’t load history.</div>'})}
$("seg").onclick=function(e){var m=e.target.dataset.m;if(!m)return;dm=m;[].forEach.call($("seg").children,function(x){x.className=x.dataset.m===m?"on":""});board()};
function show(v){if(v==="g"&&!gid&&!last)startBot();["g","d","s","h"].forEach(function(k){$("v"+k).classList.toggle("on",k===v)});document.querySelectorAll(".tab").forEach(function(x){x.classList.toggle("on",x.dataset.go===(v==="h"?"s":v))});if(v==="d")board();if(v==="h")hist()}
document.querySelectorAll("[data-go]").forEach(function(e){e.onclick=function(){show(e.dataset.go)}});
$("hb").onclick=function(){show("h")};$("bk").onclick=function(){show("s")};
document.querySelectorAll("[data-k]").forEach(function(e){var k=e.dataset.k;e.querySelector(".tg").classList.toggle("on",!!set[k]);e.onclick=function(){set[k]=set[k]?0:1;e.querySelector(".tg").classList.toggle("on",!!set[k]);if(k==="bg")$("bg").classList.toggle("off",!set.bg);save()}});
function thSeg(){[].forEach.call($("th").children,function(x){x.className=x.dataset.th===set.th?"on":""})}
$("th").onclick=function(e){var m=e.target.dataset.th;if(!m)return;set.th=m;thSeg();theme();save()};
document.addEventListener("visibilitychange",function(){if(!document.hidden&&gid)poll()});
theme();thSeg();
if(gid==="dash"){gid="";show("d")}
else if(gid==="bot"||!gid){startBot()}
else poll();
})();
</script></body></html>
"""
