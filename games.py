import os
import re
import json
import time
import uuid
import hmac
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

_games = {}
_lock = threading.Lock()
_cfg = {"token": None, "member_check": None}
_member_cache = {}


def new_game_id():
    return uuid.uuid4().hex[:12]


def game_link(gid):
    return "https://t.me/" + BOT_USERNAME + "/" + APP_SHORT_NAME + "?startapp=" + gid


def _new_game(gid):
    return {
        "id": gid,
        "board": [""] * 9,
        "players": {"X": None, "O": None},
        "turn": "X",
        "starter": "X",
        "winner": None,
        "line": None,
        "score": {"X": 0, "O": 0},
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
    return {
        "board": g["board"],
        "turn": g["turn"],
        "winner": g["winner"],
        "line": g["line"],
        "score": g["score"],
        "you": _sym_of(g, uid),
        "players": {k: ({"name": v["name"]} if v else None) for k, v in g["players"].items()},
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
        if g["players"]["X"] and g["players"]["O"]:
            return False
    return True


def _edit_payload(g):
    inline_id = g.get("inline")
    if not inline_id:
        return None
    px, po = g["players"]["X"], g["players"]["O"]
    xn = px["name"] if px else "Player 1"
    if not po:
        text = "Tic-Tac-Toe\n" + xn + " is waiting for a player"
        label = "Play"
    else:
        on = po["name"]
        sc = xn + " " + str(g["score"]["X"]) + " - " + str(g["score"]["O"]) + " " + on
        if g["winner"] is None:
            text = "Tic-Tac-Toe\n" + xn + " vs " + on + "\nGame in progress"
        elif g["winner"] == "draw":
            text = "Tic-Tac-Toe\nThat round was a draw\n" + sc
        else:
            w = px if g["winner"] == "X" else po
            text = "Tic-Tac-Toe\n" + w["name"] + " won this round\n" + sc
        label = "Open game"
    return {
        "inline_message_id": inline_id,
        "text": text,
        "reply_markup": {"inline_keyboard": [[{"text": label, "url": game_link(g["id"])}]]},
    }


def _send_edit(payload):
    if not payload or not _cfg["token"]:
        return

    def work():
        try:
            requests.post(
                "https://api.telegram.org/bot" + _cfg["token"] + "/editMessageText",
                json=payload,
                timeout=10,
            )
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


def _read_request():
    data = request.get_json(silent=True) or {}
    user = _verify(str(data.get("initData", "")))
    gid = str(data.get("game_id", ""))
    return data, user, gid


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
        if _sym_of(g, uid) is None:
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
                edit = _edit_payload(g)
            elif all(g["board"]):
                g["winner"] = "draw"
                edit = _edit_payload(g)
            else:
                g["turn"] = "O" if sym == "X" else "X"
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
            g["starter"] = "O" if g["starter"] == "X" else "X"
            g["turn"] = g["starter"]
            g["updated"] = time.time()
            edit = _edit_payload(g)
        out = _public(g, user["id"])
    _send_edit(edit)
    return jsonify(out)


def page_game():
    resp = Response(GAME_HTML, mimetype="text/html")
    resp.headers["Cache-Control"] = "no-store"
    return resp


def page_logo():
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logo.png")
    if not os.path.exists(path):
        return Response("Not found", status=404)
    return send_file(path, mimetype="image/png")


def setup(flask_app, bot_token, member_check=None):
    _cfg["token"] = bot_token
    _cfg["member_check"] = member_check
    flask_app.add_url_rule("/game", "game_page", page_game, methods=["GET"])
    flask_app.add_url_rule("/logo.png", "game_logo", page_logo, methods=["GET"])
    flask_app.add_url_rule("/api/state", "game_state", api_state, methods=["POST"])
    flask_app.add_url_rule("/api/move", "game_move", api_move, methods=["POST"])
    flask_app.add_url_rule("/api/rematch", "game_rematch", api_rematch, methods=["POST"])


def register_handlers(app, is_member, guard=None):
    from telegram import (
        InlineQueryResultArticle,
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
        res = InlineQueryResultArticle(
            id=gid,
            title="Tic-Tac-Toe",
            description="Play with a friend",
            input_message_content=InputTextMessageContent(
                "Tic-Tac-Toe\n" + name + " is waiting for a player"
            ),
            reply_markup=markup,
            thumbnail_url=BASE_URL + "/logo.png",
            thumbnail_width=640,
            thumbnail_height=360,
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
        markup = InlineKeyboardMarkup([[
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
        ]])
        await update.message.reply_text(
            "*Games*\n\nPick a game, then choose a friend or a group to play with.",
            reply_markup=markup,
            parse_mode="Markdown",
        )

    app.add_handler(CommandHandler("games", games_command))
    app.add_handler(InlineQueryHandler(inline_query))
    app.add_handler(ChosenInlineResultHandler(chosen_inline))


GAME_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no">
<title>Tic-Tac-Toe</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
:root{
  --bg:var(--tg-theme-bg-color,#ffffff);
  --fg:var(--tg-theme-text-color,#111111);
  --hint:var(--tg-theme-hint-color,#7d8492);
  --card:var(--tg-theme-secondary-bg-color,#f1f2f4);
  --btn:var(--tg-theme-button-color,#3390ec);
  --btnfg:var(--tg-theme-button-text-color,#ffffff);
  --x:#3b82f6;
  --o:#f0643c;
}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html,body{margin:0;min-height:100%;background:var(--bg);color:var(--fg);font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif}
.wrap{max-width:420px;margin:0 auto;padding:18px 16px 24px;display:flex;flex-direction:column;gap:16px;min-height:100vh}
.players{display:flex;align-items:center;gap:10px}
.pl{flex:1;min-width:0;background:var(--card);border:1.5px solid transparent;border-radius:14px;padding:10px 12px;text-align:center}
.pl.on{border-color:var(--btn)}
.nm{font-size:15px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.sy{font-size:13px;margin-top:2px;font-weight:600}
.sy.x{color:var(--x)}
.sy.o{color:var(--o)}
.score{font-size:18px;font-weight:700;min-width:54px;text-align:center}
.board{display:grid;grid-template-columns:repeat(3,1fr);gap:10px;width:100%}
.cell{aspect-ratio:1;background:var(--card);border:2px solid transparent;border-radius:16px;padding:18%;display:flex;align-items:center;justify-content:center;cursor:pointer;color:var(--fg)}
.cell:disabled{cursor:default}
.cell.x{color:var(--x)}
.cell.o{color:var(--o)}
.cell.win{border-color:var(--btn)}
.board.over .cell:not(.win){opacity:.55}
.cell svg{width:100%;height:100%}
.status{text-align:center;font-size:16px;font-weight:600}
.msg{text-align:center;font-size:13px;color:var(--hint);min-height:16px}
.actions{display:flex;gap:10px;margin-top:auto}
.btn{flex:1;padding:13px 0;border:0;border-radius:12px;background:var(--btn);color:var(--btnfg);font-size:15px;font-weight:600;cursor:pointer}
.btn.sec{background:var(--card);color:var(--fg)}
.btn[hidden]{display:none}
</style>
</head>
<body>
<div class="wrap">
  <div class="players">
    <div class="pl" id="pX"><div class="nm" id="nX">-</div><div class="sy x">X</div></div>
    <div class="score" id="score">0 : 0</div>
    <div class="pl" id="pO"><div class="nm" id="nO">Waiting</div><div class="sy o">O</div></div>
  </div>
  <div class="board" id="board"></div>
  <div class="status" id="status">Loading</div>
  <div class="msg" id="msg"></div>
  <div class="actions">
    <button class="btn" id="rematch" hidden>Rematch</button>
    <button class="btn sec" id="close">Close</button>
  </div>
</div>
<script>
(function(){
  var tg = window.Telegram && window.Telegram.WebApp;
  if (tg) {
    try { tg.ready(); tg.expand(); tg.setHeaderColor('bg_color'); tg.setBackgroundColor('bg_color'); } catch (e) {}
  }
  var initData = tg ? tg.initData : "";
  var gid = "";
  try { gid = (tg.initDataUnsafe && tg.initDataUnsafe.start_param) || ""; } catch (e) {}
  if (!gid) gid = new URLSearchParams(location.search).get("g") || "";

  var SX = '<svg viewBox="0 0 40 40"><path d="M9 9L31 31M31 9L9 31" stroke="currentColor" stroke-width="5" stroke-linecap="round" fill="none"/></svg>';
  var SO = '<svg viewBox="0 0 40 40"><circle cx="20" cy="20" r="11.5" stroke="currentColor" stroke-width="5" fill="none"/></svg>';

  var boardEl = document.getElementById('board');
  var cells = [];
  for (var i = 0; i < 9; i++) {
    var c = document.createElement('button');
    c.className = 'cell';
    c.setAttribute('aria-label', 'Cell ' + (i + 1));
    (function (n) { c.onclick = function () { move(n); }; })(i);
    boardEl.appendChild(c);
    cells.push(c);
  }

  var last = null, busy = false;
  var $ = function (id) { return document.getElementById(id); };

  function post(path, extra) {
    var body = { initData: initData, game_id: gid };
    for (var k in extra) body[k] = extra[k];
    return fetch(path, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(body)
    }).then(function (r) { return r.json(); });
  }

  function setStatus(t, m) {
    $('status').textContent = t;
    $('msg').textContent = m || '';
  }

  function render(s) {
    if (!s) return;
    if (s.error) {
      var map = {
        bad_auth: 'Open this game from Telegram.',
        no_game: 'Game not found. Ask your friend to send a new one.',
        join_required: 'Join our channels and groups first, then reopen this game.',
        busy: 'Server is busy. Try again in a moment.'
      };
      setStatus(map[s.error] || 'Something went wrong.', s.error === 'join_required' ? '@racksun19  @WEAYing  @racksungroup  @rackcraft' : '');
      return;
    }
    last = s;
    var pl = s.players;
    $('nX').textContent = pl.X ? pl.X.name : '-';
    $('nO').textContent = pl.O ? pl.O.name : 'Waiting';
    $('score').textContent = s.score.X + ' : ' + s.score.O;
    var live = !!pl.O && !s.winner;
    $('pX').className = 'pl' + (live && s.turn === 'X' ? ' on' : '');
    $('pO').className = 'pl' + (live && s.turn === 'O' ? ' on' : '');
    var canPlay = !!s.you && live && s.turn === s.you;
    for (var i = 0; i < 9; i++) {
      var v = s.board[i];
      cells[i].innerHTML = v === 'X' ? SX : (v === 'O' ? SO : '');
      cells[i].className = 'cell' + (v ? ' ' + v.toLowerCase() : '') + (s.line && s.line.indexOf(i) > -1 ? ' win' : '');
      cells[i].disabled = !(canPlay && !v);
    }
    boardEl.className = 'board' + (s.winner && s.winner !== 'draw' ? ' over' : '');
    var t;
    if (!pl.O) t = s.you ? 'Waiting for a friend to join' : 'Waiting for players';
    else if (s.winner === 'draw') t = 'It\\u2019s a draw';
    else if (s.winner) t = s.you ? (s.winner === s.you ? 'You win' : 'You lose') : (pl[s.winner].name + ' wins');
    else if (s.you) t = s.turn === s.you ? 'Your turn' : ('Waiting for ' + pl[s.turn].name);
    else t = 'Watching the game';
    setStatus(t, '');
    $('rematch').hidden = !(s.you && s.winner);
  }

  function move(n) {
    if (busy || !last) return;
    busy = true;
    try { if (tg && tg.HapticFeedback) tg.HapticFeedback.impactOccurred('light'); } catch (e) {}
    post('/api/move', { cell: n }).then(render).catch(function () {
      $('msg').textContent = 'Connection problem';
    }).then(function () { busy = false; });
  }

  $('rematch').onclick = function () {
    post('/api/rematch').then(render).catch(function () {});
  };
  $('close').onclick = function () {
    if (tg) tg.close(); else window.close();
  };

  function tick() {
    if (document.hidden) { setTimeout(tick, 2000); return; }
    post('/api/state').then(render).catch(function () {}).then(function () {
      setTimeout(tick, 1500);
    });
  }
  tick();
})();
</script>
</body>
</html>
"""
