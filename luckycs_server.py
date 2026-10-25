#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Roniks Gift — local game server.

A small, dependency-free Python server for the Roniks Gift prototype.
It keeps the live Ice Arena and Crash rounds running independently of
connected browsers and stores rounds, bets, players and mines sessions
in SQLite.

Run:
    py luckycs_server.py

Open:
    http://127.0.0.1:8123/
"""

from __future__ import annotations

import hashlib
import hmac
import html
import json
import math
import os
import random
import re
import secrets
import sqlite3
import threading
import time
import urllib.request
import uuid
from http import HTTPStatus
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, parse_qsl, urlparse

BASE_DIR = Path(__file__).resolve().parent
DB_PATH = BASE_DIR / "luckycs.db"
APP_FILE = "ice-arena-profile.html"
HOST = "127.0.0.1"
PORT = 8123
TELEGRAM_CONFIG_PATH = BASE_DIR / "telegram_config.json"
WITHDRAW_LOG_PATH = BASE_DIR / "withdraw_notifications.log"
DEPOSIT_LOG_PATH = BASE_DIR / "deposit_notifications.log"
WITHDRAW_NOTIFY_LOCK = threading.Lock()
DEPOSIT_NOTIFY_LOCK = threading.Lock()

TON_ADDRESS_RE = re.compile(r"^(?:UQ|EQ|0Q|kQ)[A-Za-z0-9_-]{46}$")
TON_RAW_RE = re.compile(r"^-?\d+:[0-9a-fA-F]{64}$")
PLAYER_ID_RE = re.compile(r"^[A-Za-z0-9_-]{8,64}$")

LOCK = threading.RLock()
DB: sqlite3.Connection | None = None
STOP = threading.Event()

ARENA_BET_SECONDS = 5.0
ARENA_SPIN_SECONDS = 10.0
ARENA_RESULT_SECONDS = 2.8
CRASH_BET_SECONDS = 7.0
CRASH_CRASHED_SECONDS = 3.5
CRASH_GROWTH = 0.30
MIN_BET = 0.1
MIN_DEPOSIT = 0.1

# Апгрейд: игрок выбирает цель, шанс = min(95%, 92.5% / цель).
# Матожидание 92.5% (7.5% edge), выплата при победе = ставка * цель.
UPGRADE_TARGETS = (1.2, 1.5, 2.0, 3.0, 5.0, 10.0)
UPGRADE_EDGE = 0.925


def upgrade_chance(target: float) -> float:
    return min(0.95, UPGRADE_EDGE / max(1.0, float(target)))

BOT_NAMES = [
    ("Пингвин", "🐧"), ("Морозко", "❄️"), ("Ледяной", "🧊"),
    ("Полярник", "🐻‍❄️"), ("Вьюга", "🌬️"), ("Конёк", "⛸️"),
    ("Шайба", "🏒"), ("Тюлень", "🦭"), ("Снежок", "☃️"),
    ("Кристалл", "💎"), ("Север", "🌌"), ("Иней", "🧊"),
]
BOT_BETS = [1, 1, 2, 5, 5, 10, 20, 50]


class ApiError(Exception):
    def __init__(self, message: str, status: int = 400):
        super().__init__(message)
        self.message = message
        self.status = status


def r2(value: float) -> float:
    return round(float(value) + 1e-9, 2)


def now_ts() -> float:
    return time.time()


def json_text(value) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


# ---------------------------------------------------------------------------
# Database
# ---------------------------------------------------------------------------

def db_connect() -> sqlite3.Connection:
    conn = sqlite3.connect(str(DB_PATH), check_same_thread=False, timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA busy_timeout=8000")
    return conn


def init_db() -> None:
    global DB
    DB = db_connect()
    with DB:
        DB.executescript(
            """
            CREATE TABLE IF NOT EXISTS players (
                id TEXT PRIMARY KEY,
                name TEXT NOT NULL,
                avatar TEXT NOT NULL DEFAULT '😎',
                balance REAL NOT NULL DEFAULT 0,
                earned REAL NOT NULL DEFAULT 0,
                address TEXT NOT NULL DEFAULT '',
                username TEXT NOT NULL DEFAULT '',
                tg_id INTEGER NOT NULL DEFAULT 0,
                created_at REAL NOT NULL
            );

            CREATE TABLE IF NOT EXISTS transactions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                player_id TEXT NOT NULL,
                type TEXT NOT NULL,
                amount REAL NOT NULL,
                created_at REAL NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_tx_player ON transactions(player_id, id DESC);

            CREATE TABLE IF NOT EXISTS deposit_requests (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                player_id TEXT NOT NULL,
                amount REAL NOT NULL,
                status TEXT NOT NULL DEFAULT 'pending',
                created_at REAL NOT NULL,
                decided_at REAL,
                decided_by TEXT
            );
            CREATE INDEX IF NOT EXISTS idx_deposit_requests_status
                ON deposit_requests(status, id DESC);

            CREATE TABLE IF NOT EXISTS arena_rounds (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                round_no INTEGER NOT NULL,
                seed TEXT NOT NULL,
                hash TEXT NOT NULL,
                phase TEXT NOT NULL,
                started_at REAL NOT NULL,
                bet_until REAL NOT NULL,
                phase_until REAL NOT NULL,
                winner_id TEXT,
                winner_name TEXT,
                winner_avatar TEXT,
                winner_bet REAL NOT NULL DEFAULT 0,
                pot REAL NOT NULL DEFAULT 0,
                prize REAL NOT NULL DEFAULT 0,
                created_at REAL NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_arena_rounds_no ON arena_rounds(round_no DESC);

            CREATE TABLE IF NOT EXISTS arena_bets (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                round_id INTEGER NOT NULL,
                player_id TEXT,
                name TEXT NOT NULL,
                avatar TEXT NOT NULL,
                amount REAL NOT NULL,
                is_bot INTEGER NOT NULL DEFAULT 0,
                created_at REAL NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_arena_bets_round ON arena_bets(round_id);

            CREATE TABLE IF NOT EXISTS crash_rounds (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                round_no INTEGER NOT NULL,
                seed TEXT NOT NULL,
                hash TEXT NOT NULL,
                phase TEXT NOT NULL,
                started_at REAL NOT NULL,
                bet_until REAL NOT NULL,
                phase_until REAL,
                crash_at REAL,
                crashed_at REAL,
                created_at REAL NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_crash_rounds_no ON crash_rounds(round_no DESC);

            CREATE TABLE IF NOT EXISTS crash_bets (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                round_id INTEGER NOT NULL,
                player_id TEXT,
                name TEXT NOT NULL,
                avatar TEXT NOT NULL,
                amount REAL NOT NULL,
                auto_at REAL,
                cashed_at REAL,
                cashout_mult REAL,
                payout REAL NOT NULL DEFAULT 0,
                is_bot INTEGER NOT NULL DEFAULT 0,
                created_at REAL NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_crash_bets_round ON crash_bets(round_id);

            CREATE TABLE IF NOT EXISTS mines_sessions (
                id TEXT PRIMARY KEY,
                player_id TEXT NOT NULL,
                bet REAL NOT NULL,
                mines INTEGER NOT NULL,
                mine_cells TEXT NOT NULL,
                revealed_cells TEXT NOT NULL,
                phase TEXT NOT NULL,
                multiplier REAL NOT NULL DEFAULT 1,
                payout REAL NOT NULL DEFAULT 0,
                created_at REAL NOT NULL,
                updated_at REAL NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_mines_player ON mines_sessions(player_id, updated_at DESC);

            CREATE TABLE IF NOT EXISTS mines_history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                player_id TEXT NOT NULL,
                win INTEGER NOT NULL,
                mult REAL NOT NULL,
                created_at REAL NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_mines_hist_player ON mines_history(player_id, id DESC);

            CREATE TABLE IF NOT EXISTS wheel_spins (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                player_id TEXT NOT NULL,
                bet REAL NOT NULL,
                sector INTEGER NOT NULL,
                target REAL NOT NULL DEFAULT 0,
                chance REAL NOT NULL DEFAULT 0,
                mult REAL NOT NULL,
                payout REAL NOT NULL DEFAULT 0,
                created_at REAL NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_wheel_player ON wheel_spins(player_id, id DESC);
            """
        )
        # Миграция живой БД: старые спины колеса остаются с target=0 и не
        # попадают в историю апгрейда, новые спины используют target/chance.
        spin_cols = {row["name"] for row in DB.execute("PRAGMA table_info(wheel_spins)").fetchall()}
        if "target" not in spin_cols:
            DB.execute("ALTER TABLE wheel_spins ADD COLUMN target REAL NOT NULL DEFAULT 0")
        if "chance" not in spin_cols:
            DB.execute("ALTER TABLE wheel_spins ADD COLUMN chance REAL NOT NULL DEFAULT 0")
        player_cols = {row["name"] for row in DB.execute("PRAGMA table_info(players)").fetchall()}
        if "username" not in player_cols:
            DB.execute("ALTER TABLE players ADD COLUMN username TEXT NOT NULL DEFAULT ''")
        if "tg_id" not in player_cols:
            DB.execute("ALTER TABLE players ADD COLUMN tg_id INTEGER NOT NULL DEFAULT 0")
        DB.commit()


def db_exec(sql: str, params=()):
    assert DB is not None
    return DB.execute(sql, params)


def db_commit() -> None:
    assert DB is not None
    DB.commit()


def ensure_player(player_id: str | None) -> sqlite3.Row:
    assert DB is not None
    pid = (player_id or "").strip()
    if not PLAYER_ID_RE.match(pid):
        pid = uuid.uuid4().hex
    row = db_exec("SELECT * FROM players WHERE id=?", (pid,)).fetchone()
    if row is None:
        db_exec(
            "INSERT INTO players(id, name, avatar, balance, earned, address, created_at) "
            "VALUES(?,?,?,?,?,?,?)",
            (pid, "Игрок Roniks Gift", "😎", 0.0, 0.0, "", now_ts()),
        )
        db_commit()
        row = db_exec("SELECT * FROM players WHERE id=?", (pid,)).fetchone()
    return row


def add_transaction(player_id: str, kind: str, amount: float, ts: float) -> None:
    db_exec(
        "INSERT INTO transactions(player_id, type, amount, created_at) VALUES(?,?,?,?)",
        (player_id, kind, r2(amount), ts),
    )


def _one_line(value) -> str:
    return str(value or "").replace("\r", " ").replace("\n", " ").strip()


def _telegram_chat_ids(raw) -> list[str]:
    if isinstance(raw, (list, tuple)):
        parts = raw
    else:
        parts = str(raw or "").replace(";", ",").split(",")
    return [str(part).strip() for part in parts if str(part).strip()]


def load_telegram_config() -> dict:
    path = Path(os.environ.get("RONIKS_TELEGRAM_CONFIG") or TELEGRAM_CONFIG_PATH)
    data: dict = {}
    try:
        loaded = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(loaded, dict):
            data = loaded
    except FileNotFoundError:
        pass
    except Exception as exc:  # noqa: BLE001
        print(f"Telegram config error: {exc}")

    token = os.environ.get("TELEGRAM_BOT_TOKEN")
    if token is None:
        token = data.get("bot_token", "")
    chat_raw = os.environ.get("TELEGRAM_CHAT_ID")
    if chat_raw is None:
        chat_raw = data.get("chat_ids", data.get("chat_id", ""))
    enabled_raw = os.environ.get("TELEGRAM_ENABLED", data.get("enabled", True))
    enabled = str(enabled_raw).strip().lower() not in ("0", "false", "no", "off", "")
    return {
        "enabled": enabled,
        "bot_token": str(token or "").strip(),
        "chat_ids": _telegram_chat_ids(chat_raw),
    }


def telegram_player_id(user_id) -> str:
    raw = str(int(user_id))
    pid = "tg_" + raw
    if len(pid) < 8:
        pid = "tg_" + raw.zfill(8 - len("tg_"))
    return pid


def validate_telegram_init_data(init_data: str, bot_token: str) -> dict | None:
    """Validate Telegram WebApp initData and return the Telegram user."""
    if not init_data or not bot_token:
        return None
    try:
        pairs = parse_qsl(str(init_data), keep_blank_values=True)
        values = dict(pairs)
        received_hash = values.pop("hash", "").strip().lower()
        if not re.fullmatch(r"[0-9a-f]{64}", received_hash):
            return None
        auth_date = int(values.get("auth_date") or 0)
        if auth_date <= 0 or now_ts() - auth_date > 86_400:
            return None
        check_string = "\n".join(f"{key}={values[key]}" for key in sorted(values))
        secret = hmac.new(b"WebAppData", bot_token.encode("utf-8"), hashlib.sha256).digest()
        expected = hmac.new(secret, check_string.encode("utf-8"), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(expected, received_hash):
            return None
        user = json.loads(values.get("user") or "{}")
        if not isinstance(user, dict) or user.get("is_bot"):
            return None
        user_id = int(user.get("id") or 0)
        if user_id <= 0:
            return None
        username = str(user.get("username") or "").strip().lstrip("@")[:32]
        if not re.fullmatch(r"[A-Za-z0-9_]{0,32}", username):
            username = ""
        first_name = _one_line(user.get("first_name"))[:64]
        last_name = _one_line(user.get("last_name"))[:64]
        name = " ".join(part for part in (first_name, last_name) if part).strip()
        if not name:
            name = "@" + username if username else "Игрок Roniks Gift"
        photo_url = str(user.get("photo_url") or "").strip()
        if not re.fullmatch(r"https://[^\s\"'<>]{1,500}", photo_url, re.IGNORECASE):
            photo_url = ""
        return {
            "id": user_id,
            "name": name[:96],
            "username": username,
            "photo_url": photo_url,
        }
    except (TypeError, ValueError, json.JSONDecodeError):
        return None


def telegram_user_from_request(init_data) -> dict | None:
    token = load_telegram_config()["bot_token"]
    return validate_telegram_init_data(str(init_data or ""), token)


def apply_telegram_identity(tg_user: dict) -> sqlite3.Row:
    pid = telegram_player_id(tg_user["id"])
    row = ensure_player(pid)
    name = tg_user.get("name") or "Игрок Roniks Gift"
    username = tg_user.get("username") or ""
    photo_url = tg_user.get("photo_url") or ""
    avatar = photo_url or row["avatar"] or "😎"
    old_username = row["username"] if "username" in row.keys() else ""
    old_tg_id = int(row["tg_id"] or 0) if "tg_id" in row.keys() else 0
    if row["name"] != name or row["avatar"] != avatar or old_username != username or old_tg_id != int(tg_user["id"]):
        db_exec(
            "UPDATE players SET name=?, avatar=?, username=?, tg_id=? WHERE id=?",
            (name, avatar, username, int(tg_user["id"]), pid),
        )
        db_commit()
        row = db_exec("SELECT * FROM players WHERE id=?", (pid,)).fetchone()
    return row


def format_withdraw_notification(player: dict, amount: float, address: str, ts: float) -> str:
    name = html.escape(_one_line(player.get("name") or "Игрок"))
    pid = html.escape(_one_line(player.get("id") or ""))
    wallet = html.escape(_one_line(address))
    when = time.strftime("%d.%m.%Y %H:%M:%S", time.localtime(ts))
    return (
        "💸 <b>Новая заявка на вывод</b>\n\n"
        f"Игрок: <b>{name}</b>\n"
        f"ID: <code>{pid}</code>\n"
        f"Сумма: <b>{r2(amount):.2f} USDT</b>\n"
        f"Адрес: <code>{wallet}</code>\n"
        f"Время: {when}"
    )


def log_withdraw_notification(player: dict, amount: float, address: str, ts: float, status: str) -> None:
    line = (
        f"{time.strftime('%d.%m.%Y %H:%M:%S', time.localtime(ts))} | "
        f"{_one_line(player.get('id'))} | {_one_line(player.get('name'))} | "
        f"{r2(amount):.2f} USDT | {_one_line(address)} | {_one_line(status)}\n"
    )
    with WITHDRAW_NOTIFY_LOCK:
        try:
            with WITHDRAW_LOG_PATH.open("a", encoding="utf-8") as fh:
                fh.write(line)
        except OSError as exc:
            print(f"Withdraw log error: {exc}")


def telegram_api_call(method: str, token: str, payload: dict | None = None,
                      timeout: float = 12) -> dict:
    url = f"https://api.telegram.org/bot{token}/{method}"
    data = None
    headers: dict[str, str] = {}
    if payload is not None:
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        headers["Content-Type"] = "application/json; charset=utf-8"
    request = urllib.request.Request(
        url,
        data=data,
        headers=headers,
        method="POST" if data is not None else "GET",
    )
    with urllib.request.urlopen(request, timeout=timeout) as response:
        result = json.loads(response.read().decode("utf-8", "replace") or "{}")
    if not result.get("ok"):
        raise RuntimeError(result.get("description") or "Telegram API error")
    return result


def telegram_send_message(token: str, chat_id: str, text: str,
                         reply_markup: dict | None = None) -> dict:
    payload = {
        "chat_id": chat_id,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": True,
    }
    if reply_markup is not None:
        payload["reply_markup"] = reply_markup
    result = telegram_api_call("sendMessage", token, payload)
    return result.get("result") or {}


def telegram_edit_message(token: str, chat_id: str, message_id: int, text: str,
                          reply_markup: dict | None = None) -> dict:
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": True,
    }
    if reply_markup is not None:
        payload["reply_markup"] = reply_markup
    result = telegram_api_call("editMessageText", token, payload)
    return result.get("result") or {}


def telegram_answer_callback(token: str, callback_id: str, text: str) -> dict:
    result = telegram_api_call(
        "answerCallbackQuery",
        token,
        {"callback_query_id": callback_id, "text": text, "show_alert": False},
    )
    return result.get("result") or {}


def telegram_get_updates(token: str, offset: int) -> list[dict]:
    result = telegram_api_call(
        "getUpdates",
        token,
        {
            "offset": offset,
            "timeout": 25,
            "limit": 100,
            "allowed_updates": ["callback_query"],
        },
        timeout=35,
    )
    updates = result.get("result") or []
    return updates if isinstance(updates, list) else []


def notify_withdraw(player: dict, amount: float, address: str, ts: float) -> None:
    config = load_telegram_config()
    text = format_withdraw_notification(player, amount, address, ts)
    if not config["enabled"]:
        log_withdraw_notification(player, amount, address, ts, "telegram disabled")
        return
    if not config["bot_token"] or not config["chat_ids"]:
        log_withdraw_notification(player, amount, address, ts, "telegram not configured")
        return

    results: list[str] = []
    for chat_id in config["chat_ids"]:
        try:
            telegram_send_message(config["bot_token"], chat_id, text)
            results.append(f"{chat_id}:ok")
        except Exception as exc:  # noqa: BLE001
            results.append(f"{chat_id}:error")
            print(f"Telegram withdraw notify error ({chat_id}): {exc}")
    log_withdraw_notification(player, amount, address, ts, "telegram " + ", ".join(results))


def notify_withdraw_async(player: dict, amount: float, address: str, ts: float) -> None:
    threading.Thread(
        target=notify_withdraw,
        args=(dict(player), amount, address, ts),
        name="withdraw-telegram",
        daemon=True,
    ).start()


def format_deposit_notification(req_id: int, player: dict, amount: float, ts: float) -> str:
    name = html.escape(_one_line(player.get("name") or "Игрок"))
    pid = html.escape(_one_line(player.get("id") or ""))
    when = time.strftime("%d.%m.%Y %H:%M:%S", time.localtime(ts))
    return (
        "💰 <b>Заявка на пополнение</b>\n\n"
        f"Заявка: <b>#{req_id}</b>\n"
        f"Игрок: <b>{name}</b>\n"
        f"ID: <code>{pid}</code>\n"
        f"Сумма: <b>{r2(amount):.2f} USDT</b>\n"
        f"Время: {when}\n\n"
        "Подтвердите пополнение, если средства поступили."
    )


def deposit_keyboard(req_id: int) -> dict:
    return {
        "inline_keyboard": [
            [
                {"text": "✅ Подтвердить", "callback_data": f"deposit:approve:{req_id}"},
                {"text": "❌ Средства не поступили", "callback_data": f"deposit:reject:{req_id}"},
            ]
        ]
    }


def log_deposit_notification(req_id: int, player: dict, amount: float, ts: float, status: str) -> None:
    line = (
        f"{time.strftime('%d.%m.%Y %H:%M:%S', time.localtime(ts))} | #{req_id} | "
        f"{_one_line(player.get('id'))} | {_one_line(player.get('name'))} | "
        f"{r2(amount):.2f} USDT | {_one_line(status)}\n"
    )
    with DEPOSIT_NOTIFY_LOCK:
        try:
            with DEPOSIT_LOG_PATH.open("a", encoding="utf-8") as fh:
                fh.write(line)
        except OSError as exc:
            print(f"Deposit log error: {exc}")


def notify_deposit(req_id: int, player: dict, amount: float, ts: float) -> None:
    config = load_telegram_config()
    text = format_deposit_notification(req_id, player, amount, ts)
    if not config["enabled"]:
        log_deposit_notification(req_id, player, amount, ts, "telegram disabled")
        return
    if not config["bot_token"] or not config["chat_ids"]:
        log_deposit_notification(req_id, player, amount, ts, "telegram not configured")
        return

    results: list[str] = []
    for chat_id in config["chat_ids"]:
        try:
            telegram_send_message(
                config["bot_token"], chat_id, text, reply_markup=deposit_keyboard(req_id)
            )
            results.append(f"{chat_id}:ok")
        except Exception as exc:  # noqa: BLE001
            results.append(f"{chat_id}:error")
            print(f"Telegram deposit notify error ({chat_id}): {exc}")
    log_deposit_notification(req_id, player, amount, ts, "telegram " + ", ".join(results))


def notify_deposit_async(req_id: int, player: dict, amount: float, ts: float) -> None:
    threading.Thread(
        target=notify_deposit,
        args=(req_id, dict(player), amount, ts),
        name="deposit-telegram",
        daemon=True,
    ).start()


def deposit_result_text(row: sqlite3.Row, status: str) -> str:
    name = html.escape(_one_line(row["player_name"] or "Игрок"))
    pid = html.escape(_one_line(row["player_id"]))
    amount = r2(row["amount"])
    if status == "approved":
        title = "✅ <b>Пополнение подтверждено</b>"
        note = f"Баланс игрока пополнен на <b>{amount:.2f} USDT</b>."
    else:
        title = "❌ <b>Пополнение отклонено</b>"
        note = "Средства не поступили на баланс."
    return (
        f"{title}\n\n"
        f"Заявка: <b>#{row['id']}</b>\n"
        f"Игрок: <b>{name}</b>\n"
        f"ID: <code>{pid}</code>\n"
        f"Сумма: <b>{amount:.2f} USDT</b>\n\n"
        f"{note}"
    )


def handle_deposit_callback(callback: dict, config: dict) -> None:
    token = config["bot_token"]
    callback_id = str(callback.get("id") or "")
    data = str(callback.get("data") or "")
    parts = data.split(":")
    if not callback_id or len(parts) != 3 or parts[0] != "deposit":
        return
    action = parts[1]
    if action not in ("approve", "reject"):
        return
    try:
        req_id = int(parts[2])
    except (TypeError, ValueError):
        return

    message = callback.get("message") or {}
    chat = message.get("chat") or {}
    chat_id = str(chat.get("id") or "")
    message_id = message.get("message_id")
    if chat_id not in config["chat_ids"]:
        try:
            telegram_answer_callback(token, callback_id, "Нет доступа")
        except Exception:  # noqa: BLE001
            pass
        return

    final_text = ""
    answer = "Заявка не найдена"
    log_row = None
    log_status = ""
    with LOCK:
        row = db_exec(
            "SELECT r.*, p.name AS player_name FROM deposit_requests r "
            "LEFT JOIN players p ON p.id=r.player_id WHERE r.id=?",
            (req_id,),
        ).fetchone()
        if row is None:
            final_text = ""
        elif row["status"] != "pending":
            final_text = deposit_result_text(row, row["status"])
            answer = "Заявка уже обработана"
            log_row = row
            log_status = row["status"]
        elif action == "approve":
            decided_at = now_ts()
            db_exec(
                "UPDATE players SET balance=balance+? WHERE id=?",
                (r2(row["amount"]), row["player_id"]),
            )
            add_transaction(row["player_id"], "deposit", r2(row["amount"]), decided_at)
            db_exec(
                "UPDATE deposit_requests SET status='approved', decided_at=?, decided_by=? "
                "WHERE id=? AND status='pending'",
                (decided_at, chat_id, req_id),
            )
            db_commit()
            final_text = deposit_result_text(row, "approved")
            answer = "Пополнение подтверждено"
            log_row = row
            log_status = "approved"
        else:
            decided_at = now_ts()
            db_exec(
                "UPDATE deposit_requests SET status='rejected', decided_at=?, decided_by=? "
                "WHERE id=? AND status='pending'",
                (decided_at, chat_id, req_id),
            )
            db_commit()
            final_text = deposit_result_text(row, "rejected")
            answer = "Отклонено: средства не поступили"
            log_row = row
            log_status = "rejected"

    if log_row is not None:
        log_deposit_notification(
            req_id,
            {"id": log_row["player_id"], "name": log_row["player_name"]},
            log_row["amount"],
            now_ts(),
            log_status,
        )
    if final_text and message_id is not None:
        try:
            telegram_edit_message(
                token,
                chat_id,
                int(message_id),
                final_text,
                reply_markup={"inline_keyboard": []},
            )
        except Exception as exc:  # noqa: BLE001
            print(f"Telegram deposit edit error: {exc}")
    try:
        telegram_answer_callback(token, callback_id, answer)
    except Exception as exc:  # noqa: BLE001
        print(f"Telegram callback answer error: {exc}")


def telegram_poll_loop() -> None:
    offset = 0
    while not STOP.is_set():
        config = load_telegram_config()
        if not config["enabled"] or not config["bot_token"] or not config["chat_ids"]:
            STOP.wait(3)
            continue
        try:
            updates = telegram_get_updates(config["bot_token"], offset)
            for update in updates:
                try:
                    update_id = int(update.get("update_id") or 0)
                except (TypeError, ValueError):
                    update_id = 0
                if update_id:
                    offset = max(offset, update_id + 1)
                callback = update.get("callback_query")
                if callback:
                    try:
                        handle_deposit_callback(callback, config)
                    except Exception as exc:  # noqa: BLE001
                        print(f"Telegram deposit callback error: {exc}")
        except Exception as exc:  # noqa: BLE001
            print(f"Telegram polling error: {exc}")
            STOP.wait(5)


def player_public(row: sqlite3.Row) -> dict:
    total_rounds = 0
    assert DB is not None
    q = db_exec(
        "SELECT "
        " (SELECT COUNT(*) FROM arena_bets WHERE player_id=? AND is_bot=0) + "
        " (SELECT COUNT(*) FROM crash_bets WHERE player_id=? AND is_bot=0) + "
        " (SELECT COUNT(*) FROM mines_sessions WHERE player_id=?) + "
        " (SELECT COUNT(*) FROM wheel_spins WHERE player_id=?) AS n",
        (row["id"], row["id"], row["id"], row["id"]),
    ).fetchone()
    if q:
        total_rounds = int(q["n"] or 0)
    return {
        "id": row["id"],
        "name": row["name"],
        "avatar": row["avatar"],
        "username": row["username"] if "username" in row.keys() else "",
        "tg_id": int(row["tg_id"] or 0) if "tg_id" in row.keys() else 0,
        "balance": r2(row["balance"]),
        "earned": r2(row["earned"]),
        "address": row["address"] or "",
        "rounds": total_rounds,
    }


# ---------------------------------------------------------------------------
# Engine
# ---------------------------------------------------------------------------

ENGINE: dict = {
    "arena": None,
    "crash": None,
}


def gen_crash_point() -> float:
    u = random.random()
    point = 0.97 / max(0.000001, 1.0 - u)
    return round(min(25.0, max(1.01, point)), 2)


def arena_hash(seed: str, round_no: int) -> str:
    import hashlib
    return hashlib.sha256((seed + ":" + str(round_no)).encode("utf-8")).hexdigest()


def add_arena_bot(round_id: int, round_no: int, index: int, ts: float,
                  identity: tuple[str, str] | None = None) -> dict:
    name, avatar = identity or random.choice(BOT_NAMES)
    amount = float(random.choice(BOT_BETS))
    bot_id = f"bot:arena:{round_no}:{index}"
    db_exec(
        "INSERT INTO arena_bets(round_id, player_id, name, avatar, amount, is_bot, created_at) "
        "VALUES(?,?,?,?,?,1,?)",
        (round_id, bot_id, name, avatar, amount, ts),
    )
    return {
        "id": bot_id,
        "player_id": None,
        "name": name,
        "avatar": avatar,
        "bet": r2(amount),
        "is_bot": True,
    }


def new_arena_round(ts: float) -> None:
    global ENGINE
    prev = ENGINE.get("arena") or {}
    db_no = int(db_exec("SELECT COALESCE(MAX(round_no),0)+1 AS n FROM arena_rounds").fetchone()["n"])
    round_no = max(int(prev.get("round_no") or 0) + 1, db_no)
    seed = secrets.token_hex(16)
    digest = arena_hash(seed, round_no)
    bet_until = ts + ARENA_BET_SECONDS
    phase_until = bet_until
    cur = db_exec(
        "INSERT INTO arena_rounds(round_no, seed, hash, phase, started_at, bet_until, phase_until, created_at) "
        "VALUES(?,?,?,?,?,?,?,?)",
        (round_no, seed, digest, "bet", ts, bet_until, phase_until, ts),
    )
    round_id = int(cur.lastrowid)
    players = []
    bot_count = random.randint(3, 5)
    bot_pool = random.sample(BOT_NAMES, bot_count)
    for i in range(bot_count):
        players.append(add_arena_bot(round_id, round_no, i, ts, bot_pool[i]))
    db_commit()
    ENGINE["arena"] = {
        "id": round_id,
        "round_no": round_no,
        "seed": seed,
        "hash": digest,
        "phase": "bet",
        "started_at": ts,
        "bet_until": bet_until,
        "phase_until": phase_until,
        "players": players,
        "pot": 0.0,
        "prize": 0.0,
        "winner": None,
    }


def start_arena_spin(ts: float) -> None:
    a = ENGINE["arena"]
    if not a or a["phase"] != "bet":
        return
    players = a["players"]
    total = sum(float(p["bet"]) for p in players)
    if total <= 0:
        a["phase"] = "result"
        a["phase_until"] = ts + ARENA_RESULT_SECONDS
        db_exec("UPDATE arena_rounds SET phase=?, phase_until=? WHERE id=?", ("result", a["phase_until"], a["id"]))
        db_commit()
        return

    pick = random.random() * total
    winner = players[-1]
    for p in players:
        pick -= float(p["bet"])
        if pick <= 0:
            winner = p
            break

    pot = r2(total)
    prize = r2(pot * 0.93)
    a["phase"] = "spin"
    a["phase_until"] = ts + ARENA_SPIN_SECONDS
    a["pot"] = pot
    a["prize"] = prize
    a["winner"] = {
        "id": winner["id"],
        "name": winner["name"],
        "avatar": winner["avatar"],
        "bet": r2(winner["bet"]),
        "is_bot": bool(winner.get("is_bot")),
        "player_id": winner.get("player_id"),
    }

    db_exec(
        "UPDATE arena_rounds SET phase=?, phase_until=?, winner_id=?, winner_name=?, "
        "winner_avatar=?, winner_bet=?, pot=?, prize=? WHERE id=?",
        (
            "spin", a["phase_until"], winner["id"], winner["name"], winner["avatar"],
            r2(winner["bet"]), pot, prize, a["id"],
        ),
    )
    if not winner.get("is_bot") and winner.get("player_id"):
        db_exec(
            "UPDATE players SET balance=balance+?, earned=earned+? WHERE id=?",
            (prize, prize, winner["player_id"]),
        )
    db_commit()


def finish_arena_result(ts: float) -> None:
    a = ENGINE["arena"]
    if not a or a["phase"] != "spin":
        return
    a["phase"] = "result"
    a["phase_until"] = ts + ARENA_RESULT_SECONDS
    db_exec("UPDATE arena_rounds SET phase=?, phase_until=? WHERE id=?", ("result", a["phase_until"], a["id"]))
    db_commit()


def add_crash_bot(round_id: int, round_no: int, index: int, ts: float,
                  identity: tuple[str, str] | None = None) -> dict:
    name, avatar = identity or random.choice(BOT_NAMES)
    amount = float(random.choice(BOT_BETS))
    auto_at = round(random.uniform(1.18, 5.5), 2)
    bot_id = f"bot:crash:{round_no}:{index}"
    db_exec(
        "INSERT INTO crash_bets(round_id, player_id, name, avatar, amount, auto_at, is_bot, created_at) "
        "VALUES(?,?,?,?,?,?,1,?)",
        (round_id, bot_id, name, avatar, amount, auto_at, ts),
    )
    return {
        "id": bot_id,
        "player_id": None,
        "name": name,
        "avatar": avatar,
        "bet": r2(amount),
        "auto_at": auto_at,
        "cashed": False,
        "cashout_mult": None,
        "payout": 0.0,
        "is_bot": True,
    }


def new_crash_round(ts: float) -> None:
    global ENGINE
    prev = ENGINE.get("crash") or {}
    db_no = int(db_exec("SELECT COALESCE(MAX(round_no),0)+1 AS n FROM crash_rounds").fetchone()["n"])
    round_no = max(int(prev.get("round_no") or 0) + 1, db_no)
    seed = secrets.token_hex(16)
    digest = arena_hash(seed, round_no)
    crash_at = gen_crash_point()
    bet_until = ts + CRASH_BET_SECONDS
    cur = db_exec(
        "INSERT INTO crash_rounds(round_no, seed, hash, phase, started_at, bet_until, phase_until, crash_at, created_at) "
        "VALUES(?,?,?,?,?,?,?,?,?)",
        (round_no, seed, digest, "bet", ts, bet_until, bet_until, crash_at, ts),
    )
    round_id = int(cur.lastrowid)
    players = []
    bot_count = random.randint(4, 7)
    bot_pool = random.sample(BOT_NAMES, bot_count)
    for i in range(bot_count):
        players.append(add_crash_bot(round_id, round_no, i, ts, bot_pool[i]))
    db_commit()
    ENGINE["crash"] = {
        "id": round_id,
        "round_no": round_no,
        "seed": seed,
        "hash": digest,
        "phase": "bet",
        "started_at": ts,
        "bet_until": bet_until,
        "phase_until": bet_until,
        "crash_at": crash_at,
        "crashed_at": None,
        "players": players,
    }


def start_crash_running(ts: float) -> None:
    c = ENGINE["crash"]
    if not c or c["phase"] != "bet":
        return
    c["phase"] = "running"
    c["started_at"] = ts
    c["phase_until"] = None
    db_exec(
        "UPDATE crash_rounds SET phase=?, started_at=?, phase_until=NULL WHERE id=?",
        ("running", ts, c["id"]),
    )
    db_commit()


def crash_multiplier(c: dict, ts: float) -> float:
    started = float(c.get("started_at") or ts)
    return math.exp(CRASH_GROWTH * max(0.0, ts - started))


def cash_out_player(c: dict, player: dict, mult: float, ts: float) -> None:
    if player.get("cashed"):
        return
    amount = float(player["bet"])
    payout = r2(amount * mult)
    player["cashed"] = True
    player["cashout_mult"] = round(mult, 2)
    player["payout"] = payout
    db_exec(
        "UPDATE crash_bets SET cashed_at=?, cashout_mult=?, payout=? WHERE round_id=? AND player_id=?",
        (ts, round(mult, 2), payout, c["id"], player["id"]),
    )
    if not player.get("is_bot") and player.get("player_id"):
        db_exec(
            "UPDATE players SET balance=balance+?, earned=earned+? WHERE id=?",
            (payout, payout, player["player_id"]),
        )


def tick_crash(ts: float) -> None:
    c = ENGINE["crash"]
    if not c:
        return
    if c["phase"] == "bet":
        if ts >= c["bet_until"]:
            start_crash_running(ts)
        return
    if c["phase"] != "running":
        return

    mult = crash_multiplier(c, ts)
    crash_at = float(c["crash_at"])
    for p in c["players"]:
        if p.get("cashed"):
            continue
        auto_at = p.get("auto_at")
        if auto_at and mult >= auto_at and auto_at < crash_at:
            cash_out_player(c, p, float(auto_at), ts)

    if mult >= crash_at:
        c["phase"] = "crashed"
        c["crashed_at"] = ts
        c["phase_until"] = ts + CRASH_CRASHED_SECONDS
        db_exec(
            "UPDATE crash_rounds SET phase=?, crashed_at=?, phase_until=? WHERE id=?",
            ("crashed", ts, c["phase_until"], c["id"]),
        )
        db_commit()


def tick_engine() -> None:
    with LOCK:
        if ENGINE.get("arena") is None:
            new_arena_round(now_ts())
        if ENGINE.get("crash") is None:
            new_crash_round(now_ts())
        ts = now_ts()
        a = ENGINE["arena"]
        if a["phase"] == "bet" and ts >= a["bet_until"]:
            start_arena_spin(ts)
        elif a["phase"] == "spin" and ts >= a["phase_until"]:
            finish_arena_result(ts)
        elif a["phase"] == "result" and ts >= a["phase_until"]:
            new_arena_round(ts)

        c = ENGINE["crash"]
        if c["phase"] == "bet" and ts >= c["bet_until"]:
            start_crash_running(ts)
        elif c["phase"] == "running":
            tick_crash(ts)
        elif c["phase"] == "crashed" and ts >= c["phase_until"]:
            new_crash_round(ts)


def engine_loop() -> None:
    while not STOP.is_set():
        try:
            tick_engine()
        except Exception as exc:  # keep the live rounds alive
            print("[engine]", exc, flush=True)
        STOP.wait(0.08)


# ---------------------------------------------------------------------------
# State builders
# ---------------------------------------------------------------------------

def arena_history(pid: str = "", limit: int = 10) -> list[dict]:
    rows = db_exec(
        "SELECT round_no, hash, winner_id, winner_name, winner_avatar, winner_bet, pot, prize "
        "FROM arena_rounds WHERE winner_name IS NOT NULL ORDER BY round_no DESC LIMIT ?",
        (limit,),
    ).fetchall()
    return [
        {
            "round_no": r["round_no"],
            "hash": r["hash"],
            "winner": {"name": r["winner_name"], "avatar": r["winner_avatar"]},
            "winner_is_me": bool(pid and r["winner_id"] == pid),
            "bet": r2(r["winner_bet"] or 0),
            "pot": r2(r["pot"] or 0),
            "prize": r2(r["prize"] or 0),
        }
        for r in rows
    ]


def crash_history(limit: int = 12) -> list[dict]:
    rows = db_exec(
        "SELECT round_no, crash_at FROM crash_rounds WHERE crashed_at IS NOT NULL "
        "ORDER BY round_no DESC LIMIT ?",
        (limit,),
    ).fetchall()
    return [{"round_no": r["round_no"], "crash_at": round(float(r["crash_at"]), 2)} for r in rows]


def mines_history_for(player_id: str, limit: int = 8) -> list[dict]:
    rows = db_exec(
        "SELECT win, mult FROM mines_history WHERE player_id=? ORDER BY id DESC LIMIT ?",
        (player_id, limit),
    ).fetchall()
    return [{"win": bool(r["win"]), "mult": round(float(r["mult"]), 2)} for r in rows]


def arena_state(pid: str, ts: float) -> dict:
    a = ENGINE.get("arena")
    if not a:
        return {}
    players = []
    my_bet = None
    for p in a["players"]:
        is_me = bool(p.get("player_id") and p["player_id"] == pid)
        item = {
            "id": p["id"],
            "name": p["name"],
            "avatar": p["avatar"],
            "bet": r2(p["bet"]),
            "is_me": is_me,
            "is_bot": bool(p.get("is_bot")),
        }
        players.append(item)
        if is_me:
            my_bet = r2(p["bet"])
    winner = None
    if a.get("winner") and a["phase"] in ("spin", "result"):
        w = a["winner"]
        winner = {
            "id": w["id"],
            "name": w["name"],
            "avatar": w["avatar"],
            "bet": r2(w["bet"]),
            "is_me": bool(w.get("player_id") and w["player_id"] == pid),
        }
    total_pot = db_exec("SELECT COALESCE(SUM(pot),0) AS s FROM arena_rounds WHERE pot>0").fetchone()["s"] or 0
    return {
        "round_no": a["round_no"],
        "phase": a["phase"],
        "bet_until": a["bet_until"],
        "phase_until": a["phase_until"],
        "players": players,
        "pot": r2(a["pot"] or sum(p["bet"] for p in a["players"])),
        "prize": r2(a["prize"] or 0),
        "winner": winner,
        "my_bet": my_bet,
        "hash": a["hash"],
        "seed": a["seed"] if a["phase"] == "result" else "",
        "history": arena_history(pid),
        "tour_total": r2(total_pot),
        "online": 47 + len(a["players"]),
    }


def crash_state(pid: str, ts: float) -> dict:
    c = ENGINE.get("crash")
    if not c:
        return {}
    players = []
    my_bet = None
    for p in c["players"]:
        is_me = bool(p.get("player_id") and p["player_id"] == pid)
        item = {
            "id": p["id"],
            "name": p["name"],
            "avatar": p["avatar"],
            "bet": r2(p["bet"]),
            "is_me": is_me,
            "is_bot": bool(p.get("is_bot")),
            "cashed": bool(p.get("cashed")),
            "cashout_mult": p.get("cashout_mult"),
            "payout": r2(p.get("payout") or 0),
            "auto_at": p.get("auto_at") if is_me else None,
        }
        players.append(item)
        if is_me:
            my_bet = item
    if c["phase"] == "running":
        mult = crash_multiplier(c, ts)
        elapsed = max(0.0, ts - float(c["started_at"]))
    elif c["phase"] == "crashed":
        mult = float(c["crash_at"])
        elapsed = math.log(max(1.01, mult)) / CRASH_GROWTH
    else:
        mult = 1.0
        elapsed = 0.0
    return {
        "round_no": c["round_no"],
        "phase": c["phase"],
        "bet_until": c["bet_until"],
        "started_at": c["started_at"],
        "phase_until": c["phase_until"] if c["phase"] in ("bet", "crashed") else None,
        "crashed_at": c.get("crashed_at"),
        "crash_at": float(c["crash_at"]) if c["phase"] == "crashed" else None,
        "multiplier": round(mult, 2),
        "elapsed": round(elapsed, 3),
        "players": players,
        "my_bet": my_bet,
        "hash": c["hash"],
        "seed": c["seed"] if c["phase"] == "crashed" else "",
        "history": crash_history(),
    }


def mines_session_public(row: sqlite3.Row, reveal_mines: bool = False) -> dict:
    mine_cells = json.loads(row["mine_cells"] or "[]")
    revealed = json.loads(row["revealed_cells"] or "[]")
    item = {
        "id": row["id"],
        "bet": r2(row["bet"]),
        "mines": int(row["mines"]),
        "revealed": revealed,
        "phase": row["phase"],
        "multiplier": round(float(row["multiplier"] or 1), 2),
        "payout": r2(row["payout"] or 0),
    }
    if reveal_mines or row["phase"] in ("lost", "won"):
        item["mine_cells"] = mine_cells
    return item


def mines_state(pid: str) -> dict:
    active = db_exec(
        "SELECT * FROM mines_sessions WHERE player_id=? AND phase='playing' "
        "ORDER BY updated_at DESC LIMIT 1",
        (pid,),
    ).fetchone()
    last = db_exec(
        "SELECT * FROM mines_sessions WHERE player_id=? ORDER BY updated_at DESC LIMIT 1",
        (pid,),
    ).fetchone()
    history = mines_history_for(pid)
    return {
        "active": mines_session_public(active) if active else None,
        "last": mines_session_public(last) if last else None,
        "history": history,
    }


def wheel_history_for(pid: str, limit: int = 10) -> list[dict]:
    rows = db_exec(
        "SELECT bet, sector, target, chance, mult, payout FROM wheel_spins "
        "WHERE player_id=? AND target>0 ORDER BY id DESC LIMIT ?",
        (pid, limit),
    ).fetchall()
    return [
        {
            "bet": r2(r["bet"]),
            "sector": int(r["sector"]),
            "target": round(float(r["target"]), 2),
            "chance": round(float(r["chance"]), 6),
            "mult": round(float(r["mult"]), 2),
            "payout": r2(r["payout"] or 0),
            "win": float(r["mult"]) > 0,
        }
        for r in rows
    ]


def wheel_stats(pid: str) -> dict:
    row = db_exec(
        "SELECT COUNT(*) AS spins, "
        "COALESCE(SUM(CASE WHEN mult>0 THEN 1 ELSE 0 END),0) AS wins, "
        "COALESCE(SUM(payout-bet),0) AS net, "
        "COALESCE(MAX(payout),0) AS best "
        "FROM wheel_spins WHERE player_id=? AND target>0",
        (pid,),
    ).fetchone()
    spins = int(row["spins"] or 0)
    wins = int(row["wins"] or 0)
    return {
        "spins": spins,
        "wins": wins,
        "winrate": round(wins / spins, 6) if spins else 0,
        "net": r2(row["net"] or 0),
        "best": r2(row["best"] or 0),
    }


def wheel_state(pid: str) -> dict:
    last = db_exec(
        "SELECT bet, sector, target, chance, mult, payout FROM wheel_spins "
        "WHERE player_id=? AND target>0 ORDER BY id DESC LIMIT 1",
        (pid,),
    ).fetchone()
    return {
        "targets": [
            {"target": target, "chance": round(upgrade_chance(target), 6)}
            for target in UPGRADE_TARGETS
        ],
        "history": wheel_history_for(pid),
        "stats": wheel_stats(pid),
        "last": (
            {
                "bet": r2(last["bet"]),
                "sector": int(last["sector"]),
                "target": round(float(last["target"]), 2),
                "chance": round(float(last["chance"]), 6),
                "mult": round(float(last["mult"]), 2),
                "payout": r2(last["payout"] or 0),
                "win": float(last["mult"]) > 0,
            }
            if last
            else None
        ),
    }


def transactions_for(pid: str, limit: int = 6) -> list[dict]:
    rows = db_exec(
        "SELECT type, amount, created_at FROM transactions WHERE player_id=? ORDER BY id DESC LIMIT ?",
        (pid, limit),
    ).fetchall()
    return [
        {
            "type": r["type"],
            "amount": r2(r["amount"]),
            "time": time.strftime("%H:%M", time.localtime(float(r["created_at"]))),
        }
        for r in rows
    ]


def build_state(pid: str) -> dict:
    ts = now_ts()
    player = ensure_player(pid)
    return {
        "ok": True,
        "now": ts,
        "player": player_public(player),
        "arena": arena_state(player["id"], ts),
        "crash": crash_state(player["id"], ts),
        "mines": mines_state(player["id"]),
        "wheel": wheel_state(player["id"]),
        "transactions": transactions_for(player["id"]),
    }


# ---------------------------------------------------------------------------
# API operations
# ---------------------------------------------------------------------------

def op_arena_bet(pid: str, body: dict) -> dict:
    ts = now_ts()
    a = ENGINE["arena"]
    player = ensure_player(pid)
    pid = player["id"]
    if not a or a["phase"] != "bet" or ts >= a["bet_until"]:
        raise ApiError("Ставки на этот раунд закрыты")
    if any(p.get("player_id") == pid for p in a["players"]):
        raise ApiError("Вы уже в этом раунде")
    try:
        amount = r2(float(body.get("amount")))
    except (TypeError, ValueError):
        raise ApiError("Некорректная ставка")
    if amount < MIN_BET:
        raise ApiError("Минимальная ставка — 0.1 USDT")
    if amount > float(player["balance"]):
        raise ApiError("Недостаточно USDT")
    db_exec("UPDATE players SET balance=balance-? WHERE id=?", (amount, pid))
    db_exec(
        "INSERT INTO arena_bets(round_id, player_id, name, avatar, amount, is_bot, created_at) "
        "VALUES(?,?,?,?,?,0,?)",
        (a["id"], pid, player["name"], player["avatar"], amount, ts),
    )
    a["players"].append({
        "id": pid,
        "player_id": pid,
        "name": player["name"],
        "avatar": player["avatar"],
        "bet": amount,
        "is_bot": False,
    })
    db_commit()
    return build_state(pid)


def op_crash_bet(pid: str, body: dict) -> dict:
    ts = now_ts()
    c = ENGINE["crash"]
    player = ensure_player(pid)
    pid = player["id"]
    if not c or c["phase"] != "bet" or ts >= c["bet_until"]:
        raise ApiError("Ставки на этот раунд закрыты")
    if any(p.get("player_id") == pid for p in c["players"]):
        raise ApiError("Вы уже в этом раунде")
    try:
        amount = r2(float(body.get("amount")))
    except (TypeError, ValueError):
        raise ApiError("Некорректная ставка")
    if amount < MIN_BET:
        raise ApiError("Минимальная ставка — 0.1 USDT")
    if amount > float(player["balance"]):
        raise ApiError("Недостаточно USDT")
    auto_raw = body.get("auto_at")
    auto_at = None
    if auto_raw not in (None, "", False):
        try:
            auto_at = round(float(auto_raw), 2)
        except (TypeError, ValueError):
            auto_at = None
        if auto_at is not None and auto_at < 1.01:
            auto_at = None
    db_exec("UPDATE players SET balance=balance-? WHERE id=?", (amount, pid))
    db_exec(
        "INSERT INTO crash_bets(round_id, player_id, name, avatar, amount, auto_at, is_bot, created_at) "
        "VALUES(?,?,?,?,?,?,0,?)",
        (c["id"], pid, player["name"], player["avatar"], amount, auto_at, ts),
    )
    c["players"].append({
        "id": pid,
        "player_id": pid,
        "name": player["name"],
        "avatar": player["avatar"],
        "bet": amount,
        "auto_at": auto_at,
        "cashed": False,
        "cashout_mult": None,
        "payout": 0.0,
        "is_bot": False,
    })
    db_commit()
    return build_state(pid)


def op_crash_cashout(pid: str, body: dict) -> dict:
    ts = now_ts()
    c = ENGINE["crash"]
    player = ensure_player(pid)
    pid = player["id"]
    if not c or c["phase"] != "running":
        raise ApiError("Раунд сейчас не идёт")
    target = next((p for p in c["players"] if p.get("player_id") == pid), None)
    if not target:
        raise ApiError("У вас нет ставки в этом раунде")
    if target.get("cashed"):
        raise ApiError("Ставка уже выведена")
    mult = crash_multiplier(c, ts)
    if mult >= float(c["crash_at"]):
        raise ApiError("Поздно — раунд уже крашнулся")
    cash_out_player(c, target, mult, ts)
    db_commit()
    return build_state(pid)


def op_mines_start(pid: str, body: dict) -> dict:
    ts = now_ts()
    player = ensure_player(pid)
    pid = player["id"]
    active = db_exec(
        "SELECT id FROM mines_sessions WHERE player_id=? AND phase='playing' LIMIT 1",
        (pid,),
    ).fetchone()
    if active:
        raise ApiError("Сначала завершите текущую игру")
    try:
        amount = r2(float(body.get("amount")))
        mines = int(body.get("mines"))
    except (TypeError, ValueError):
        raise ApiError("Некорректные параметры игры")
    if amount < MIN_BET:
        raise ApiError("Минимальная ставка — 0.1 USDT")
    if amount > float(player["balance"]):
        raise ApiError("Недостаточно USDT")
    if mines not in (3, 5, 10):
        raise ApiError("Можно выбрать 3, 5 или 10 мин")
    session_id = uuid.uuid4().hex
    mine_cells = sorted(random.sample(range(25), mines))
    db_exec("UPDATE players SET balance=balance-? WHERE id=?", (amount, pid))
    db_exec(
        "INSERT INTO mines_sessions(id, player_id, bet, mines, mine_cells, revealed_cells, phase, multiplier, payout, created_at, updated_at) "
        "VALUES(?,?,?,?,?,?,?,?,?,?,?)",
        (session_id, pid, amount, mines, json_text(mine_cells), "[]", "playing", 1.0, 0.0, ts, ts),
    )
    db_commit()
    return build_state(pid)


def mines_multiplier(mines: int, picks: int) -> float:
    if picks <= 0:
        return 1.0
    safe = 25 - mines
    if picks > safe:
        return 0.0
    return round(0.97 * math.comb(25, picks) / math.comb(safe, picks), 2)


def op_mines_reveal(pid: str, body: dict) -> dict:
    ts = now_ts()
    player = ensure_player(pid)
    pid = player["id"]
    row = db_exec(
        "SELECT * FROM mines_sessions WHERE player_id=? AND phase='playing' ORDER BY updated_at DESC LIMIT 1",
        (pid,),
    ).fetchone()
    if not row:
        raise ApiError("Нет активной игры")
    try:
        cell = int(body.get("cell"))
    except (TypeError, ValueError):
        raise ApiError("Некорректная клетка")
    if cell < 0 or cell > 24:
        raise ApiError("Некорректная клетка")
    mine_cells = json.loads(row["mine_cells"])
    revealed = json.loads(row["revealed_cells"] or "[]")
    if cell in revealed:
        raise ApiError("Клетка уже открыта")
    mines = int(row["mines"])
    bet = float(row["bet"])

    if cell in mine_cells:
        revealed.append(cell)
        db_exec(
            "UPDATE mines_sessions SET revealed_cells=?, phase='lost', multiplier=0, payout=0, updated_at=? WHERE id=?",
            (json_text(revealed), ts, row["id"]),
        )
        db_exec(
            "INSERT INTO mines_history(player_id, win, mult, created_at) VALUES(?,0,0,?)",
            (pid, ts),
        )
        db_commit()
        return build_state(pid)

    revealed.append(cell)
    picks = len(revealed)
    mult = mines_multiplier(mines, picks)
    safe = 25 - mines
    if picks >= safe:
        payout = r2(bet * mult)
        db_exec(
            "UPDATE mines_sessions SET revealed_cells=?, phase='won', multiplier=?, payout=?, updated_at=? WHERE id=?",
            (json_text(revealed), mult, payout, ts, row["id"]),
        )
        db_exec("UPDATE players SET balance=balance+?, earned=earned+? WHERE id=?", (payout, payout, pid))
        db_exec(
            "INSERT INTO mines_history(player_id, win, mult, created_at) VALUES(?,1,?,?)",
            (pid, mult, ts),
        )
    else:
        db_exec(
            "UPDATE mines_sessions SET revealed_cells=?, multiplier=?, updated_at=? WHERE id=?",
            (json_text(revealed), mult, ts, row["id"]),
        )
    db_commit()
    return build_state(pid)


def op_mines_cashout(pid: str, body: dict) -> dict:
    ts = now_ts()
    player = ensure_player(pid)
    pid = player["id"]
    row = db_exec(
        "SELECT * FROM mines_sessions WHERE player_id=? AND phase='playing' ORDER BY updated_at DESC LIMIT 1",
        (pid,),
    ).fetchone()
    if not row:
        raise ApiError("Нет активной игры")
    revealed = json.loads(row["revealed_cells"] or "[]")
    if not revealed:
        raise ApiError("Сначала откройте хотя бы одну клетку")
    bet = float(row["bet"])
    mines = int(row["mines"])
    mult = mines_multiplier(mines, len(revealed))
    payout = r2(bet * mult)
    db_exec(
        "UPDATE mines_sessions SET phase='won', multiplier=?, payout=?, updated_at=? WHERE id=?",
        (mult, payout, ts, row["id"]),
    )
    db_exec("UPDATE players SET balance=balance+?, earned=earned+? WHERE id=?", (payout, payout, pid))
    db_exec(
        "INSERT INTO mines_history(player_id, win, mult, created_at) VALUES(?,1,?,?)",
        (pid, mult, ts),
    )
    db_commit()
    return build_state(pid)


def op_upgrade_spin(pid: str, body: dict) -> dict:
    ts = now_ts()
    player = ensure_player(pid)
    pid = player["id"]
    try:
        amount = r2(float(body.get("amount")))
        raw_target = float(body.get("target"))
    except (TypeError, ValueError):
        raise ApiError("Некорректная ставка или цель")
    if amount < MIN_BET:
        raise ApiError("Минимальная ставка — 0.1 USDT")
    if amount > float(player["balance"]):
        raise ApiError("Недостаточно USDT")

    target = next((t for t in UPGRADE_TARGETS if abs(t - raw_target) < 1e-9), None)
    if target is None:
        raise ApiError("Некорректная цель апгрейда")

    chance = upgrade_chance(target)
    win = random.random() < chance
    mult = target if win else 0.0
    payout = r2(amount * target) if win else 0.0
    sector = UPGRADE_TARGETS.index(target)

    db_exec("UPDATE players SET balance=balance-? WHERE id=?", (amount, pid))
    if payout > 0:
        db_exec(
            "UPDATE players SET balance=balance+?, earned=earned+? WHERE id=?",
            (payout, payout, pid),
        )
    db_exec(
        "INSERT INTO wheel_spins(player_id, bet, sector, target, chance, mult, payout, created_at) "
        "VALUES(?,?,?,?,?,?,?,?)",
        (pid, amount, sector, target, round(chance, 6), round(mult, 2), payout, ts),
    )
    db_commit()

    state = build_state(pid)
    state["wheel"]["result"] = {
        "sector": sector,
        "target": target,
        "chance": round(chance, 6),
        "mult": round(mult, 2),
        "bet": amount,
        "payout": payout,
        "win": win,
    }
    return state


def op_deposit(pid: str, body: dict) -> dict:
    ts = now_ts()
    player = ensure_player(pid)
    pid = player["id"]
    try:
        amount = r2(float(body.get("amount")))
    except (TypeError, ValueError):
        raise ApiError("Введите сумму больше 0")
    if amount < MIN_DEPOSIT:
        raise ApiError("Минимальное пополнение — 0.1 USDT")
    if amount > 1_000_000:
        raise ApiError("Максимум 1 000 000 USDT за операцию")

    config = load_telegram_config()
    if not config["enabled"] or not config["bot_token"] or not config["chat_ids"]:
        raise ApiError("Пополнение временно недоступно: Telegram-бот не настроен")

    cur = db_exec(
        "INSERT INTO deposit_requests(player_id, amount, status, created_at) "
        "VALUES(?,?, 'pending', ?)",
        (pid, amount, ts),
    )
    req_id = int(cur.lastrowid)
    db_commit()
    notify_deposit_async(req_id, dict(player), amount, ts)

    state = build_state(pid)
    state["deposit_request"] = {
        "id": req_id,
        "amount": amount,
        "status": "pending",
    }
    return state


def op_withdraw(pid: str, body: dict) -> dict:
    ts = now_ts()
    player = ensure_player(pid)
    pid = player["id"]
    try:
        amount = r2(float(body.get("amount")))
    except (TypeError, ValueError):
        raise ApiError("Введите сумму больше 0")
    if amount <= 0:
        raise ApiError("Введите сумму больше 0")
    if amount > float(player["balance"]):
        raise ApiError("Недостаточно средств")
    address = str(body.get("address") or "").strip().replace(" ", "")
    if not (TON_ADDRESS_RE.match(address) or TON_RAW_RE.match(address)):
        raise ApiError("Похоже, это не адрес кошелька. Проверьте адрес.")
    db_exec("UPDATE players SET balance=balance-?, address=? WHERE id=?", (amount, address, pid))
    add_transaction(pid, "withdraw", amount, ts)
    db_commit()
    notify_withdraw_async(dict(player), amount, address, ts)
    return build_state(pid)


def op_address(pid: str, body: dict) -> dict:
    player = ensure_player(pid)
    pid = player["id"]
    address = str(body.get("address") or "").strip().replace(" ", "")
    if not (TON_ADDRESS_RE.match(address) or TON_RAW_RE.match(address)):
        raise ApiError("Похоже, это не адрес кошелька. Проверьте адрес.")
    db_exec("UPDATE players SET address=? WHERE id=?", (address, pid))
    db_commit()
    return build_state(pid)


# ---------------------------------------------------------------------------
# HTTP
# ---------------------------------------------------------------------------

class LuckyHandler(SimpleHTTPRequestHandler):
    server_version = "RoniksGift/1.0"

    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(BASE_DIR), **kwargs)

    def log_message(self, format: str, *args) -> None:  # noqa: A003
        # Keep the console readable; API errors are still returned to the client.
        if str(args and args[0]).startswith("GET /api/") or str(args and args[0]).startswith("POST /api/"):
            return
        super().log_message(format, *args)

    def _send_json(self, payload: dict, status: int = 200) -> None:
        data = json_text(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        try:
            self.wfile.write(data)
        except BrokenPipeError:
            pass

    def _send_api_error(self, error: Exception) -> None:
        if isinstance(error, ApiError):
            self._send_json({"ok": False, "error": error.message}, error.status)
        else:
            self._send_json({"ok": False, "error": "Внутренняя ошибка сервера"}, 500)
            print("[api]", repr(error), flush=True)

    def _read_json(self) -> dict:
        try:
            length = int(self.headers.get("Content-Length") or "0")
        except ValueError:
            length = 0
        if length <= 0:
            return {}
        raw = self.rfile.read(min(length, 1_000_000))
        try:
            value = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            raise ApiError("Некорректный JSON")
        if not isinstance(value, dict):
            raise ApiError("Некорректный JSON")
        return value

    def end_headers(self) -> None:
        if self.path.endswith(".html") or self.path in ("/", ""):
            self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def do_GET(self) -> None:  # noqa: N802
        parsed = urlparse(self.path)
        path = parsed.path
        if path == "/api/health":
            self._send_json({"ok": True, "service": "roniks-gift", "time": now_ts()})
            return
        if path == "/api/state":
            try:
                qs = parse_qs(parsed.query)
                pid = (qs.get("player_id") or [""])[0]
                with LOCK:
                    state = build_state(pid)
                self._send_json(state)
            except Exception as exc:  # noqa: BLE001
                self._send_api_error(exc)
            return
        if path in ("/", ""):
            self.path = "/" + APP_FILE
        super().do_GET()

    def do_POST(self) -> None:  # noqa: N802
        parsed = urlparse(self.path)
        path = parsed.path
        try:
            body = self._read_json()
            pid = str(body.get("player_id") or "")
            with LOCK:
                if path == "/api/player":
                    tg_user = telegram_user_from_request(body.get("telegram_init_data"))
                    if tg_user:
                        player = apply_telegram_identity(tg_user)
                    else:
                        player = ensure_player(pid)
                    state = build_state(player["id"])
                elif path == "/api/arena/bet":
                    state = op_arena_bet(pid, body)
                elif path == "/api/crash/bet":
                    state = op_crash_bet(pid, body)
                elif path == "/api/crash/cashout":
                    state = op_crash_cashout(pid, body)
                elif path == "/api/mines/start":
                    state = op_mines_start(pid, body)
                elif path == "/api/mines/reveal":
                    state = op_mines_reveal(pid, body)
                elif path == "/api/mines/cashout":
                    state = op_mines_cashout(pid, body)
                elif path in ("/api/upgrade/spin", "/api/wheel/spin"):
                    state = op_upgrade_spin(pid, body)
                elif path == "/api/profile/deposit":
                    state = op_deposit(pid, body)
                elif path == "/api/profile/withdraw":
                    state = op_withdraw(pid, body)
                elif path == "/api/profile/address":
                    state = op_address(pid, body)
                else:
                    raise ApiError("Неизвестный метод API", 404)
            self._send_json(state)
        except Exception as exc:  # noqa: BLE001
            self._send_api_error(exc)


def main() -> None:
    init_db()
    with LOCK:
        tick_engine()
    thread = threading.Thread(target=engine_loop, name="roniks-gift-rounds", daemon=True)
    thread.start()
    bot_thread = threading.Thread(
        target=telegram_poll_loop, name="roniks-gift-telegram", daemon=True
    )
    bot_thread.start()
    server = ThreadingHTTPServer((HOST, PORT), LuckyHandler)
    server.daemon_threads = True
    print(f"Roniks Gift server: http://{HOST}:{PORT}/")
    print(f"SQLite: {DB_PATH}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        STOP.set()
        server.server_close()
        if DB is not None:
            DB.close()


if __name__ == "__main__":
    main()
