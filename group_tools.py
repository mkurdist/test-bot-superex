# -*- coding: utf-8 -*-
"""
group_tools.py
---------------------------------------------------------
ماژول ایزوله برای ۲ قابلیت مدیریت گروه:

    1) آمار فعالیت اعضا (۷ روز گذشته)
       - شمارش پیام هر عضو در حافظه و ذخیره‌ی دسته‌ای در SQLite
       - دستور دستی  /stats  یا  «آمار»  (فقط ادمین‌ها)
       - ارسال خودکار روزانه (اختیاری، با STATS_AUTO_TIME)

    2) عضویت اجباری کانال
       - پیام کاربری که عضو کانال نیست حذف می‌شود
       - یک پیام هشدار با دکمه‌ی «عضویت در کانال» و «عضو شدم» می‌آید
       - ادمین‌های گروه و پیام‌های کانال/ادمین ناشناس معاف‌اند

اتصال به main.py فقط ۴ خط است (انتهای همین فایل را ببینید).

متغیرهای محیطی (همه اختیاری):
    FORCE_JOIN_ENABLED   = 1 / 0                     (پیش‌فرض 1)
    FORCE_JOIN_CHANNEL   = @SuperExNews_Iran         (یوزرنیم یا آیدی عددی کانال)
    FORCE_JOIN_URL       = https://t.me/...          (فقط اگر کانال خصوصی است)
    GROUP_IDS            = -1001234,-1005678         (خالی = همه‌ی گروه‌هایی که ربات در آن‌هاست)
    GROUP_STATS_DB       = group_stats.sqlite3       (روی Render مسیر دیسک پایدار بدهید)
    STATS_TOP_N          = 50
    MEMBER_CACHE_TTL     = 21600                     (شبکه‌ی ایمنی؛ لازم نیست دست بزنید)
    STATS_AUTO_TIME      = 23:00                     (به وقت تهران؛ خالی = ارسال خودکار خاموش)
---------------------------------------------------------
"""

import asyncio
import html
import logging
import os
import sqlite3
import threading
import time
from datetime import datetime, timedelta, timezone
from typing import Dict, List, Optional, Set, Tuple

from aiogram import Bot, Dispatcher, Router, types, F
from aiogram.filters import Command
from aiogram.filters.callback_data import CallbackData
from aiogram.dispatcher.middlewares.base import BaseMiddleware
from aiogram.types import InlineKeyboardMarkup, InlineKeyboardButton

logger = logging.getLogger("group_tools")

group_router = Router(name="group_tools_router")

# ===========================================================
# Config
# ===========================================================
TEHRAN_TZ = timezone(timedelta(hours=3, minutes=30))  # ایران ساعت تابستانی ندارد

FORCE_JOIN_ENABLED = os.getenv("FORCE_JOIN_ENABLED", "1").strip() not in ("0", "false", "False", "")
_raw_channel = os.getenv("FORCE_JOIN_CHANNEL", "@SuperExNews_Iran").strip()
FORCE_CHANNEL = int(_raw_channel) if _raw_channel.lstrip("-").isdigit() else _raw_channel
FORCE_CHANNEL_URL = os.getenv("FORCE_JOIN_URL") or (
    f"https://t.me/{_raw_channel.lstrip('@')}" if not _raw_channel.lstrip("-").isdigit() else "https://t.me/SuperExNews_Iran"
)

_raw_groups = os.getenv("GROUP_IDS", "").strip()
ALLOWED_GROUP_IDS: Set[int] = {int(x) for x in _raw_groups.split(",") if x.strip().lstrip("-").isdigit()}

DB_PATH = os.getenv("GROUP_STATS_DB", "group_stats.sqlite3")
STATS_TOP_N = int(os.getenv("STATS_TOP_N", "50"))
STATS_AUTO_TIME = os.getenv("STATS_AUTO_TIME", "").strip()  # "23:00"
STATS_WINDOW_DAYS = 7

FLUSH_INTERVAL = 10          # ثانیه: هر چند ثانیه شمارنده‌ها در دیتابیس ذخیره شوند
MEMBER_CACHE_TTL = int(os.getenv("MEMBER_CACHE_TTL", "21600"))  # فقط شبکه‌ی ایمنی (۶ ساعت)؛ خروج از کانال با رویداد chat_member فوراً از کش پاک می‌شود
ADMIN_CACHE_TTL = 300
WARN_COOLDOWN = 30           # هر کاربر حداکثر هر ۳۰ ثانیه یک هشدار می‌گیرد
WARN_DELETE_AFTER = 25       # پیام هشدار بعد از این مدت پاک می‌شود

# پیام‌های سرویسی تلگرام (ورود/خروج، پین، ...) که نه شمرده می‌شوند و نه محدودیت می‌خورند
_SERVICE_TYPES = {
    "new_chat_members", "left_chat_member", "new_chat_title", "new_chat_photo",
    "delete_chat_photo", "group_chat_created", "supergroup_chat_created",
    "channel_chat_created", "message_auto_delete_timer_changed", "migrate_to_chat_id",
    "migrate_from_chat_id", "pinned_message", "forum_topic_created", "forum_topic_edited",
    "forum_topic_closed", "forum_topic_reopened", "general_forum_topic_hidden",
    "general_forum_topic_unhidden", "video_chat_scheduled", "video_chat_started",
    "video_chat_ended", "video_chat_participants_invited", "write_access_allowed",
    "boost_added", "chat_background_set",
}
_TELEGRAM_SERVICE_IDS = {777000, 1087968824}  # Telegram / GroupAnonymousBot


def _chat_allowed(chat_id: int) -> bool:
    return not ALLOWED_GROUP_IDS or chat_id in ALLOWED_GROUP_IDS


# ===========================================================
# Persian date helpers (بدون نیاز به کتابخانه‌ی اضافه)
# ===========================================================
_FA_DIGITS = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")
_FA_MONTHS = ["فروردین", "اردیبهشت", "خرداد", "تیر", "مرداد", "شهریور",
              "مهر", "آبان", "آذر", "دی", "بهمن", "اسفند"]
_FA_WEEKDAYS = ["دوشنبه", "سه‌شنبه", "چهارشنبه", "پنجشنبه", "جمعه", "شنبه", "یکشنبه"]  # weekday(): Mon=0


def fa_digits(text: str) -> str:
    return str(text).translate(_FA_DIGITS)


def gregorian_to_jalali(gy: int, gm: int, gd: int) -> Tuple[int, int, int]:
    g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    gy2 = gy + 1 if gm > 2 else gy
    days = (355666 + (365 * gy) + ((gy2 + 3) // 4) - ((gy2 + 99) // 100)
            + ((gy2 + 399) // 400) + gd + g_d_m[gm - 1])
    jy = -1595 + (33 * (days // 12053))
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm = 1 + (days // 31)
        jd = 1 + (days % 31)
    else:
        jm = 7 + ((days - 186) // 30)
        jd = 1 + ((days - 186) % 30)
    return jy, jm, jd


def _now_tehran() -> datetime:
    return datetime.now(TEHRAN_TZ)


# ===========================================================
# SQLite (sync) + اجرای آن در thread تا event loop بلاک نشود
# ===========================================================
_db_lock = threading.Lock()
_conn: Optional[sqlite3.Connection] = None


def _get_conn() -> sqlite3.Connection:
    global _conn
    if _conn is None:
        _conn = sqlite3.connect(DB_PATH, check_same_thread=False)
        _conn.execute("PRAGMA journal_mode=WAL")
        _conn.execute("""CREATE TABLE IF NOT EXISTS msg_counts (
            chat_id INTEGER NOT NULL, user_id INTEGER NOT NULL, day TEXT NOT NULL,
            cnt INTEGER NOT NULL DEFAULT 0, PRIMARY KEY (chat_id, user_id, day))""")
        _conn.execute("""CREATE TABLE IF NOT EXISTS users (
            chat_id INTEGER NOT NULL, user_id INTEGER NOT NULL, name TEXT,
            is_channel INTEGER NOT NULL DEFAULT 0, PRIMARY KEY (chat_id, user_id))""")
        _conn.execute("CREATE TABLE IF NOT EXISTS meta (k TEXT PRIMARY KEY, v TEXT)")
        _conn.commit()
    return _conn


def _flush_sync(counts: Dict[Tuple[int, int, str], int], names: Dict[Tuple[int, int], Tuple[str, int]]) -> None:
    with _db_lock:
        conn = _get_conn()
        conn.executemany(
            "INSERT INTO msg_counts (chat_id, user_id, day, cnt) VALUES (?,?,?,?) "
            "ON CONFLICT(chat_id, user_id, day) DO UPDATE SET cnt = cnt + excluded.cnt",
            [(c, u, d, n) for (c, u, d), n in counts.items()],
        )
        conn.executemany(
            "INSERT INTO users (chat_id, user_id, name, is_channel) VALUES (?,?,?,?) "
            "ON CONFLICT(chat_id, user_id) DO UPDATE SET name = excluded.name, is_channel = excluded.is_channel",
            [(c, u, nm, ch) for (c, u), (nm, ch) in names.items()],
        )
        conn.commit()


def _query_top_sync(chat_id: int, since_day: str, limit: int) -> List[Tuple[int, int, str, int]]:
    with _db_lock:
        cur = _get_conn().execute(
            "SELECT m.user_id, SUM(m.cnt) AS total, COALESCE(u.name, ''), COALESCE(u.is_channel, 0) "
            "FROM msg_counts m LEFT JOIN users u ON u.chat_id = m.chat_id AND u.user_id = m.user_id "
            "WHERE m.chat_id = ? AND m.day >= ? GROUP BY m.user_id "
            "ORDER BY total DESC, m.user_id LIMIT ?",
            (chat_id, since_day, limit),
        )
        return cur.fetchall()


def _active_chats_sync(since_day: str) -> List[int]:
    with _db_lock:
        cur = _get_conn().execute("SELECT DISTINCT chat_id FROM msg_counts WHERE day >= ?", (since_day,))
        return [r[0] for r in cur.fetchall()]


def _prune_sync(before_day: str) -> None:
    with _db_lock:
        conn = _get_conn()
        conn.execute("DELETE FROM msg_counts WHERE day < ?", (before_day,))
        conn.commit()


def _meta_get_sync(key: str) -> Optional[str]:
    with _db_lock:
        row = _get_conn().execute("SELECT v FROM meta WHERE k = ?", (key,)).fetchone()
        return row[0] if row else None


def _meta_set_sync(key: str, value: str) -> None:
    with _db_lock:
        conn = _get_conn()
        conn.execute("INSERT INTO meta (k, v) VALUES (?, ?) ON CONFLICT(k) DO UPDATE SET v = excluded.v", (key, value))
        conn.commit()


# ===========================================================
# 1) آمار فعالیت
# ===========================================================
_buf_counts: Dict[Tuple[int, int, str], int] = {}
_buf_names: Dict[Tuple[int, int], Tuple[str, int]] = {}


def _record(chat_id: int, user_id: int, name: str, is_channel: bool) -> None:
    day = _now_tehran().strftime("%Y-%m-%d")
    key = (chat_id, user_id, day)
    _buf_counts[key] = _buf_counts.get(key, 0) + 1
    _buf_names[(chat_id, user_id)] = (name[:60], 1 if is_channel else 0)


async def flush_buffers() -> None:
    """بافر حافظه را (بدون بلاک کردن event loop) در SQLite می‌نویسد."""
    global _buf_counts, _buf_names
    if not _buf_counts and not _buf_names:
        return
    counts, names = _buf_counts, _buf_names
    _buf_counts, _buf_names = {}, {}
    try:
        await asyncio.to_thread(_flush_sync, counts, names)
    except Exception as e:
        logger.error(f"[group_tools] flush failed, will retry: {e}")
        for k, n in counts.items():          # برگرداندن به بافر تا از دست نرود
            _buf_counts[k] = _buf_counts.get(k, 0) + n
        for k, v in names.items():
            _buf_names.setdefault(k, v)


def _build_stats_text(rows: List[Tuple[int, int, str, int]]) -> str:
    now = _now_tehran()
    jy, jm, jd = gregorian_to_jalali(now.year, now.month, now.day)
    date_str = fa_digits(f"{jd:02d} {_FA_MONTHS[jm - 1]} {jy}")
    time_str = fa_digits(now.strftime("%H:%M:%S"))

    head = [
        f"➖ <b>آمار کل فعالیت های {fa_digits(STATS_WINDOW_DAYS)} روز گذشته</b>",
        "",
        f"• {_FA_WEEKDAYS[now.weekday()]}: {date_str}",
        f"• ساعت : {time_str}",
        "",
        "• فعال ترین اعضا به ترتیب:",
        "",
    ]
    text = "\n".join(head)
    for i, (user_id, total, name, is_channel) in enumerate(rows, 1):
        safe = html.escape((name or "کاربر").strip()[:28])
        label = f"<b>{safe}</b>" if is_channel else f"<a href='tg://user?id={user_id}'>{safe}</a>"
        line = f"\nنفر {i} {label} با {total} پیام"
        if len(text) + len(line) > 3900:      # سقف ۴۰۹۶ کاراکتر تلگرام
            break
        text += line
    return text


async def build_stats_for_chat(chat_id: int) -> Optional[str]:
    await flush_buffers()
    since = (_now_tehran() - timedelta(days=STATS_WINDOW_DAYS - 1)).strftime("%Y-%m-%d")
    rows = await asyncio.to_thread(_query_top_sync, chat_id, since, STATS_TOP_N)
    if not rows:
        return None
    return _build_stats_text(rows)


_admin_cache: Dict[Tuple[int, int], Tuple[float, bool]] = {}


async def _is_group_admin(bot: Bot, chat_id: int, user_id: int) -> bool:
    key = (chat_id, user_id)
    hit = _admin_cache.get(key)
    if hit and hit[0] > time.time():
        return hit[1]
    try:
        cm = await bot.get_chat_member(chat_id, user_id)
        status = getattr(cm.status, "value", cm.status)
        result = status in ("creator", "administrator")
    except Exception as e:
        logger.warning(f"[group_tools] admin check failed: {e}")
        return False
    _admin_cache[key] = (time.time() + ADMIN_CACHE_TTL, result)
    return result


@group_router.message(Command("stats"))
@group_router.message(F.text == "آمار")
async def handle_stats_command(message: types.Message):
    chat = message.chat
    if chat.type not in ("group", "supergroup") or not _chat_allowed(chat.id):
        return
    # ادمین ناشناس (sender_chat == خود گروه) یا ادمین عادی
    is_admin = (message.sender_chat is not None and message.sender_chat.id == chat.id) or (
        message.from_user is not None and await _is_group_admin(message.bot, chat.id, message.from_user.id)
    )
    if not is_admin:
        return  # Silent
    text = await build_stats_for_chat(chat.id)
    if text:
        await message.answer(text, parse_mode="HTML", disable_web_page_preview=True)


@group_router.message(Command("id"))
async def handle_chat_id_command(message: types.Message):
    """آیدی عددی گروه را نشان می‌دهد (برای پر کردن LISTING_CHAT_ID). فقط ادمین‌ها."""
    chat = message.chat
    if chat.type not in ("group", "supergroup"):
        return
    is_admin = (message.sender_chat is not None and message.sender_chat.id == chat.id) or (
        message.from_user is not None and await _is_group_admin(message.bot, chat.id, message.from_user.id)
    )
    if is_admin:
        await message.answer(f"🆔 آیدی این گروه:\n<code>{chat.id}</code>", parse_mode="HTML")


async def _maybe_auto_post(bot: Bot) -> None:
    if not STATS_AUTO_TIME:
        return
    try:
        hh, mm = (int(x) for x in STATS_AUTO_TIME.split(":"))
    except ValueError:
        return
    now = _now_tehran()
    if (now.hour, now.minute) < (hh, mm):
        return
    today = now.strftime("%Y-%m-%d")
    if await asyncio.to_thread(_meta_get_sync, "last_auto_post") == today:
        return
    await asyncio.to_thread(_meta_set_sync, "last_auto_post", today)   # اول ثبت می‌کنیم تا دوبار نرود

    await flush_buffers()
    since = (now - timedelta(days=STATS_WINDOW_DAYS - 1)).strftime("%Y-%m-%d")
    for chat_id in await asyncio.to_thread(_active_chats_sync, since):
        if not _chat_allowed(chat_id):
            continue
        try:
            text = await build_stats_for_chat(chat_id)
            if text:
                await bot.send_message(chat_id, text, parse_mode="HTML", disable_web_page_preview=True)
        except Exception as e:
            logger.warning(f"[group_tools] auto-post to {chat_id} failed: {e}")


# ===========================================================
# 2) عضویت اجباری کانال
# ===========================================================
class JoinCheckCallback(CallbackData, prefix="fj"):
    user_id: int


_member_cache: Dict[int, float] = {}                 # user_id -> expiry (فقط عضوها)
_exempt_cache: Dict[Tuple[int, int], float] = {}     # (chat_id, user_id) -> expiry (ادمین‌ها)
_warn_ts: Dict[Tuple[int, int], float] = {}
_bg_tasks: Set[asyncio.Task] = set()
_last_error_log = 0.0


def _log_throttled(msg: str) -> None:
    global _last_error_log
    if time.time() - _last_error_log > 300:
        _last_error_log = time.time()
        logger.error(msg)


def _status_is_member(cm) -> bool:
    status = getattr(cm.status, "value", cm.status)
    return status in ("creator", "administrator", "member") or (
        status == "restricted" and bool(getattr(cm, "is_member", False))
    )


def _is_force_channel(chat) -> bool:
    """آیا این چت همان کانال عضویت اجباری است؟"""
    if isinstance(FORCE_CHANNEL, int):
        return chat.id == FORCE_CHANNEL
    return (chat.username or "").lower() == FORCE_CHANNEL.lstrip("@").lower()


@group_router.chat_member()
async def on_channel_member_update(event: types.ChatMemberUpdated):
    """
    تلگرام خودش هر بار کسی وارد/خارج کانال شود این رویداد را می‌فرستد (بدون هیچ فشار اضافه).
    ربات باید ادمین کانال باشد و "chat_member" در allowed_updates باشد.
    """
    if not FORCE_JOIN_ENABLED or not _is_force_channel(event.chat):
        return
    user_id = event.new_chat_member.user.id
    if _status_is_member(event.new_chat_member):
        _member_cache[user_id] = time.time() + MEMBER_CACHE_TTL
        logger.info(f"[group_tools] {user_id} عضو کانال شد")
    else:
        _member_cache.pop(user_id, None)
        _exempt_cache_clear_user(user_id)
        logger.info(f"[group_tools] {user_id} از کانال خارج شد؛ از لیست مجازها حذف شد")


def _exempt_cache_clear_user(user_id: int) -> None:
    for key in [k for k in _exempt_cache if k[1] == user_id]:
        _exempt_cache.pop(key, None)


async def is_channel_member(bot: Bot, user_id: int, use_cache: bool = True) -> Optional[bool]:
    """True/False، یا None اگر استعلام ممکن نبود (در این حالت کاربر را رد نمی‌کنیم)."""
    now = time.time()
    if use_cache and _member_cache.get(user_id, 0) > now:
        return True
    try:
        cm = await bot.get_chat_member(FORCE_CHANNEL, user_id)
    except Exception as e:
        _log_throttled(
            f"[group_tools] get_chat_member on {FORCE_CHANNEL} failed: {e} "
            f"(ربات باید ادمین کانال باشد؛ تا آن موقع محدودیت اعمال نمی‌شود)"
        )
        return None
    is_member = _status_is_member(cm)
    if is_member:
        _member_cache[user_id] = now + MEMBER_CACHE_TTL
    else:
        _member_cache.pop(user_id, None)
    return is_member


def _spawn(coro) -> None:
    task = asyncio.create_task(coro)
    _bg_tasks.add(task)
    task.add_done_callback(_bg_tasks.discard)


async def _delete_later(msg: types.Message, delay: int) -> None:
    await asyncio.sleep(delay)
    try:
        await msg.delete()
    except Exception:
        pass


async def _enforce_join(message: types.Message, user: types.User) -> None:
    try:
        await message.delete()
    except Exception as e:
        _log_throttled(f"[group_tools] cannot delete message (ربات باید ادمین با دسترسی حذف پیام باشد): {e}")

    key = (message.chat.id, user.id)
    now = time.time()
    if now - _warn_ts.get(key, 0) < WARN_COOLDOWN:
        return
    _warn_ts[key] = now

    name = html.escape(user.full_name[:30])
    text = (
        f"⚠️ <a href='tg://user?id={user.id}'>{name}</a> عزیز، برای ارسال پیام در گروه "
        f"باید ابتدا در کانال رسمی ما عضو شوید.\n\n"
        f"بعد از عضویت روی دکمه «عضو شدم» بزنید."
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="عضویت در کانال 📢", url=FORCE_CHANNEL_URL),
        InlineKeyboardButton(text="✅ عضو شدم", callback_data=JoinCheckCallback(user_id=user.id).pack()),
    ]])
    try:
        sent = await message.answer(text, parse_mode="HTML", reply_markup=kb)
        _spawn(_delete_later(sent, WARN_DELETE_AFTER))
    except Exception as e:
        logger.warning(f"[group_tools] warning send failed: {e}")


async def _passes_force_join(message: types.Message, user: types.User) -> bool:
    bot = message.bot
    chat_id = message.chat.id
    now = time.time()

    if _exempt_cache.get((chat_id, user.id), 0) > now:
        return True

    member = await is_channel_member(bot, user.id)
    if member is not False:          # True یا None (خطا => fail-open)
        return True

    if await _is_group_admin(bot, chat_id, user.id):
        _exempt_cache[(chat_id, user.id)] = now + ADMIN_CACHE_TTL
        return True

    await _enforce_join(message, user)
    return False


@group_router.callback_query(JoinCheckCallback.filter())
async def on_join_check(query: types.CallbackQuery, callback_data: JoinCheckCallback):
    if query.from_user.id != callback_data.user_id:
        await query.answer("این دکمه مخصوص شما نیست.", show_alert=True)
        return
    member = await is_channel_member(query.bot, query.from_user.id, use_cache=False)
    if member is False:
        await query.answer("هنوز عضو کانال نشده‌اید ❌", show_alert=True)
        return
    await query.answer("✅ عضویت شما تأیید شد، می‌توانید پیام بدهید.", show_alert=True)
    try:
        await query.message.delete()
    except Exception:
        pass


# ===========================================================
# Middleware: برای هر پیام گروه، اول عضویت چک می‌شود، بعد شمارش
# (Middleware است تا بقیه‌ی هندلرهای ربات مثل قیمت/چارت دست‌نخورده کار کنند)
# ===========================================================
def _is_service_message(message: types.Message) -> bool:
    ct = getattr(message.content_type, "value", message.content_type)
    return ct in _SERVICE_TYPES


async def _process_group_message(message: types.Message) -> bool:
    """False یعنی پیام مسدود شد و نباید به هندلرهای دیگر برسد."""
    chat = message.chat
    if chat.type not in ("group", "supergroup") or not _chat_allowed(chat.id):
        return True
    if _is_service_message(message):
        return True

    if message.sender_chat is not None:
        # پیام از طرف کانال یا ادمین ناشناس؛ شمارش می‌شود ولی محدودیتی ندارد
        sc = message.sender_chat
        _record(chat.id, sc.id, sc.title or "کانال", True)
        return True

    user = message.from_user
    if user is None or user.is_bot or user.id in _TELEGRAM_SERVICE_IDS:
        return True

    if FORCE_JOIN_ENABLED and not await _passes_force_join(message, user):
        return False

    _record(chat.id, user.id, user.full_name or user.first_name or "کاربر", False)
    return True


class GroupGuardMiddleware(BaseMiddleware):
    async def __call__(self, handler, event: types.Message, data):
        try:
            allowed = await _process_group_message(event)
        except Exception as e:
            logger.exception(f"[group_tools] middleware error (fail-open): {e}")
            allowed = True
        if not allowed:
            return None
        return await handler(event, data)


# ===========================================================
# Public API برای main.py
# ===========================================================
def setup_group_tools(dp: Dispatcher) -> None:
    dp.message.outer_middleware(GroupGuardMiddleware())
    dp.include_router(group_router)


def init_group_tools() -> None:
    _get_conn()


async def group_tools_background_loop(bot: Bot) -> None:
    """ذخیره‌ی دسته‌ای شمارنده‌ها، ارسال خودکار آمار و تمیزکاری کش‌ها/دیتای قدیمی."""
    last_prune = 0.0
    while True:
        try:
            await flush_buffers()
            await _maybe_auto_post(bot)

            now = time.time()
            if now - last_prune > 3600:
                last_prune = now
                for store in (_member_cache, _exempt_cache):
                    for k in [k for k, exp in store.items() if exp < now]:
                        store.pop(k, None)
                for k in [k for k, exp in _admin_cache.items() if exp[0] < now]:
                    _admin_cache.pop(k, None)
                for k in [k for k, ts in _warn_ts.items() if now - ts > 3600]:
                    _warn_ts.pop(k, None)
                old = (_now_tehran() - timedelta(days=STATS_WINDOW_DAYS + 7)).strftime("%Y-%m-%d")
                await asyncio.to_thread(_prune_sync, old)
        except Exception as e:
            logger.warning(f"[group_tools] background loop error: {e}")
        await asyncio.sleep(FLUSH_INTERVAL)


async def shutdown_group_tools() -> None:
    await flush_buffers()
