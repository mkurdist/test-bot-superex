# -*- coding: utf-8 -*-
"""
listing_monitor.py
---------------------------------------------------------
مانیتور مرکز اطلاعیه‌های SuperEx (نسخه‌ی فارسی) و ارسال خبرها به تلگرام.

چهار بخش پایش می‌شود: لیست‌های جدید، اطلاعیه‌ها، رویدادها، به‌روزرسانی/نگهداری/حذف.

جریان کار:
    ۱) هر بخش را می‌خواند (اول API عمومی Zendesk، اگر نشد HTML با BeautifulSoup).
    ۲) شناسه‌ی عددی هر مقاله را با دیتابیس «دیده‌شده‌ها» مقایسه می‌کند.
    ۳) فقط مقاله‌های جدید را به ترتیب زمانی (قدیمی به جدید) به تلگرام می‌فرستد.
    ۴) هر N ثانیه تکرار می‌کند.

ضد تکرار:
    - ذخیره‌سازی اصلی Supabase است (روی Render دیسک موقت است).
      اگر SUPABASE_URL / SUPABASE_KEY نباشد، SQLite محلی استفاده می‌شود.
    - اگر هیچ‌کدام از مقاله‌های فعلیِ یک بخش در دیتابیس نباشد (اجرای اول یا بخش تازه)،
      فقط «خط پایه» ثبت می‌شود و هیچ خبر قدیمی ارسال نمی‌شود.
    - خبر فقط بعد از ارسال موفق «دیده‌شده» ثبت می‌شود.
    - اگر دیتابیس در دسترس نباشد، چیزی ارسال نمی‌شود.
    - خرابی یک بخش، بخش‌های دیگر را متوقف نمی‌کند.

اجرا:
    python listing_monitor.py              # اجرای دائمی
    python listing_monitor.py --once       # فقط یک بار چک کن
    python listing_monitor.py --dry-run    # فقط بخوان و پیش‌نمایش پیام را چاپ کن

متغیرهای محیطی:
    BOT_TOKEN                توکن ربات
    LISTING_CHAT_ID          مقصدها با کاما: @mychannel,-100123456789  (تاپیک: -100123456789:55)
    LISTING_SECTIONS         بخش‌های فعال با کاما (پیش‌فرض همه): listings,announcements,events,updates
    LISTING_CHECK_INTERVAL   فاصله‌ی چک به ثانیه (پیش‌فرض 600)
    LISTING_MAX_PER_CYCLE    سقف پیام هر بخش در هر دوره (پیش‌فرض 5)
    LISTING_PREVIEW          1 = پیش‌نمایش لینک روشن (پیش‌فرض 0)
    SUPABASE_URL, SUPABASE_KEY, SUPABASE_TABLE (پیش‌فرض seen_listings)
    LISTING_SQLITE_PATH      مسیر SQLite جایگزین
---------------------------------------------------------
"""

import argparse
import html
import logging
import os
import re
import signal
import sqlite3
import threading
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Iterable, List, Optional, Set
from urllib.parse import urljoin, urlparse

import requests
import premium_emoji as pe
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

logger = logging.getLogger("listing_monitor")


# ===========================================================
# بخش‌های پایش‌شده + ظاهر پیام
# emoji: اینجا هر چیزی بگذارید (حتی ایموجی پریمیوم) بالای پیام می‌آید. مثال:
#   '<tg-emoji emoji-id="5368324170671202286">🆕</tg-emoji>'
# ===========================================================
@dataclass(frozen=True)
class Section:
    key: str        # شناسه‌ی داخلی (برای LISTING_SECTIONS)
    title: str      # تیتر پیام
    hashtag: str    # هشتگ پایین پیام
    url: str        # آدرس بخش در مرکز اطلاعیه‌ها (نسخه‌ی فارسی)
    emoji: str = ""  # ایموجی کنار تیتر (خالی = بدون ایموجی)
    detailed: bool = False  # فقط لیستینگ‌ها: نمایش دسته‌بندی و نماد


_BASE = "https://support.superex.com/hc/fa/sections/"
ALL_SECTIONS = (
    Section("listings", "لیست جدید", "#لیست_جدید", _BASE + "9117167570457", detailed=True),
    Section("announcements", "اطلاعیه", "#اطلاعیه", _BASE + "9117102988825"),
    Section("events", "رویداد", "#رویداد", _BASE + "9117136933657"),
    Section("updates", "به‌روزرسانی و نگهداری", "#به_روزرسانی", _BASE + "9117198982041"),
)

BROWSER_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "en-US,en;q=0.9",
    "Accept": "text/html,application/xhtml+xml,application/json;q=0.9,*/*;q=0.8",
}

HTTP_TIMEOUT = (10, 20)   # (connect, read) ثانیه
STOP_EVENT = threading.Event()


# ===========================================================
# خطاهای اختصاصی (تا حلقه‌ی اصلی بداند چه اتفاقی افتاده)
# ===========================================================
class FetchError(Exception):
    """خطای شبکه یا پاسخ نامعتبر از سایت صرافی."""


class ParseError(Exception):
    """ساختار صفحه عوض شده و هیچ مقاله‌ای پیدا نشد."""


class StorageError(Exception):
    """خطای دیتابیس (Supabase / SQLite)."""


class TelegramError(Exception):
    """خطای غیرقابل‌تلاش‌مجدد تلگرام (مثلاً ربات از کانال حذف شده)."""


# ===========================================================
# تنظیمات
# ===========================================================
def _pick_sections(raw: str) -> tuple:
    wanted = {x.strip() for x in raw.split(",") if x.strip()}
    chosen = tuple(sec for sec in ALL_SECTIONS if not wanted or sec.key in wanted)
    return chosen or ALL_SECTIONS


@dataclass(frozen=True)
class Config:
    bot_token: str
    chat_ids: tuple  # هر عضو: (chat_id, thread_id|None)
    sections: tuple
    interval: int
    max_per_cycle: int
    preview: bool
    supabase_url: str
    supabase_key: str
    supabase_table: str
    sqlite_path: str

    @classmethod
    def from_env(cls) -> "Config":
        try:  # اگر python-dotenv نصب است (در requirements هست) فایل .env را بخوان
            from dotenv import load_dotenv
            load_dotenv()
        except ImportError:
            pass
        # چند مقصد با کاما: «@mychannel,-1001234567890» یا برای تاپیک «-1001234567890:55»
        targets = []
        for part in os.getenv("LISTING_CHAT_ID", "").split(","):
            part = part.strip()
            if not part:
                continue
            chat, _, thread = part.partition(":")
            targets.append((chat.strip(), int(thread) if thread.strip().isdigit() else None))
        return cls(
            bot_token=os.getenv("BOT_TOKEN", "").strip(),
            chat_ids=tuple(targets),
            sections=_pick_sections(os.getenv("LISTING_SECTIONS", "")),
            interval=max(60, int(os.getenv("LISTING_CHECK_INTERVAL", "600"))),
            max_per_cycle=max(1, int(os.getenv("LISTING_MAX_PER_CYCLE", "5"))),
            preview=os.getenv("LISTING_PREVIEW", "0").strip() == "1",
            supabase_url=os.getenv("SUPABASE_URL", "").strip().rstrip("/"),
            supabase_key=os.getenv("SUPABASE_KEY", "").strip(),
            supabase_table=os.getenv("SUPABASE_TABLE", "seen_listings").strip(),
            sqlite_path=os.getenv("LISTING_SQLITE_PATH", "listing_seen.sqlite3").strip(),
        )

    def validate(self, need_telegram: bool = True) -> None:
        missing = []
        if need_telegram and not self.bot_token:
            missing.append("BOT_TOKEN")
        if need_telegram and not self.chat_ids:
            missing.append("LISTING_CHAT_ID")
        if missing:
            raise SystemExit(f"متغیرهای محیطی لازم تنظیم نشده‌اند: {', '.join(missing)}")


@dataclass(frozen=True)
class Listing:
    article_id: int
    title: str
    url: str
    date_str: str = ""  # تاریخ مقاله (اضافه شده برای نمایش شمسی)


# ===========================================================
# توابع کمکی برای تبدیل تاریخ
# ===========================================================
def gregorian_to_jalali(gy: int, gm: int, gd: int) -> tuple:
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

def parse_and_format_date(date_str: str) -> str:
    """رشته تاریخ ISO (مثل 2023-04-10T15:45:30Z) را به شمسی تبدیل می‌کند."""
    if not date_str:
        return ""
    try:
        date_part = date_str.split("T")[0]
        y, m, d = map(int, date_part.split("-"))
        jy, jm, jd = gregorian_to_jalali(y, m, d)
        return f"{jy:04d}/{jm:02d}/{jd:02d}"
    except Exception:
        return str(date_str).split("T")[0]


# ===========================================================
# بخش ۱: دریافت و پارس کردن خبرها
# ===========================================================
def build_http_session() -> requests.Session:
    """Session با تلاش مجدد خودکار برای خطاهای موقت شبکه/سرور."""
    session = requests.Session()
    retry = Retry(
        total=3, connect=3, read=3, backoff_factor=1.5,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=frozenset({"GET"}),
    )
    session.mount("https://", HTTPAdapter(max_retries=retry))
    session.mount("http://", HTTPAdapter(max_retries=retry))
    session.headers.update(BROWSER_HEADERS)
    return session


_ARTICLE_ID_RE = re.compile(r"/articles/(\d+)")


def parse_listings_html(html_content: str, base_url: str) -> List[Listing]:
    """
    لینک مقاله‌ها را از HTML صفحه‌ی بخش (Section) زندسک بیرون می‌کشد.
    به‌جای تکیه بر اسم کلاس‌های قالب، همه‌ی لینک‌های /articles/<id> را می‌گیرد؛
    شناسه‌ی عددی داخل URL کلید یکتای ماست (و با گذر زمان بزرگ‌تر می‌شود).
    خروجی به ترتیب نمایش در صفحه (جدیدترین اول) و بدون تکرار است.
    """
    soup = BeautifulSoup(html_content, "html.parser")
    container = soup.select_one("ul.article-list") or soup.select_one("main") or soup

    listings: List[Listing] = []
    seen_ids: Set[int] = set()
    for a in container.find_all("a", href=True):
        match = _ARTICLE_ID_RE.search(a["href"])
        title = a.get_text(" ", strip=True)
        if not match or not title:
            continue
        article_id = int(match.group(1))
        if article_id in seen_ids:
            continue
        seen_ids.add(article_id)
        
        # پیدا کردن تگ زمان در صورت وجود در ساختار HTML
        date_str = ""
        li = a.find_parent("li")
        if li:
            time_tag = li.find("time")
            if time_tag and time_tag.has_attr("datetime"):
                date_str = parse_and_format_date(time_tag["datetime"])

        full = urljoin(base_url, a["href"])
        clean_url = full.split("#")[0].split("?")[0]
        listings.append(Listing(article_id, title, clean_url, date_str))

    if not listings:
        raise ParseError("هیچ مقاله‌ای در صفحه پیدا نشد (احتمالاً ساختار صفحه یا بلاک شدن)")
    return listings


def _zendesk_api_url(source_url: str) -> Optional[str]:
    """از آدرس صفحه، آدرس API عمومی Zendesk همان بخش را می‌سازد."""
    m = re.search(r"/hc/([^/]+)/sections/(\d+)", source_url)
    if not m:
        return None
    parsed = urlparse(source_url)
    return (f"{parsed.scheme}://{parsed.netloc}/api/v2/help_center/{m.group(1)}/sections/{m.group(2)}"
            f"/articles.json?sort_by=created_at&sort_order=desc&per_page=30")


def _fetch_via_api(session: requests.Session, section_url: str) -> List[Listing]:
    api_url = _zendesk_api_url(section_url)
    if not api_url:
        raise FetchError("آدرس API قابل ساخت نیست")
    resp = session.get(api_url, timeout=HTTP_TIMEOUT)
    if resp.status_code != 200:
        raise FetchError(f"API HTTP {resp.status_code}")
    articles = resp.json().get("articles", [])
    
    listings = []
    for a in articles:
        if a.get("id") and a.get("title") and a.get("html_url"):
            dt = parse_and_format_date(str(a.get("created_at", "")))
            listings.append(Listing(
                int(a["id"]), 
                str(a["title"]).strip(), 
                str(a["html_url"]).split("?")[0],
                dt
            ))
            
    if not listings:
        raise ParseError("API مقاله‌ای برنگرداند")
    return listings


def _fetch_via_html(session: requests.Session, section_url: str) -> List[Listing]:
    resp = session.get(section_url, timeout=HTTP_TIMEOUT)
    if resp.status_code != 200:
        raise FetchError(f"HTML HTTP {resp.status_code}")
    return parse_listings_html(resp.text, section_url)


def fetch_listings(session: requests.Session, section_url: str) -> List[Listing]:
    """اول API عمومی Zendesk (روی Render جواب می‌دهد)؛ اگر شکست خورد HTML."""
    try:
        return _fetch_via_api(session, section_url)
    except (requests.RequestException, ValueError, KeyError, FetchError, ParseError) as api_error:
        logger.warning(f"API ناموفق ({type(api_error).__name__}: {api_error}) → تلاش با HTML")
        try:
            return _fetch_via_html(session, section_url)
        except (requests.RequestException, FetchError, ParseError) as html_error:
            raise FetchError(f"API ({api_error}) و HTML ({html_error}) هر دو ناموفق بودند") from html_error


# ===========================================================
# بخش ۲: ذخیره‌سازی «دیده‌شده‌ها»
# ===========================================================
class Storage(ABC):
    @abstractmethod
    def is_empty(self) -> bool: ...

    @abstractmethod
    def get_seen(self, ids: Iterable[int]) -> Set[int]: ...

    @abstractmethod
    def mark_seen(self, listings: Iterable[Listing]) -> None: ...


class SupabaseStorage(Storage):
    """
    از REST خود Supabase (PostgREST) با requests استفاده می‌کند؛ نیازی به کتابخانه‌ی اضافه نیست.
    جدول (SQL در انتهای همین فایل) فقط با service key قابل دسترسی است.
    """

    def __init__(self, url: str, key: str, table: str):
        self.base = f"{url}/rest/v1/{table}"
        self.session = requests.Session()
        headers = {"apikey": key, "Content-Type": "application/json"}
        if key.startswith("eyJ"):  # کلید قدیمی JWT؛ کلیدهای جدید sb_secret_ فقط apikey می‌خواهند
            headers["Authorization"] = f"Bearer {key}"
        self.session.headers.update(headers)

    def _request(self, method: str, **kwargs) -> requests.Response:
        try:
            resp = self.session.request(method, self.base, timeout=HTTP_TIMEOUT, **kwargs)
        except requests.RequestException as e:
            raise StorageError(f"اتصال به Supabase ناموفق: {type(e).__name__}") from e
        if resp.status_code >= 300:
            raise StorageError(f"Supabase HTTP {resp.status_code}: {resp.text[:200]}")
        return resp

    def is_empty(self) -> bool:
        return len(self._request("GET", params={"select": "article_id", "limit": "1"}).json()) == 0

    def get_seen(self, ids: Iterable[int]) -> Set[int]:
        id_list = ",".join(str(i) for i in ids)
        if not id_list:
            return set()
        rows = self._request("GET", params={"select": "article_id", "article_id": f"in.({id_list})"}).json()
        return {int(r["article_id"]) for r in rows}

    def mark_seen(self, listings: Iterable[Listing]) -> None:
        rows = [{"article_id": l.article_id, "title": l.title, "url": l.url} for l in listings]
        if not rows:
            return
        self._request(
            "POST", params={"on_conflict": "article_id"}, json=rows,
            headers={"Prefer": "resolution=ignore-duplicates,return=minimal"},
        )


class SqliteStorage(Storage):
    """جایگزین محلی (برای تست یا وقتی Supabase تنظیم نشده)."""

    def __init__(self, path: str):
        self.lock = threading.Lock()
        try:
            self.conn = sqlite3.connect(path, check_same_thread=False)
            self.conn.execute(
                "CREATE TABLE IF NOT EXISTS seen (article_id INTEGER PRIMARY KEY, title TEXT, url TEXT, "
                "created_at TEXT DEFAULT CURRENT_TIMESTAMP)")
            self.conn.commit()
        except sqlite3.Error as e:
            raise StorageError(f"باز کردن SQLite ناموفق: {e}") from e

    def is_empty(self) -> bool:
        with self.lock:
            return self.conn.execute("SELECT 1 FROM seen LIMIT 1").fetchone() is None

    def get_seen(self, ids: Iterable[int]) -> Set[int]:
        id_list = list(ids)
        if not id_list:
            return set()
        marks = ",".join("?" * len(id_list))
        with self.lock:
            rows = self.conn.execute(f"SELECT article_id FROM seen WHERE article_id IN ({marks})", id_list).fetchall()
        return {r[0] for r in rows}

    def mark_seen(self, listings: Iterable[Listing]) -> None:
        try:
            with self.lock:
                self.conn.executemany(
                    "INSERT OR IGNORE INTO seen (article_id, title, url) VALUES (?,?,?)",
                    [(l.article_id, l.title, l.url) for l in listings])
                self.conn.commit()
        except sqlite3.Error as e:
            raise StorageError(f"نوشتن در SQLite ناموفق: {e}") from e


def build_storage(cfg: Config) -> Storage:
    if cfg.supabase_url and cfg.supabase_key:
        logger.info("ذخیره‌سازی: Supabase")
        return SupabaseStorage(cfg.supabase_url, cfg.supabase_key, cfg.supabase_table)
    logger.warning("SUPABASE_URL/SUPABASE_KEY تنظیم نشده؛ از SQLite محلی استفاده می‌شود "
                   "(روی Render با هر دیپلوی پاک می‌شود)")
    return SqliteStorage(cfg.sqlite_path)


# ===========================================================
# بخش ۳: ساخت پیام
# ===========================================================
def detect_categories(title: str) -> str:
    """دسته‌بندی را از روی کلمات کلیدیِ عنوان فارسی تشخیص می‌دهد (خالی = نامشخص)."""
    cats = []
    if "اسپات" in title:
        cats.append("اسپات")
    if any(w in title for w in ("فیوچرز", "آتی", "پرپچوال", "دائمی", "USDT-M")):
        cats.append("فیوچرز دائمی")
    if "index futures" in title.lower():
        cats.append("مارجین Index Futures")
    return "، ".join(cats)


def detect_symbols(title: str) -> List[str]:
    """نمادها را پیدا می‌کند: (MHA) داخل پرانتز، یا جفت‌های مثل CYPHUSDT."""
    found: List[str] = []
    patterns = (r"\(([A-Z0-9.\-]{2,12})\)", r"(?<![A-Za-z0-9])([A-Z0-9]{2,12}USDT)(?![A-Za-z0-9])")
    for pattern in patterns:
        for sym in re.findall(pattern, title):
            if sym not in found:
                found.append(sym)
    return found[:6]


def format_message(listing: Listing, section: Section, html_mode: bool = True, premium: bool = True) -> str:
    """
    قالب پیام:

        <گل> تیتر بخش <گل>

        <زنگ> عنوان خبر

        تاریخ: ...
        دسته‌بندی: ...        (فقط لیستینگ‌ها)
        نماد: ...             (فقط لیستینگ‌ها)

        <فلش> مشاهده‌ی جزئیات

        <ایموجی هشتگ> نام هشتگ

    premium=False (یا html_mode=False): همان ظاهر ساده با ایموجی معمولی و هشتگ واقعی.
    """
    prem = pe.active(premium and html_mode)
    if html_mode:
        esc = html.escape
        if section.emoji:
            head = f"{section.emoji} <b>{section.title}</b>"
        elif prem:
            head = f"{pe.e('flower_l')} <b>{section.title}</b> {pe.e('flower_r')}"
        else:
            head = f"<b>{section.title}</b>"
        link = f'{pe.e("arrow_link", prem)} <a href="{html.escape(listing.url, quote=True)}">مشاهده‌ی جزئیات</a>'
        sym_fmt = lambda x: f"<code>{html.escape(x)}</code>"
        date_fmt = lambda x: f"📅 <b>تاریخ:</b> {x}"
    else:  # متن ساده‌ی اضطراری: تگ‌های ایموجی حذف و فقط خود ایموجی می‌ماند
        esc = lambda x: x
        plain_emoji = re.sub(r"<[^>]+>", "", section.emoji)
        head = f"{plain_emoji} {section.title}".strip()
        link = f"{pe.PLAIN['arrow_link']} مشاهده‌ی جزئیات:\n{listing.url}"
        sym_fmt = lambda x: x
        date_fmt = lambda x: f"📅 تاریخ: {x}"

    blocks = [head, f"{pe.e('bell', prem)} \u200F{esc(listing.title)}"]

    details = []
    if listing.date_str:
        details.append(date_fmt(listing.date_str))

    if section.detailed:
        category = detect_categories(listing.title)
        if category:
            details.append(f"دسته‌بندی: {category}")
        symbols = detect_symbols(listing.title)
        if symbols:
            details.append(f"\u200Fنماد: " + "، ".join(sym_fmt(x) for x in symbols))

    if details:
        blocks.append("\n".join(details))

    blocks += [link, pe.hashtag(section.hashtag, prem)]
    return "\n\n".join(blocks)


# ===========================================================
# بخش ۴: ارسال به تلگرام
# ===========================================================
class TelegramSender:
    MAX_ATTEMPTS = 4

    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.url = f"https://api.telegram.org/bot{cfg.bot_token}/sendMessage"
        self.session = requests.Session()
        self._no_premium: Set[str] = set()   # مقصدهایی که ایموجی پریمیوم را نپذیرفته‌اند (تا ری‌استارت دیگر امتحان نمی‌شود)

    def _safe(self, text: str) -> str:
        """توکن ربات هرگز در لاگ نیاید."""
        token = self.cfg.bot_token
        return str(text).replace(token, "***") if token else str(text)

    def send(self, listing: Listing, section: Section) -> None:
        """به همه‌ی مقصدها می‌فرستد. فقط اگر به هیچ‌کدام نرسید خطا می‌دهد (تا خبر تکراری نشود)."""
        ok = 0
        last_error: Optional[TelegramError] = None
        for chat_id, thread_id in self.cfg.chat_ids:
            try:
                self._send_to(listing, section, chat_id, thread_id)
                ok += 1
            except TelegramError as e:
                logger.error(f"ارسال به {chat_id} ناموفق: {e}")
                last_error = e
        if ok == 0:
            raise last_error or TelegramError("هیچ مقصدی تنظیم نشده")

    def _send_to(self, listing: Listing, section: Section, chat_id: str, thread_id: Optional[int]) -> None:
        # سه حالت به ترتیب: premium (ایموجی پریمیوم) → html (ایموجی معمولی) → plain (متن ساده)
        mode = "premium" if (pe.ENABLED and chat_id not in self._no_premium) else "html"
        downgraded = False

        def build(m: str) -> str:
            return format_message(listing, section, html_mode=(m != "plain"), premium=(m == "premium"))

        payload = {
            "chat_id": chat_id,
            "text": build(mode),
            "parse_mode": "HTML",
            "disable_web_page_preview": not self.cfg.preview,
        }
        if thread_id:
            payload["message_thread_id"] = thread_id

        for attempt in range(1, self.MAX_ATTEMPTS + 1):
            try:
                resp = self.session.post(self.url, json=payload, timeout=HTTP_TIMEOUT)
            except requests.RequestException as e:
                logger.warning(f"خطای شبکه‌ی تلگرام (تلاش {attempt}): {self._safe(e)}")
                if STOP_EVENT.wait(2 ** attempt):
                    return
                continue

            if resp.status_code == 200:
                if downgraded and mode != "premium":
                    self._no_premium.add(chat_id)   # فقط وقتی نسخه‌ی معمولی رسید یعنی مشکل از ایموجی بوده
                return

            try:
                data = resp.json()
            except ValueError:
                data = {}
            desc = str(data.get("description", resp.text[:200]))

            if resp.status_code == 429:                              # محدودیت نرخ تلگرام
                wait = int(data.get("parameters", {}).get("retry_after", 5)) + 1
                logger.warning(f"Flood control؛ {wait} ثانیه صبر")
                STOP_EVENT.wait(min(wait, 60))
                continue
            if resp.status_code == 400 and mode == "premium":
                logger.warning(f"ایموجی پریمیوم برای {chat_id} پذیرفته نشد ({self._safe(desc)}) → ارسال با ایموجی معمولی")
                downgraded = True
                mode = "html"
                payload["text"] = build(mode)
                continue
            if resp.status_code == 400 and "parse entities" in desc.lower() and "parse_mode" in payload:
                logger.warning("خطای HTML؛ ارسال مجدد به‌صورت متن ساده")
                payload.pop("parse_mode")
                mode = "plain"
                payload["text"] = build(mode)
                continue
            if resp.status_code >= 500:
                STOP_EVENT.wait(2 ** attempt)
                continue
            raise TelegramError(f"HTTP {resp.status_code}: {self._safe(desc)}")

        raise TelegramError("ارسال بعد از چند تلاش ناموفق ماند")


# ===========================================================
# بخش ۵: یک دوره‌ی بررسی + حلقه‌ی اصلی
# ===========================================================
def _process_section(section: Section, cfg: Config, http: requests.Session,
                     storage: Storage, sender: TelegramSender) -> int:
    """یک بخش را بررسی می‌کند و تعداد پیام‌های ارسال‌شده را برمی‌گرداند."""
    listings = fetch_listings(http, section.url)
    seen = storage.get_seen(l.article_id for l in listings)

    # هیچ‌کدام از مقاله‌های فعلی دیده نشده => اجرای اول (یا بخش تازه): فقط خط پایه
    if not seen:
        storage.mark_seen(listings)
        logger.info(f"[{section.key}] خط پایه ثبت شد ({len(listings)} خبر؛ چیزی ارسال نشد)")
        return 0

    new = sorted((l for l in listings if l.article_id not in seen), key=lambda l: l.article_id)
    if not new:
        logger.info(f"[{section.key}] خبر جدیدی نیست")
        return 0

    # محافظ ضد اسپم: اگر ناگهان خیلی زیاد «جدید» دیدیم
    if len(new) > cfg.max_per_cycle:
        skipped, new = new[:-cfg.max_per_cycle], new[-cfg.max_per_cycle:]
        logger.warning(f"[{section.key}] {len(skipped) + len(new)} خبر جدید؛ فقط {len(new)} تای آخر ارسال می‌شود")
        storage.mark_seen(skipped)

    sent = 0
    for listing in new:                       # قدیمی → جدید
        try:
            sender.send(listing, section)
        except TelegramError as e:
            logger.error(f"[{section.key}] ارسال «{listing.title[:60]}» ناموفق: {e} — دوره‌ی بعد دوباره تلاش می‌شود")
            break                             # ترتیب خبرها به‌هم نریزد
        storage.mark_seen([listing])          # فقط بعد از ارسال موفق
        sent += 1
        STOP_EVENT.wait(1.5)
    logger.info(f"[{section.key}] {sent} پیام ارسال شد")
    return sent


def run_once(cfg: Config, http: requests.Session, storage: Storage, sender: TelegramSender) -> int:
    """همه‌ی بخش‌ها را می‌گردد. خرابی یک بخش بقیه را متوقف نمی‌کند."""
    total = 0
    for section in cfg.sections:
        try:
            total += _process_section(section, cfg, http, storage, sender)
        except (FetchError, ParseError) as e:
            logger.warning(f"[{section.key}] دریافت خبرها ناموفق: {e}")
    return total


def run_forever(cfg: Optional[Config] = None) -> None:
    cfg = cfg or Config.from_env()
    cfg.validate()
    http = build_http_session()
    storage = build_storage(cfg)
    sender = TelegramSender(cfg)
    logger.info(f"مانیتور شروع شد؛ فاصله‌ی چک: {cfg.interval} ثانیه")

    while not STOP_EVENT.is_set():
        try:
            run_once(cfg, http, storage, sender)
        except StorageError as e:
            logger.error(f"دیتابیس در دسترس نیست؛ این دوره رد شد: {e}")
        except Exception:
            logger.exception("خطای پیش‌بینی‌نشده؛ حلقه ادامه پیدا می‌کند")
        STOP_EVENT.wait(cfg.interval)         # مثل time.sleep ولی قابل قطع با Ctrl+C / SIGTERM
    logger.info("مانیتور متوقف شد")


def start_in_background() -> threading.Thread:
    """برای اجرا داخل پروسه‌ی main.py (مثلاً روی Render که فقط یک سرویس دارید)."""
    thread = threading.Thread(target=run_forever, name="listing-monitor", daemon=True)
    thread.start()
    return thread


# ===========================================================
# CLI
# ===========================================================
def _dry_run(cfg: Config) -> None:
    http = build_http_session()
    for section in cfg.sections:
        print(f"\n===== {section.key} =====")
        try:
            listings = fetch_listings(http, section.url)
        except (FetchError, ParseError) as e:
            print(f"خطا: {e}")
            continue
        print(f"{len(listings)} خبر پیدا شد. پیش‌نمایش جدیدترین خبر:\n")
        print(format_message(max(listings, key=lambda l: l.article_id), section, html_mode=False))


def _test_send(cfg: Config) -> None:
    """برای هر بخش یک پیام نمونه به مقصدها می‌فرستد تا ظاهر (و ایموجی‌های پریمیوم) را ببینید."""
    sender = TelegramSender(cfg)
    samples = {
        "listings": "SuperEx معاملات اسپات TEST (TST) را لیست می‌کند",
        "announcements": "این یک اطلاعیه‌ی آزمایشی است",
        "events": "این یک رویداد آزمایشی است",
        "updates": "این یک اطلاعیه‌ی آزمایشی نگهداری است",
    }
    for i, section in enumerate(cfg.sections, 1):
        sample = Listing(0 - i, samples.get(section.key, "پیام آزمایشی"),
                         "https://support.superex.com/hc/fa", date_str="۱۴ مهر ۱۴۰۵")
        sender.send(sample, section)
        print(f"ارسال شد: {section.key}")
        STOP_EVENT.wait(1.5)


def main() -> None:
    parser = argparse.ArgumentParser(description="مانیتور لیست‌های جدید SuperEx")
    parser.add_argument("--once", action="store_true", help="فقط یک بار چک کن")
    parser.add_argument("--dry-run", action="store_true", help="فقط بخوان و پیش‌نمایش بده")
    parser.add_argument("--test-send", action="store_true", help="برای هر بخش یک پیام نمونه به مقصدها بفرست (بدون دست زدن به دیتابیس)")
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
    cfg = Config.from_env()

    if args.dry_run:
        _dry_run(cfg)
        return

    cfg.validate()
    if args.test_send:
        _test_send(cfg)
        return
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, lambda *_: STOP_EVENT.set())

    if args.once:
        run_once(cfg, build_http_session(), build_storage(cfg), TelegramSender(cfg))
    else:
        run_forever(cfg)


if __name__ == "__main__":
    main()


# ===========================================================
# SQL لازم برای Supabase (در SQL Editor اجرا کنید)
# ===========================================================
"""
create table if not exists public.seen_listings (
    article_id bigint primary key,
    title      text        not null,
    url        text        not null,
    created_at timestamptz not null default now()
);

-- جدول از بیرون قابل دسترسی نباشد؛ فقط service/secret key (که RLS را دور می‌زند) به آن می‌رسد
alter table public.seen_listings enable row level security;
"""
