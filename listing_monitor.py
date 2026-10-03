# -*- coding: utf-8 -*-
"""
listing_monitor.py
---------------------------------------------------------
مانیتور خبرهای «لیست‌های جدید» صرافی SuperEx و ارسال آن‌ها به تلگرام.

جریان کار:
    ۱) صفحه‌ی New Listings مرکز پشتیبانی (Zendesk) را می‌خواند
       (اول HTML با BeautifulSoup، و اگر شکست خورد API عمومی Zendesk).
    ۲) شناسه‌ی عددی هر مقاله را با دیتابیس «دیده‌شده‌ها» مقایسه می‌کند.
    ۳) فقط مقاله‌های جدید را به ترتیب زمانی (قدیمی به جدید) به تلگرام می‌فرستد.
    ۴) هر N ثانیه تکرار می‌کند.

ضد تکرار:
    - ذخیره‌سازی اصلی Supabase است (روی Render دیسک موقت است و فایل محلی پاک می‌شود).
    - اگر SUPABASE_URL / SUPABASE_KEY تنظیم نشده باشد، به SQLite محلی برمی‌گردد.
    - در اولین اجرا (دیتابیس خالی) فقط «خط پایه» ثبت می‌شود و هیچ پیام قدیمی ارسال نمی‌شود.
    - یک خبر فقط بعد از ارسال موفق به تلگرام «دیده‌شده» ثبت می‌شود؛ پس خطای تلگرام
      باعث گم شدن خبر نمی‌شود و دوره‌ی بعد دوباره تلاش می‌شود.
    - اگر دیتابیس در دسترس نباشد، چیزی ارسال نمی‌شود (چون بدون دیتابیس تکراری‌ها
      قابل تشخیص نیستند).

اجرا:
    python listing_monitor.py              # اجرای دائمی
    python listing_monitor.py --once       # فقط یک بار چک کن و خارج شو
    python listing_monitor.py --dry-run    # فقط بخوان و پیش‌نمایش پیام را چاپ کن (بدون ارسال/ذخیره)

اجرا داخل پروسه‌ی main.py (اختیاری):
    from listing_monitor import start_in_background
    start_in_background()

متغیرهای محیطی:
    BOT_TOKEN                توکن ربات (همان که main.py استفاده می‌کند)
    LISTING_CHAT_ID          آیدی کانال/گروه مقصد (مثل -100123... یا @channel)
    LISTING_THREAD_ID        (اختیاری) آیدی تاپیک، برای سوپرگروه‌های Forum
    LISTING_CHECK_INTERVAL   فاصله‌ی چک به ثانیه (پیش‌فرض 600)
    LISTING_SOURCE_URL       (اختیاری) آدرس صفحه
    LISTING_MAX_PER_CYCLE    سقف پیام در هر دوره (پیش‌فرض 5)
    LISTING_PREVIEW          1 = پیش‌نمایش لینک روشن (پیش‌فرض 0)
    SUPABASE_URL, SUPABASE_KEY, SUPABASE_TABLE (پیش‌فرض seen_listings)
    LISTING_SQLITE_PATH      مسیر SQLite جایگزین (پیش‌فرض listing_seen.sqlite3)
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
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

logger = logging.getLogger("listing_monitor")

DEFAULT_SOURCE_URL = "https://support.superex.com/hc/en-001/sections/4412788340249-New-Listings"
FOOTER_CHANNEL = "https://t.me/SuperExNews_Iran"
FOOTER_GROUP = "https://t.me/SuperexIR"

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
@dataclass(frozen=True)
class Config:
    bot_token: str
    chat_id: str
    thread_id: Optional[int]
    source_url: str
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
        thread = os.getenv("LISTING_THREAD_ID", "").strip()
        return cls(
            bot_token=os.getenv("BOT_TOKEN", "").strip(),
            chat_id=os.getenv("LISTING_CHAT_ID", "").strip(),
            thread_id=int(thread) if thread.isdigit() else None,
            source_url=os.getenv("LISTING_SOURCE_URL", DEFAULT_SOURCE_URL).strip(),
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
        if need_telegram and not self.chat_id:
            missing.append("LISTING_CHAT_ID")
        if missing:
            raise SystemExit(f"متغیرهای محیطی لازم تنظیم نشده‌اند: {', '.join(missing)}")


@dataclass(frozen=True)
class Listing:
    article_id: int
    title: str
    url: str


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


def parse_listings_html(html: str, base_url: str) -> List[Listing]:
    """
    لینک مقاله‌ها را از HTML صفحه‌ی بخش (Section) زندسک بیرون می‌کشد.
    به‌جای تکیه بر اسم کلاس‌های قالب، همه‌ی لینک‌های /articles/<id> را می‌گیرد؛
    شناسه‌ی عددی داخل URL کلید یکتای ماست (و با گذر زمان بزرگ‌تر می‌شود).
    خروجی به ترتیب نمایش در صفحه (جدیدترین اول) و بدون تکرار است.
    """
    soup = BeautifulSoup(html, "html.parser")
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
        full = urljoin(base_url, a["href"])
        clean_url = full.split("#")[0].split("?")[0]
        listings.append(Listing(article_id, title, clean_url))

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


def fetch_listings(session: requests.Session, source_url: str) -> List[Listing]:
    """اول HTML؛ اگر شکست خورد (مثلاً ۴۰۳ یا تغییر قالب) API زندسک."""
    html_error: Exception
    try:
        resp = session.get(source_url, timeout=HTTP_TIMEOUT)
        if resp.status_code != 200:
            raise FetchError(f"HTTP {resp.status_code}")
        return parse_listings_html(resp.text, source_url)
    except (requests.RequestException, FetchError, ParseError) as e:
        html_error = e
        logger.warning(f"خواندن HTML ناموفق ({type(e).__name__}: {e}) → تلاش با API")

    api_url = _zendesk_api_url(source_url)
    if not api_url:
        raise FetchError(f"HTML ناموفق بود و API قابل ساخت نیست: {html_error}")
    try:
        resp = session.get(api_url, timeout=HTTP_TIMEOUT)
        if resp.status_code != 200:
            raise FetchError(f"API HTTP {resp.status_code}")
        articles = resp.json().get("articles", [])
        listings = [Listing(int(a["id"]), str(a["title"]).strip(), str(a["html_url"]).split("?")[0])
                    for a in articles if a.get("id") and a.get("title") and a.get("html_url")]
        if not listings:
            raise ParseError("API هم مقاله‌ای برنگرداند")
        return listings
    except (requests.RequestException, ValueError, KeyError, FetchError, ParseError) as e:
        raise FetchError(f"HTML ({html_error}) و API ({type(e).__name__}: {e}) هر دو ناموفق بودند") from e


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
    """دسته‌بندی را از روی کلمات کلیدی عنوان تشخیص می‌دهد."""
    t = title.lower()
    cats = []
    if "spot" in t:
        cats.append("🟢 اسپات (Spot)")
    if "perpetual" in t:
        cats.append("🔵 فیوچرز دائمی (USDT-M)")
    if "index futures" in t:
        cats.append("🟣 مارجین فیوچرز شاخص")
    return " + ".join(cats) if cats else "🆕 لیست جدید"


def detect_symbols(title: str) -> List[str]:
    """نمادها را پیدا می‌کند: (MHA) داخل پرانتز، یا جفت‌های مثل CYPHUSDT."""
    found: List[str] = []
    for s in re.findall(r"\(([A-Z0-9.\-]{2,12})\)", title) + re.findall(r"\b([A-Z0-9]{2,12}USDT)\b", title):
        if s not in found:
            found.append(s)
    return found[:6]


def format_message(listing: Listing, html_mode: bool = True) -> str:
    """
    متن پیام. حالت پیش‌فرض HTML است (کم‌باگ‌تر از Markdown چون فقط < > & باید فرار داده شوند
    و html.escape این کار را انجام می‌دهد). حالت html_mode=False متن ساده برای حالت اضطراری است.
    """
    esc = html.escape if html_mode else (lambda s: s)
    b = (lambda s: f"<b>{s}</b>") if html_mode else (lambda s: s)
    code = (lambda s: f"<code>{esc(s)}</code>") if html_mode else (lambda s: s)

    lines = [
        f"🆕 {b('لیست جدید در صرافی SuperEx')} 🆕",
        "━━━━━━━━━━━━━━━━━━",
        "",
        f"📌 {b('عنوان خبر:')}",
        esc(listing.title),
        "",
        f"🏷 {b('دسته‌بندی:')} {detect_categories(listing.title)}",
    ]
    symbols = detect_symbols(listing.title)
    if symbols:
        lines.append(f"🪙 {b('نماد:')} " + "، ".join(code(s) for s in symbols))
    lines.append("")
    if html_mode:
        lines.append(f"🔗 <a href=\"{html.escape(listing.url, quote=True)}\">مشاهده‌ی جزئیات خبر</a>")
    else:
        lines.append(f"🔗 مشاهده‌ی جزئیات خبر:\n{listing.url}")
    lines += ["", "━━━━━━━━━━━━━━━━━━"]
    if html_mode:
        lines.append(f"📢 <a href=\"{FOOTER_CHANNEL}\">کانال رسمی</a> | 👥 <a href=\"{FOOTER_GROUP}\">گروه گفتگو</a>")
    else:
        lines.append(f"📢 {FOOTER_CHANNEL}\n👥 {FOOTER_GROUP}")
    return "\n".join(lines)


# ===========================================================
# بخش ۴: ارسال به تلگرام
# ===========================================================
class TelegramSender:
    MAX_ATTEMPTS = 4

    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.url = f"https://api.telegram.org/bot{cfg.bot_token}/sendMessage"
        self.session = requests.Session()

    def _safe(self, text: str) -> str:
        """توکن ربات هرگز در لاگ نیاید."""
        return str(text).replace(self.cfg.bot_token, "***")

    def send(self, listing: Listing) -> None:
        payload = {
            "chat_id": self.cfg.chat_id,
            "text": format_message(listing, html_mode=True),
            "parse_mode": "HTML",
            "disable_web_page_preview": not self.cfg.preview,
        }
        if self.cfg.thread_id:
            payload["message_thread_id"] = self.cfg.thread_id

        for attempt in range(1, self.MAX_ATTEMPTS + 1):
            try:
                resp = self.session.post(self.url, json=payload, timeout=HTTP_TIMEOUT)
            except requests.RequestException as e:
                logger.warning(f"خطای شبکه‌ی تلگرام (تلاش {attempt}): {self._safe(e)}")
                if STOP_EVENT.wait(2 ** attempt):
                    return
                continue

            if resp.status_code == 200:
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
            if resp.status_code == 400 and "parse entities" in desc.lower() and "parse_mode" in payload:
                logger.warning("خطای HTML؛ ارسال مجدد به‌صورت متن ساده")
                payload.pop("parse_mode")
                payload["text"] = format_message(listing, html_mode=False)
                continue
            if resp.status_code >= 500:
                STOP_EVENT.wait(2 ** attempt)
                continue
            raise TelegramError(f"HTTP {resp.status_code}: {self._safe(desc)}")

        raise TelegramError("ارسال بعد از چند تلاش ناموفق ماند")


# ===========================================================
# بخش ۵: یک دوره‌ی بررسی + حلقه‌ی اصلی
# ===========================================================
def run_once(cfg: Config, http: requests.Session, storage: Storage, sender: TelegramSender) -> int:
    """یک دوره‌ی کامل را اجرا می‌کند و تعداد پیام‌های ارسال‌شده را برمی‌گرداند."""
    listings = fetch_listings(http, cfg.source_url)
    ids = [l.article_id for l in listings]

    # اجرای اول: فقط خط پایه را ثبت کن تا تاریخچه‌ی سایت اسپم نشود
    if storage.is_empty():
        storage.mark_seen(listings)
        logger.info(f"اولین اجرا: {len(listings)} خبر موجود به‌عنوان خط پایه ثبت شد (چیزی ارسال نشد)")
        return 0

    seen = storage.get_seen(ids)
    new = sorted((l for l in listings if l.article_id not in seen), key=lambda l: l.article_id)
    if not new:
        logger.info("خبر جدیدی نیست")
        return 0

    # محافظ ضد اسپم: اگر ناگهان خیلی زیاد «جدید» دیدیم (مثلاً دیتابیس ریست شده)
    if len(new) > cfg.max_per_cycle:
        skipped, new = new[:-cfg.max_per_cycle], new[-cfg.max_per_cycle:]
        logger.warning(f"{len(skipped) + len(new)} خبر جدید دیده شد؛ فقط {len(new)} تای آخر ارسال می‌شود")
        storage.mark_seen(skipped)

    sent = 0
    for listing in new:                       # قدیمی → جدید
        try:
            sender.send(listing)
        except TelegramError as e:
            logger.error(f"ارسال «{listing.title[:60]}» ناموفق: {e} — دوره‌ی بعد دوباره تلاش می‌شود")
            break                             # ترتیب خبرها به‌هم نریزد
        storage.mark_seen([listing])          # فقط بعد از ارسال موفق
        sent += 1
        STOP_EVENT.wait(1.5)                  # فاصله‌ی کوتاه بین پیام‌ها
    logger.info(f"{sent} پیام ارسال شد")
    return sent


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
        except (FetchError, ParseError) as e:
            logger.warning(f"دریافت خبرها ناموفق: {e}")
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
    listings = fetch_listings(build_http_session(), cfg.source_url)
    print(f"{len(listings)} خبر پیدا شد. ۳ مورد اول:")
    for l in listings[:3]:
        print(f"  [{l.article_id}] {l.title}\n      {l.url}")
    print("\n--- پیش‌نمایش پیام برای جدیدترین خبر ---\n")
    print(format_message(max(listings, key=lambda l: l.article_id), html_mode=False))


def main() -> None:
    parser = argparse.ArgumentParser(description="مانیتور لیست‌های جدید SuperEx")
    parser.add_argument("--once", action="store_true", help="فقط یک بار چک کن")
    parser.add_argument("--dry-run", action="store_true", help="فقط بخوان و پیش‌نمایش بده")
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
    cfg = Config.from_env()

    if args.dry_run:
        _dry_run(cfg)
        return

    cfg.validate()
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
