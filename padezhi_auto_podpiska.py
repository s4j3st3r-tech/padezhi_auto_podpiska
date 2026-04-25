import asyncio
import difflib
import html
import json
import logging
import sqlite3
import sys
import tempfile
from collections import deque
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
import re
from typing import Any, Dict, List, Optional, Set, Tuple

import pymorphy2
from telegram import (
    Bot,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputMediaDocument,
    InputMediaPhoto,
    InputMediaVideo,
    error,
)
from telegram.request import HTTPXRequest
from telethon import TelegramClient, events
from telethon.errors.rpcerrorlist import (
    FloodWaitError,
    InviteHashExpiredError,
    InviteHashInvalidError,
    SessionPasswordNeededError,
    UserAlreadyParticipantError,
)
from telethon.tl.functions.channels import JoinChannelRequest
from telethon.tl.functions.messages import ImportChatInviteRequest
from telethon.utils import get_peer_id


def app_path() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


BASE_DIR = app_path()
DATA_DIR = BASE_DIR / "data"
CONFIG_PATH = BASE_DIR / "config_telegram.json"
KEYWORDS_JSON_PATH = BASE_DIR / "keywords.json"
CHANNELS_JSON_PATH = BASE_DIR / "channels.json"
DB_PATH = BASE_DIR / "padezhi_auto_podpiska.sqlite3"
ERROR_LOG_PATH = BASE_DIR / "errors.log"

RATE_LIMIT_DELAY = 0.8
SEND_DELAY = 0.4
POLL_INTERVAL = 20
POLL_LIMIT_PER_CHANNEL = 5
PROCESSED_MAX_ITEMS = 5000
BOT_CONTROL_INTERVAL = 1.2
ALBUM_WAIT_SECONDS = 1.5
BOT_CONNECT_TIMEOUT = 30
BOT_POOL_TIMEOUT = 60
BOT_MEDIA_TIMEOUT = 300
BOT_CONNECTION_POOL_SIZE = 32
MEDIA_CAPTION_LIMIT = 1000

word_re = re.compile(r"\w+", flags=re.UNICODE)


logging.basicConfig(level=logging.INFO, format="%(levelname)s:%(name)s:%(message)s")
log = logging.getLogger("forwarder")
error_handler = logging.FileHandler(ERROR_LOG_PATH, encoding="utf-8")
error_handler.setLevel(logging.ERROR)
error_handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s:%(name)s:%(message)s"))
logging.getLogger().addHandler(error_handler)
logging.getLogger("telethon.client.updates").setLevel(logging.WARNING)
logging.getLogger("telethon.client.users").setLevel(logging.WARNING)


@dataclass
class AppConfig:
    api_id: int
    api_hash: str
    phone_number: str
    bot_token: str
    channel_chat_id: str
    admin_chat_ids: Set[int]


def load_json(path: Path, default: Any = None) -> Any:
    if not path.exists():
        if default is not None:
            return default
        raise FileNotFoundError(f"Не найден файл: {path}")
    try:
        with path.open("r", encoding="utf-8-sig") as f:
            return json.load(f)
    except json.JSONDecodeError as exc:
        raise ValueError(f"Файл {path.name} содержит ошибку JSON: {exc}") from exc


def load_config() -> AppConfig:
    raw = load_json(CONFIG_PATH)
    required = ("api_id", "api_hash", "phone_number", "bot_token", "channel_chat_id")
    missing = [name for name in required if raw.get(name) in (None, "")]
    if missing:
        raise ValueError("Заполните поля в config_telegram.json: " + ", ".join(missing))

    admins = raw.get("admin_chat_ids") or []
    return AppConfig(
        api_id=int(raw["api_id"]),
        api_hash=str(raw["api_hash"]),
        phone_number=str(raw["phone_number"]),
        bot_token=str(raw["bot_token"]),
        channel_chat_id=str(raw["channel_chat_id"]),
        admin_chat_ids={int(x) for x in admins},
    )


CONFIG = load_config()
morph = pymorphy2.MorphAnalyzer(path=str(DATA_DIR))
client = TelegramClient(str(BASE_DIR / "session_name"), CONFIG.api_id, CONFIG.api_hash)
bot_request = HTTPXRequest(
    connection_pool_size=BOT_CONNECTION_POOL_SIZE,
    connect_timeout=BOT_CONNECT_TIMEOUT,
    read_timeout=BOT_MEDIA_TIMEOUT,
    write_timeout=BOT_MEDIA_TIMEOUT,
    pool_timeout=BOT_POOL_TIMEOUT,
)
bot = Bot(token=CONFIG.bot_token, request=bot_request)

RESOLVE_CACHE: Dict[str, Any] = {}
PROCESSED = deque(maxlen=PROCESSED_MAX_ITEMS)
PROCESSED_LOOKUP: Set[Tuple[int, int]] = set()
PROCESSED_ALBUMS: Set[Tuple[int, int]] = set()
CHANNEL_ENTITIES: Dict[str, dict] = {}
ALLOWED_IDS: Set[int] = set()
ALLOWED_USERNAMES: Set[str] = set()
ALLOWED_ID_STRINGS: Set[str] = set()
ADMIN_MODES: Dict[int, str] = {}
ADMIN_SCREEN_MESSAGES: Dict[int, int] = {}
BOT_UPDATE_OFFSET = 0
BOT_SEND_LOCK = asyncio.Lock()

KEYWORDS: List[str] = []
CHANNELS: List[dict] = []
SINGLE_WORD_LEMMAS: Set[str] = set()
PHRASES_LC: List[str] = []


def db_connect() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def init_db() -> None:
    with db_connect() as conn:
        conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS keywords (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                text TEXT NOT NULL UNIQUE COLLATE NOCASE,
                created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
            );
            CREATE TABLE IF NOT EXISTS channels (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                link TEXT,
                channel_id INTEGER,
                name TEXT,
                custom_text TEXT,
                created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
            );
            CREATE TABLE IF NOT EXISTS state (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL,
                updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
            );
            """
        )


def table_is_empty(table: str) -> bool:
    with db_connect() as conn:
        return conn.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0] == 0


def migrate_json_to_db() -> None:
    if table_is_empty("keywords"):
        for keyword in load_json(KEYWORDS_JSON_PATH, []):
            text = str(keyword or "").strip()
            if text:
                add_keyword_db(text)

    if table_is_empty("channels"):
        for channel in load_json(CHANNELS_JSON_PATH, []):
            add_channel_db(channel)


def load_keywords_from_db() -> List[str]:
    with db_connect() as conn:
        rows = conn.execute("SELECT text FROM keywords ORDER BY id").fetchall()
    return [row["text"] for row in rows]


def load_channels_from_db() -> List[dict]:
    with db_connect() as conn:
        rows = conn.execute(
            "SELECT link, channel_id, name, custom_text FROM channels ORDER BY id"
        ).fetchall()

    channels = []
    for row in rows:
        channel = {}
        if row["channel_id"] is not None:
            channel["id"] = int(row["channel_id"])
        if row["link"]:
            channel["link"] = row["link"]
        if row["name"]:
            channel["name"] = row["name"]
        if row["custom_text"]:
            channel["custom_text"] = row["custom_text"]
        channels.append(channel)
    return channels


def refresh_memory_from_db() -> None:
    global KEYWORDS, CHANNELS
    KEYWORDS = load_keywords_from_db()
    CHANNELS = load_channels_from_db()
    rebuild_keyword_index()


def resolve_list_number(value: str, total: int) -> Optional[int]:
    value = value.strip()
    if value.isdigit():
        index = int(value) - 1
        if 0 <= index < total:
            return index
    return None


def resolve_keyword_reference(reference: str) -> Optional[str]:
    index = resolve_list_number(reference, len(KEYWORDS))
    if index is not None:
        return KEYWORDS[index]
    return None


def resolve_channel_reference(reference: str) -> Optional[str]:
    index = resolve_list_number(reference, len(CHANNELS))
    if index is None:
        return None
    channel = CHANNELS[index]
    return str(channel.get("link") or channel.get("id") or "")


def add_keyword_db(text: str) -> bool:
    text = text.strip()
    if not text:
        return False
    with db_connect() as conn:
        cur = conn.execute("INSERT OR IGNORE INTO keywords(text) VALUES (?)", (text,))
        return cur.rowcount > 0


def delete_keyword_db(text: str) -> bool:
    text = resolve_keyword_reference(text) or text
    with db_connect() as conn:
        cur = conn.execute("DELETE FROM keywords WHERE lower(text) = lower(?)", (text.strip(),))
        return cur.rowcount > 0


def rename_keyword_db(old: str, new: str) -> bool:
    old = resolve_keyword_reference(old) or old
    old = old.strip()
    new = new.strip()
    if not old or not new:
        return False
    with db_connect() as conn:
        cur = conn.execute("UPDATE keywords SET text = ? WHERE lower(text) = lower(?)", (new, old))
        return cur.rowcount > 0


def add_channel_db(channel: dict) -> bool:
    link = channel.get("link")
    channel_id = channel.get("id")
    if link and find_channel_index(str(link)) is not None:
        return False
    if channel_id is not None and find_channel_index(str(channel_id)) is not None:
        return False
    with db_connect() as conn:
        conn.execute(
            """
            INSERT INTO channels(link, channel_id, name, custom_text)
            VALUES (?, ?, ?, ?)
            """,
            (
                str(link) if link else None,
                int(channel_id) if channel_id is not None else None,
                channel.get("name"),
                channel.get("custom_text"),
            ),
        )
    return True


def delete_channel_db(reference: str) -> Optional[dict]:
    reference = resolve_channel_reference(reference) or reference
    index = find_channel_index(reference)
    if index is None:
        return None
    channel = CHANNELS[index]
    link = channel.get("link")
    channel_id = channel.get("id")
    with db_connect() as conn:
        if channel_id is not None:
            conn.execute("DELETE FROM channels WHERE channel_id = ?", (int(channel_id),))
        else:
            conn.execute("DELETE FROM channels WHERE lower(link) = lower(?)", (str(link),))
    return channel


def set_channel_label_db(reference: str, label: str) -> bool:
    reference = resolve_channel_reference(reference) or reference
    index = find_channel_index(reference)
    if index is None:
        return False
    channel = CHANNELS[index]
    with db_connect() as conn:
        if channel.get("id") is not None:
            cur = conn.execute(
                "UPDATE channels SET custom_text = ? WHERE channel_id = ?",
                (label.strip(), int(channel["id"])),
            )
        else:
            cur = conn.execute(
                "UPDATE channels SET custom_text = ? WHERE lower(link) = lower(?)",
                (label.strip(), str(channel.get("link"))),
            )
    return cur.rowcount > 0


def get_state(key: str, default: str = "0") -> str:
    with db_connect() as conn:
        row = conn.execute("SELECT value FROM state WHERE key = ?", (key,)).fetchone()
    return row["value"] if row else default


def set_state(key: str, value: Any) -> None:
    with db_connect() as conn:
        conn.execute(
            """
            INSERT INTO state(key, value, updated_at) VALUES (?, ?, CURRENT_TIMESTAMP)
            ON CONFLICT(key) DO UPDATE SET value = excluded.value, updated_at = CURRENT_TIMESTAMP
            """,
            (key, str(value)),
        )


def last_seen_key(chat_id: int) -> str:
    return f"last_seen:{chat_id}"


def get_last_seen(chat_id: int) -> int:
    return int(get_state(last_seen_key(chat_id), "0"))


def set_last_seen(chat_id: int, message_id: int) -> None:
    set_state(last_seen_key(chat_id), message_id)


def is_admin(chat_id: int) -> bool:
    if CONFIG.admin_chat_ids:
        return chat_id in CONFIG.admin_chat_ids
    return str(chat_id) == str(CONFIG.channel_chat_id)


def remember_processed(key: Tuple[int, int]) -> bool:
    if key in PROCESSED_LOOKUP:
        return False
    if len(PROCESSED) == PROCESSED.maxlen and PROCESSED:
        PROCESSED_LOOKUP.discard(PROCESSED[0])
    PROCESSED.append(key)
    PROCESSED_LOOKUP.add(key)
    return True


def lemma(text: str) -> str:
    return morph.parse(text)[0].normal_form


def rebuild_keyword_index() -> None:
    SINGLE_WORD_LEMMAS.clear()
    PHRASES_LC.clear()
    seen = set()
    for keyword in KEYWORDS:
        text = str(keyword or "").strip()
        if not text:
            continue
        key = text.casefold()
        if key in seen:
            continue
        seen.add(key)
        parts = word_re.findall(text)
        if len(parts) <= 1:
            SINGLE_WORD_LEMMAS.add(lemma(text.lower()))
        else:
            PHRASES_LC.append(text.lower())


def add_keyword(keyword: str) -> bool:
    added = add_keyword_db(keyword)
    refresh_memory_from_db()
    return added


def delete_keyword(keyword: str) -> bool:
    deleted = delete_keyword_db(keyword)
    refresh_memory_from_db()
    return deleted


def rename_keyword(old: str, new: str) -> bool:
    renamed = rename_keyword_db(old, new)
    refresh_memory_from_db()
    return renamed


def normalize_text(text: str) -> List[Tuple[str, str]]:
    words = word_re.findall(text.lower())
    return [(word, lemma(word)) for word in words]


def find_triggers(message_text: str) -> Tuple[List[str], List[str]]:
    text_lc = message_text.lower()
    phrase_hits = [phrase for phrase in PHRASES_LC if phrase in text_lc]
    word_hits = []
    for original, normalized in normalize_text(message_text):
        if normalized in SINGLE_WORD_LEMMAS:
            word_hits.append(original)

    seen = set()
    unique_words = []
    for word in word_hits:
        if word not in seen:
            seen.add(word)
            unique_words.append(word)
    return phrase_hits, unique_words


def should_forward(message_text: str) -> Tuple[bool, List[str]]:
    phrases, words = find_triggers(message_text)
    triggers = [*phrases, *words]
    return bool(triggers), triggers


def highlight_text(text: str, phrases: List[str], tokens: List[str]) -> str:
    escaped = html.escape(text)
    for item in [*phrases, *tokens]:
        if not item:
            continue
        escaped_item = html.escape(item)
        pattern = re.compile(re.escape(escaped_item), flags=re.IGNORECASE)
        escaped = pattern.sub(lambda match: f"<b>{match.group(0)}</b>", escaped)
    return escaped


def message_text(message: Any) -> str:
    return getattr(message, "text", None) or getattr(message, "message", None) or ""


def message_link_for(chat: Any, message_id: int) -> str:
    username = getattr(chat, "username", None)
    if username:
        return f"https://t.me/{username}/{message_id}"
    chat_id = str(getattr(chat, "id", ""))
    if chat_id.startswith("-100"):
        chat_id = chat_id[4:]
    else:
        chat_id = chat_id.lstrip("-")
    return f"https://t.me/c/{chat_id}/{message_id}"


def get_channel_custom_text(chat: Any) -> str:
    for key in (getattr(chat, "username", None), str(getattr(chat, "id", ""))):
        if key and key in CHANNEL_ENTITIES:
            return CHANNEL_ENTITIES[key].get("custom_text", "")
    return ""


def format_forward_text(chat: Any, message: Any, triggers: List[str], source_text: str) -> str:
    phrases, words = find_triggers(source_text)
    highlighted = highlight_text(source_text, phrases, words)
    message_link = message_link_for(chat, message.id)
    title = html.escape(getattr(chat, "title", "Источник"))
    custom_text = html.escape(get_channel_custom_text(chat))
    header = (
        f'Найден пост в {custom_text} <a href="{message_link}">{title}</a>'
        if custom_text
        else f'Найден пост в <a href="{message_link}">{title}</a>'
    )
    tail = ""
    if triggers:
        safe_triggers = [html.escape(item) for item in sorted(set(triggers))]
        tail = "\n\nКлючевые слова: " + ", ".join(safe_triggers)
    return f"{header}:\n\n{highlighted}{tail}"


async def resolve_username_once(username: str):
    if not username:
        raise ValueError("empty username")
    if username in RESOLVE_CACHE:
        return RESOLVE_CACHE[username]
    await asyncio.sleep(RATE_LIMIT_DELAY)
    entity = await client.get_input_entity(username)
    RESOLVE_CACHE[username] = entity
    return entity


async def resolve_link_once(link: str):
    if not link:
        raise ValueError("empty link")
    if link in RESOLVE_CACHE:
        return RESOLVE_CACHE[link]
    await asyncio.sleep(RATE_LIMIT_DELAY)
    entity = await client.get_entity(link)
    RESOLVE_CACHE[link] = entity
    return entity


async def get_channel_entity(channel: dict):
    if "id" in channel:
        return await client.get_input_entity(channel["id"])
    link = channel.get("link", "")
    if "joinchat" in link or "t.me/+" in link:
        return await resolve_link_once(link)
    username = link.rsplit("/", 1)[-1].lstrip("@")
    return await resolve_username_once(username)


async def join_channel(channel: dict) -> bool:
    try:
        if "id" in channel:
            entity = await client.get_input_entity(channel["id"])
            await client(JoinChannelRequest(entity))
            return True

        link = channel.get("link", "")
        if "joinchat" in link or "t.me/+" in link:
            invite_hash = link.split("/")[-1].replace("+", "")
            await client(ImportChatInviteRequest(invite_hash))
            return True

        entity = await get_channel_entity(channel)
        await client(JoinChannelRequest(entity))
        return True
    except UserAlreadyParticipantError:
        return True
    except FloodWaitError as exc:
        log.warning("FloodWait %ss для канала %s", exc.seconds, channel)
        await asyncio.sleep(exc.seconds)
        return await join_channel(channel)
    except (InviteHashExpiredError, InviteHashInvalidError) as exc:
        log.error("Проблема с invite-ссылкой %s: %s", channel, exc)
        return False
    except Exception as exc:
        log.error("Не удалось подключить канал %s: %s", channel, exc)
        return False


async def check_channel_access(reference: str) -> str:
    try:
        channel = parse_channel_input(reference)
        entity = await get_channel_entity(channel)
        peer_id = get_peer_id(entity)
        title = html.escape(getattr(entity, "title", getattr(entity, "username", "канал")))
        latest_id = 0
        async for message in client.iter_messages(entity, limit=1):
            latest_id = message.id
            break
        return f"Канал доступен: {title}\nID: {peer_id}\nПоследний пост: {latest_id or 'нет'}"
    except Exception as exc:
        log.error("Проверка канала не прошла для %s: %s", reference, exc)
        return f"Канал недоступен: {html.escape(str(exc))}"


async def safe_send_text(text: str, chat_id: Optional[int] = None, reply_markup=None) -> None:
    target = chat_id if chat_id is not None else CONFIG.channel_chat_id
    for attempt in range(3):
        try:
            await asyncio.sleep(SEND_DELAY)
            async with BOT_SEND_LOCK:
                return await bot.send_message(
                    chat_id=target,
                    text=text[:4096],
                    parse_mode="HTML",
                    disable_web_page_preview=True,
                    reply_markup=reply_markup,
                    connect_timeout=BOT_CONNECT_TIMEOUT,
                    read_timeout=BOT_MEDIA_TIMEOUT,
                    write_timeout=BOT_MEDIA_TIMEOUT,
                    pool_timeout=BOT_POOL_TIMEOUT,
                )
        except (error.TimedOut, asyncio.TimeoutError):
            await asyncio.sleep(2**attempt)
        except Exception as exc:
            log.error("Ошибка отправки сообщения: %s", exc)
            return


def media_kind_for(message: Any) -> Optional[str]:
    if getattr(message, "photo", None):
        return "photo"
    document = getattr(message, "document", None)
    if not document:
        return None
    mime_type = getattr(document, "mime_type", "") or ""
    if mime_type.startswith("video/"):
        return "video"
    return "document"


def compact_media_caption(text: str, fallback_title: str) -> str:
    if len(text) <= MEDIA_CAPTION_LIMIT:
        return text

    plain = re.sub(r"<[^>]+>", "", text)
    plain = html.unescape(plain)
    prefix = f"{fallback_title}\nПодпись сокращена из-за лимита Telegram.\n\n"
    available = MEDIA_CAPTION_LIMIT - len(prefix) - 3
    if available < 100:
        return html.escape(fallback_title[:MEDIA_CAPTION_LIMIT])
    return html.escape(prefix + plain[:available].rstrip() + "...")


def media_timeout_kwargs() -> dict:
    return {
        "connect_timeout": BOT_CONNECT_TIMEOUT,
        "read_timeout": BOT_MEDIA_TIMEOUT,
        "write_timeout": BOT_MEDIA_TIMEOUT,
        "pool_timeout": BOT_POOL_TIMEOUT,
    }


async def safe_send_media(text: str, media_path: Path, media_kind: str) -> None:
    caption = text if len(text) <= 1000 else "Найден пост с медиа. Текст отправлен отдельным сообщением."
    try:
        with media_path.open("rb") as media:
            if media_kind == "photo":
                await bot.send_photo(CONFIG.channel_chat_id, media, caption=caption, parse_mode="HTML")
            elif media_kind == "video":
                await bot.send_video(CONFIG.channel_chat_id, media, caption=caption, parse_mode="HTML")
            else:
                await bot.send_document(CONFIG.channel_chat_id, media, caption=caption, parse_mode="HTML")
        if len(text) > 1000:
            await safe_send_text(text)
    except Exception as exc:
        log.error("Ошибка отправки медиа: %s", exc)
        await safe_send_text(text)


async def safe_send_media(text: str, media_path: Path, media_kind: str) -> None:
    caption = compact_media_caption(text, "Найден пост с медиа.")
    for attempt in range(3):
        try:
            with media_path.open("rb") as media:
                async with BOT_SEND_LOCK:
                    if media_kind == "photo":
                        await bot.send_photo(
                            CONFIG.channel_chat_id,
                            media,
                            caption=caption,
                            parse_mode="HTML",
                            **media_timeout_kwargs(),
                        )
                    elif media_kind == "video":
                        await bot.send_video(
                            CONFIG.channel_chat_id,
                            media,
                            caption=caption,
                            parse_mode="HTML",
                            supports_streaming=True,
                            **media_timeout_kwargs(),
                        )
                    else:
                        await bot.send_document(
                            CONFIG.channel_chat_id,
                            media,
                            caption=caption,
                            parse_mode="HTML",
                            **media_timeout_kwargs(),
                        )
            return
        except (error.TimedOut, asyncio.TimeoutError, error.NetworkError) as exc:
            log.warning("Повтор отправки медиа %s/3 после таймаута: %s", attempt + 1, exc)
            await asyncio.sleep(2 ** attempt)
        except Exception as exc:
            log.error("Ошибка отправки медиа: %s", exc)
            break
    await safe_send_text(text)


async def send_album_to_target(text: str, messages: List[Any]) -> None:
    media_messages = [message for message in messages if media_kind_for(message)]
    if not media_messages:
        await safe_send_text(text)
        return

    caption = text if len(text) <= 1000 else "Найден альбом. Текст отправлен отдельным сообщением."
    try:
        with tempfile.TemporaryDirectory() as temp_dir:
            paths = []
            for message in media_messages[:10]:
                downloaded = await client.download_media(message, file=temp_dir)
                if downloaded:
                    paths.append((Path(downloaded), media_kind_for(message)))

            if not paths:
                await safe_send_text(text)
                return

            if len(paths) == 1:
                await safe_send_media(text, paths[0][0], paths[0][1] or "document")
                return

            handles = []
            media_group = []
            try:
                for index, (path, kind) in enumerate(paths):
                    handle = path.open("rb")
                    handles.append(handle)
                    media_caption = caption if index == 0 else None
                    if kind == "photo":
                        media_group.append(InputMediaPhoto(handle, caption=media_caption, parse_mode="HTML"))
                    elif kind == "video":
                        media_group.append(InputMediaVideo(handle, caption=media_caption, parse_mode="HTML"))
                    else:
                        media_group.append(InputMediaDocument(handle, caption=media_caption, parse_mode="HTML"))

                await bot.send_media_group(CONFIG.channel_chat_id, media_group)
                if len(text) > 1000:
                    await safe_send_text(text)
            finally:
                for handle in handles:
                    handle.close()
    except Exception as exc:
        log.error("Ошибка отправки альбома: %s", exc)
        await safe_send_text(text)


async def send_album_to_target(text: str, messages: List[Any]) -> None:
    media_messages = [message for message in messages if media_kind_for(message)]
    if not media_messages:
        await safe_send_text(text)
        return

    caption = compact_media_caption(text, "Найден альбом.")
    try:
        with tempfile.TemporaryDirectory() as temp_dir:
            paths = []
            for message in media_messages[:10]:
                downloaded = await client.download_media(message, file=temp_dir)
                if downloaded:
                    paths.append((Path(downloaded), media_kind_for(message)))

            if not paths:
                await safe_send_text(text)
                return

            if len(paths) == 1:
                await safe_send_media(text, paths[0][0], paths[0][1] or "document")
                return

            for attempt in range(3):
                handles = []
                media_group = []
                try:
                    for index, (path, kind) in enumerate(paths):
                        handle = path.open("rb")
                        handles.append(handle)
                        media_caption = caption if index == 0 else None
                        if kind == "photo":
                            media_group.append(InputMediaPhoto(handle, caption=media_caption, parse_mode="HTML"))
                        elif kind == "video":
                            media_group.append(InputMediaVideo(handle, caption=media_caption, parse_mode="HTML"))
                        else:
                            media_group.append(InputMediaDocument(handle, caption=media_caption, parse_mode="HTML"))

                    async with BOT_SEND_LOCK:
                        await bot.send_media_group(CONFIG.channel_chat_id, media_group, **media_timeout_kwargs())
                    return
                except (error.TimedOut, asyncio.TimeoutError, error.NetworkError) as exc:
                    log.warning("Повтор отправки альбома %s/3 после таймаута: %s", attempt + 1, exc)
                    await asyncio.sleep(2 ** attempt)
                finally:
                    for handle in handles:
                        handle.close()
            await safe_send_text(text)
    except Exception as exc:
        log.error("Ошибка отправки альбома: %s", exc)
        await safe_send_text(text)


async def forward_to_target(chat: Any, message: Any, text: str, album_messages: Optional[List[Any]] = None) -> None:
    if album_messages:
        await send_album_to_target(text, album_messages)
        return

    kind = media_kind_for(message)
    if not kind:
        await safe_send_text(text)
        return

    try:
        with tempfile.TemporaryDirectory() as temp_dir:
            downloaded = await client.download_media(message, file=temp_dir)
            if downloaded:
                await safe_send_media(text, Path(downloaded), kind)
            else:
                await safe_send_text(text)
    except Exception as exc:
        log.error("Не удалось переслать медиа: %s", exc)
        await safe_send_text(text)


async def collect_album_messages(entity: Any, grouped_id: int) -> List[Any]:
    await asyncio.sleep(ALBUM_WAIT_SECONDS)
    messages = []
    async for item in client.iter_messages(entity, limit=20):
        if getattr(item, "grouped_id", None) == grouped_id:
            messages.append(item)
    return sorted(messages, key=lambda item: item.id)


async def process_and_maybe_forward(chat: Any, message: Any, entity: Any = None) -> None:
    if not message:
        return

    grouped_id = getattr(message, "grouped_id", None)
    if grouped_id:
        album_key = (message.chat_id, int(grouped_id))
        if album_key in PROCESSED_ALBUMS:
            return
        PROCESSED_ALBUMS.add(album_key)
        album_messages = await collect_album_messages(entity or chat, grouped_id)
        for album_message in album_messages:
            remember_processed((album_message.chat_id, album_message.id))
        source_text = "\n\n".join(message_text(item) for item in album_messages if message_text(item)).strip()
    else:
        if not remember_processed((message.chat_id, message.id)):
            return
        album_messages = None
        source_text = message_text(message).strip()

    if not source_text:
        return

    should, triggers = should_forward(source_text)
    log.info("Найдено ключей: %s", triggers)
    if not should:
        return

    text = format_forward_text(chat, message, triggers, source_text)
    await forward_to_target(chat, message, text, album_messages)


async def keep_updates_alive() -> None:
    while True:
        try:
            await client.get_dialogs(limit=0)
        except Exception as exc:
            log.warning("keepalive/get_dialogs: %s", exc)
        await asyncio.sleep(20)


async def polling_loop() -> None:
    while True:
        try:
            for info in CHANNEL_ENTITIES.values():
                entity = info["entity"]
                chat_id = get_peer_id(entity)
                last_id = get_last_seen(chat_id)
                new_messages = []
                async for message in client.iter_messages(entity, limit=POLL_LIMIT_PER_CHANNEL):
                    if last_id and message.id <= last_id:
                        break
                    new_messages.append(message)

                for message in reversed(new_messages):
                    chat = await message.get_chat()
                    await process_and_maybe_forward(chat, message, entity)
                    set_last_seen(chat_id, max(get_last_seen(chat_id), message.id))
                    await asyncio.sleep(0.1)

                await asyncio.sleep(0.1)
        except Exception as exc:
            log.error("polling_loop: %s", exc)
        await asyncio.sleep(POLL_INTERVAL)


def admin_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("Ключ +", callback_data="kw:add"),
                InlineKeyboardButton("Ключ -", callback_data="kw:delete"),
            ],
            [
                InlineKeyboardButton("Ключ изменить", callback_data="kw:rename"),
                InlineKeyboardButton("Ключ найти", callback_data="kw:search"),
            ],
            [
                InlineKeyboardButton("Каналы список", callback_data="ch:list"),
                InlineKeyboardButton("Канал +", callback_data="ch:add"),
            ],
            [
                InlineKeyboardButton("Канал -", callback_data="ch:delete"),
                InlineKeyboardButton("Канал проверить", callback_data="ch:check"),
            ],
            [
                InlineKeyboardButton("Канал метка", callback_data="ch:label"),
                InlineKeyboardButton("Канал найти", callback_data="ch:search"),
            ],
            [
                InlineKeyboardButton("Статус", callback_data="kw:stats"),
                InlineKeyboardButton("Ошибки", callback_data="errors:last"),
            ],
            [
                InlineKeyboardButton("Перезагрузить", callback_data="all:reload"),
            ],
        ]
    )


def back_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("Назад", callback_data="menu:back")]])


async def send_admin_menu(chat_id: int) -> None:
    await safe_send_text(
        "Панель управления.\n\n"
        "Ключи: /add, /del, /rename, /search, /list\n"
        "Каналы: /ch_add, /ch_del, /ch_label, /ch_check, /ch_list\n"
        "Диагностика: /stats, /errors",
        chat_id=chat_id,
        reply_markup=admin_keyboard(),
    )


async def answer_callback(callback: Any, text: str = "Готово") -> None:
    try:
        await bot.answer_callback_query(callback_query_id=callback.id, text=text)
    except Exception:
        pass


async def send_keyword_list(chat_id: int) -> None:
    lines = [f"{index + 1}. {html.escape(value)}" for index, value in enumerate(KEYWORDS)]
    await send_long_text(chat_id, "Ключевые слова:\n\n" + "\n".join(lines))


async def send_long_text(chat_id: int, text: str) -> None:
    for start in range(0, max(len(text), 1), 3500):
        await safe_send_text(text[start : start + 3500] or "Пусто.", chat_id)


async def send_keyword_search(chat_id: int, query: str) -> None:
    query_cf = query.strip().casefold()
    matches = [item for item in KEYWORDS if query_cf in item.casefold()] if query_cf else []
    if not matches:
        await safe_send_text("Ничего не нашёл.", chat_id)
        return
    lines = [f"{index + 1}. {html.escape(value)}" for index, value in enumerate(matches[:50])]
    await safe_send_text("Нашёл:\n\n" + "\n".join(lines), chat_id)


async def send_stats(chat_id: int) -> None:
    await safe_send_text(
        "Статус:\n"
        f"Ключей: {len(KEYWORDS)}\n"
        f"Каналов в базе: {len(CHANNELS)}\n"
        f"Каналов подключено: {len(CHANNEL_ENTITIES)}\n"
        f"Однословных лемм: {len(SINGLE_WORD_LEMMAS)}\n"
        f"Фраз: {len(PHRASES_LC)}\n"
        f"Обработано в памяти: {len(PROCESSED_LOOKUP)}\n"
        f"База: {html.escape(str(DB_PATH.name))}",
        chat_id,
    )


def parse_channel_input(text: str) -> dict:
    raw = text.strip()
    if not raw:
        raise ValueError("Введите ссылку, @username, invite-ссылку или ID канала.")

    custom_text = ""
    name = ""
    if "|" in raw:
        raw, custom_text = [part.strip() for part in raw.split("|", 1)]
    else:
        parts = raw.split(maxsplit=1)
        if len(parts) == 2:
            raw, custom_text = parts[0].strip(), parts[1].strip()

    if raw.lstrip("-").isdigit():
        channel = {"id": int(raw)}
    else:
        link = raw.strip()
        if link.startswith("@"):
            link = f"https://t.me/{link[1:]}"
        elif link.startswith("t.me/"):
            link = f"https://{link}"
        elif not link.startswith(("https://t.me/", "http://t.me/")):
            link = f"https://t.me/{link.lstrip('/')}"
        channel = {"link": link}
        name = link.rsplit("/", 1)[-1]

    if name:
        channel["name"] = name
    if custom_text:
        channel["custom_text"] = custom_text
    return channel


def channel_keys(channel: dict) -> Set[str]:
    keys = set()
    if "id" in channel:
        keys.add(str(channel["id"]))
    link = channel.get("link")
    if link:
        normalized = str(link).strip()
        keys.add(normalized.casefold())
        keys.add(normalized.replace("https://", "").replace("http://", "").casefold())
        keys.add(normalized.rsplit("/", 1)[-1].lstrip("@").casefold())
    return {key for key in keys if key}


def find_channel_index(reference: str) -> Optional[int]:
    try:
        target = parse_channel_input(reference)
    except ValueError:
        target = {"link": reference.strip()}
    target_keys = channel_keys(target)
    for index, channel in enumerate(CHANNELS):
        if channel_keys(channel) & target_keys:
            return index
    return None


async def refresh_channel_filters() -> None:
    global CHANNEL_ENTITIES, ALLOWED_IDS, ALLOWED_USERNAMES, ALLOWED_ID_STRINGS
    CHANNEL_ENTITIES, ALLOWED_IDS, ALLOWED_USERNAMES, ALLOWED_ID_STRINGS = await build_filters()


async def add_channel_and_refresh(text: str) -> str:
    try:
        channel = parse_channel_input(text)
    except ValueError as exc:
        return str(exc)
    if not add_channel_db(channel):
        return "Такой канал уже есть."
    refresh_memory_from_db()
    joined = await join_channel(channel)
    await refresh_channel_filters()
    return "Канал добавлен и подключён." if joined else "Канал сохранён, но пока недоступен."


async def delete_channel_and_refresh(reference: str) -> str:
    removed = delete_channel_db(reference)
    refresh_memory_from_db()
    if removed:
        await refresh_channel_filters()
        return f"Удалил: {html.escape(str(removed.get('link') or removed.get('id')))}"
    return "Не нашёл такой канал."


async def set_channel_label_and_refresh(payload: str) -> str:
    if "=>" not in payload:
        return "Формат: канал => новая метка"
    reference, label = [part.strip() for part in payload.split("=>", 1)]
    ok = set_channel_label_db(reference, label)
    refresh_memory_from_db()
    if ok:
        await refresh_channel_filters()
        return "Метка канала обновлена."
    return "Не нашёл такой канал."


async def reload_all_from_db() -> str:
    refresh_memory_from_db()
    await refresh_channel_filters()
    return "Перезагрузил данные из SQLite."


async def send_channel_list(chat_id: int) -> None:
    lines = []
    for index, channel in enumerate(CHANNELS, 1):
        ref = channel.get("link") or channel.get("id")
        label = channel.get("custom_text") or channel.get("name") or ""
        suffix = f" | {html.escape(str(label))}" if label else ""
        lines.append(f"{index}. {html.escape(str(ref))}{suffix}")
    await send_long_text(chat_id, "Каналы:\n\n" + "\n".join(lines))


async def send_channel_search(chat_id: int, query: str) -> None:
    query_cf = query.strip().casefold()
    matches = []
    for channel in CHANNELS:
        haystack = " ".join(str(value) for value in channel.values()).casefold()
        if query_cf and query_cf in haystack:
            matches.append(channel)
    if not matches:
        await safe_send_text("Ничего не нашёл.", chat_id)
        return
    lines = []
    for index, channel in enumerate(matches[:50], 1):
        ref = channel.get("link") or channel.get("id")
        label = channel.get("custom_text") or channel.get("name") or ""
        suffix = f" | {html.escape(str(label))}" if label else ""
        lines.append(f"{index}. {html.escape(str(ref))}{suffix}")
    await safe_send_text("Нашёл:\n\n" + "\n".join(lines), chat_id)


async def send_errors(chat_id: int) -> None:
    if not ERROR_LOG_PATH.exists():
        await safe_send_text("Файл ошибок пока пуст.", chat_id)
        return
    lines = ERROR_LOG_PATH.read_text(encoding="utf-8", errors="replace").splitlines()[-20:]
    await send_long_text(chat_id, "Последние ошибки:\n\n" + html.escape("\n".join(lines) or "Ошибок нет."))


async def handle_admin_text(chat_id: int, text: str) -> None:
    text = text.strip()
    mode = ADMIN_MODES.pop(chat_id, "")

    if mode == "add":
        await safe_send_text("Добавил." if add_keyword(text) else "Такой ключ уже есть или текст пустой.", chat_id)
    elif mode == "delete":
        await safe_send_text("Удалил." if delete_keyword(text) else "Не нашёл такой ключ.", chat_id)
    elif mode == "rename":
        if "=>" not in text:
            await safe_send_text("Формат: старое => новое", chat_id)
            return
        old, new = [part.strip() for part in text.split("=>", 1)]
        await safe_send_text("Изменил." if rename_keyword(old, new) else "Не нашёл старый ключ.", chat_id)
    elif mode == "search":
        await send_keyword_search(chat_id, text)
    elif mode == "channel_add":
        await safe_send_text(await add_channel_and_refresh(text), chat_id)
    elif mode == "channel_delete":
        await safe_send_text(await delete_channel_and_refresh(text), chat_id)
    elif mode == "channel_label":
        await safe_send_text(await set_channel_label_and_refresh(text), chat_id)
    elif mode == "channel_search":
        await send_channel_search(chat_id, text)
    elif mode == "channel_check":
        await safe_send_text(await check_channel_access(text), chat_id)
    elif text.startswith("/start") or text.startswith("/menu"):
        await send_admin_menu(chat_id)
    elif text.startswith("/add "):
        await safe_send_text("Добавил." if add_keyword(text[5:]) else "Такой ключ уже есть или текст пустой.", chat_id)
    elif text.startswith("/del "):
        await safe_send_text("Удалил." if delete_keyword(text[5:]) else "Не нашёл такой ключ.", chat_id)
    elif text.startswith("/rename "):
        payload = text[8:].strip()
        if "=>" not in payload:
            await safe_send_text("Формат: /rename старое => новое", chat_id)
            return
        old, new = [part.strip() for part in payload.split("=>", 1)]
        await safe_send_text("Изменил." if rename_keyword(old, new) else "Не нашёл старый ключ.", chat_id)
    elif text.startswith("/search "):
        await send_keyword_search(chat_id, text[8:])
    elif text.startswith("/list"):
        await send_keyword_list(chat_id)
    elif text.startswith("/stats"):
        await send_stats(chat_id)
    elif text.startswith("/errors"):
        await send_errors(chat_id)
    elif text.startswith("/ch_add "):
        await safe_send_text(await add_channel_and_refresh(text[8:]), chat_id)
    elif text.startswith("/ch_del "):
        await safe_send_text(await delete_channel_and_refresh(text[8:]), chat_id)
    elif text.startswith("/ch_label "):
        await safe_send_text(await set_channel_label_and_refresh(text[10:]), chat_id)
    elif text.startswith("/ch_check "):
        await safe_send_text(await check_channel_access(text[10:]), chat_id)
    elif text.startswith("/ch_search "):
        await send_channel_search(chat_id, text[11:])
    elif text.startswith("/ch_list"):
        await send_channel_list(chat_id)
    elif text.startswith("/reload") or text.startswith("/ch_reload"):
        await safe_send_text(await reload_all_from_db(), chat_id)
    else:
        await send_admin_menu(chat_id)


async def handle_callback(chat_id: int, callback: Any) -> None:
    data = callback.data or ""
    if data == "menu:back":
        ADMIN_MODES.pop(chat_id, None)
        await send_admin_menu(chat_id)
    elif data == "kw:add":
        ADMIN_MODES[chat_id] = "add"
        await safe_send_text("Отправьте ключевое слово или фразу.", chat_id, reply_markup=back_keyboard())
    elif data == "kw:delete":
        ADMIN_MODES[chat_id] = "delete"
        await safe_send_text("Отправьте точный ключ для удаления.", chat_id, reply_markup=back_keyboard())
    elif data == "kw:rename":
        ADMIN_MODES[chat_id] = "rename"
        await safe_send_text("Формат: старое => новое", chat_id, reply_markup=back_keyboard())
    elif data == "kw:search":
        ADMIN_MODES[chat_id] = "search"
        await safe_send_text("Отправьте часть ключа для поиска.", chat_id, reply_markup=back_keyboard())
    elif data == "kw:list":
        await send_keyword_list(chat_id)
    elif data == "kw:stats":
        await send_stats(chat_id)
    elif data == "ch:add":
        ADMIN_MODES[chat_id] = "channel_add"
        await safe_send_text(
            "Отправьте канал:\n"
            "@username | метка\n"
            "https://t.me/+invite_hash | метка\n"
            "-1001234567890 | метка",
            chat_id,
            reply_markup=back_keyboard(),
        )
    elif data == "ch:delete":
        ADMIN_MODES[chat_id] = "channel_delete"
        await safe_send_text("Отправьте ссылку, @username или ID канала для удаления.", chat_id, reply_markup=back_keyboard())
    elif data == "ch:check":
        ADMIN_MODES[chat_id] = "channel_check"
        await safe_send_text("Отправьте ссылку, @username или ID канала для проверки.", chat_id, reply_markup=back_keyboard())
    elif data == "ch:label":
        ADMIN_MODES[chat_id] = "channel_label"
        await safe_send_text("Отправьте: ссылка_или_id => новая метка", chat_id, reply_markup=back_keyboard())
    elif data == "ch:search":
        ADMIN_MODES[chat_id] = "channel_search"
        await safe_send_text("Отправьте часть ссылки, ID или метки канала.", chat_id, reply_markup=back_keyboard())
    elif data == "ch:list":
        await send_channel_list(chat_id)
    elif data == "errors:last":
        await send_errors(chat_id)
    elif data == "all:reload":
        await safe_send_text(await reload_all_from_db(), chat_id)
    await answer_callback(callback)


def admin_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("Ключевые слова", callback_data="kw:list")],
            [InlineKeyboardButton("Каналы", callback_data="ch:list")],
            [
                InlineKeyboardButton("Статус", callback_data="stats:show"),
                InlineKeyboardButton("Ошибки", callback_data="errors:last"),
            ],
            [InlineKeyboardButton("Перезагрузить", callback_data="all:reload")],
        ]
    )


def keyword_list_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("Добавить", callback_data="kw:add"),
                InlineKeyboardButton("Убрать", callback_data="kw:delete"),
            ],
            [
                InlineKeyboardButton("Изменить", callback_data="kw:rename"),
                InlineKeyboardButton("Найти", callback_data="kw:search"),
            ],
            [InlineKeyboardButton("Назад", callback_data="menu:back")],
        ]
    )


def channel_list_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("Добавить канал", callback_data="ch:add")],
            [
                InlineKeyboardButton("Убрать", callback_data="ch:delete"),
                InlineKeyboardButton("Проверить", callback_data="ch:check"),
            ],
            [
                InlineKeyboardButton("Метка", callback_data="ch:label"),
                InlineKeyboardButton("Найти", callback_data="ch:search"),
            ],
            [InlineKeyboardButton("Назад", callback_data="menu:back")],
        ]
    )


def channel_type_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("Открытый канал", callback_data="ch:add_public")],
            [InlineKeyboardButton("Закрытый канал", callback_data="ch:add_private")],
            [InlineKeyboardButton("Назад", callback_data="ch:list")],
        ]
    )


def back_keyboard(target: str = "menu:back") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("Назад", callback_data=target)]])


async def delete_message_quiet(chat_id: int, message_id: Optional[int]) -> None:
    if not message_id:
        return
    try:
        await bot.delete_message(chat_id=chat_id, message_id=message_id)
    except Exception:
        pass


async def show_admin_screen(
    chat_id: int,
    text: str,
    reply_markup: Optional[InlineKeyboardMarkup] = None,
    message_id: Optional[int] = None,
) -> None:
    target_message_id = message_id or ADMIN_SCREEN_MESSAGES.get(chat_id)
    if target_message_id:
        try:
            await bot.edit_message_text(
                chat_id=chat_id,
                message_id=target_message_id,
                text=text[:4096],
                parse_mode="HTML",
                disable_web_page_preview=True,
                reply_markup=reply_markup,
            )
            ADMIN_SCREEN_MESSAGES[chat_id] = target_message_id
            return
        except Exception:
            await delete_message_quiet(chat_id, target_message_id)

    message = await safe_send_text(text, chat_id=chat_id, reply_markup=reply_markup)
    if message:
        ADMIN_SCREEN_MESSAGES[chat_id] = message.message_id


async def send_admin_menu(chat_id: int, message_id: Optional[int] = None) -> None:
    ADMIN_MODES.pop(chat_id, None)
    await show_admin_screen(
        chat_id,
        "Панель управления.\n\n"
        "Ключевые слова - список слов и фраз, по которым бот ищет посты.\n"
        "Каналы - источники, которые бот читает через Telethon.\n"
        "Статус - сколько ключей/каналов сейчас подключено.\n"
        "Ошибки - последние ошибки из errors.log.\n"
        "Перезагрузить - перечитать данные из SQLite.",
        admin_keyboard(),
        message_id,
    )


def format_keyword_list(limit: int = 80) -> str:
    if not KEYWORDS:
        return "Ключевые слова пока пустые."
    lines = [f"{index + 1}. {html.escape(value)}" for index, value in enumerate(KEYWORDS[:limit])]
    if len(KEYWORDS) > limit:
        lines.append(f"\n...и еще {len(KEYWORDS) - limit}. Используйте «Найти».")
    return "Ключевые слова:\n\n" + "\n".join(lines)


async def show_keyword_list(chat_id: int, message_id: Optional[int] = None) -> None:
    await show_admin_screen(chat_id, format_keyword_list(), keyword_list_keyboard(), message_id)


def keyword_search_matches(query: str) -> List[str]:
    query = query.strip()
    if not query:
        return []
    query_cf = query.casefold()
    query_words = word_re.findall(query.lower())
    query_lemmas = {lemma(word) for word in query_words}
    matches = []
    for item in KEYWORDS:
        item_cf = item.casefold()
        item_words = word_re.findall(item.lower())
        item_lemmas = {lemma(word) for word in item_words}
        if query_cf in item_cf or query_lemmas & item_lemmas:
            matches.append(item)
    return matches or difflib.get_close_matches(query, KEYWORDS, n=10, cutoff=0.55)


def format_numbered_items(items: List[str], title: str = "Варианты") -> str:
    if not items:
        return f"{title}: ничего не найдено."
    lines = [f"{index + 1}. {html.escape(value)}" for index, value in enumerate(items[:50])]
    if len(items) > 50:
        lines.append(f"\n...и еще {len(items) - 50}. Уточните поиск.")
    return f"{title}:\n\n" + "\n".join(lines)


def prompt_with_keyword_list(prompt: str) -> str:
    return f"{prompt}\n\n{format_keyword_list()}"


def prompt_with_channel_list(prompt: str) -> str:
    return f"{prompt}\n\n{format_channel_list()}"


def resolve_keyword_for_action(reference: str) -> Tuple[Optional[str], List[str]]:
    direct = resolve_keyword_reference(reference)
    if direct:
        return direct, []
    exact = next((item for item in KEYWORDS if item.casefold() == reference.strip().casefold()), None)
    if exact:
        return exact, []
    return None, keyword_search_matches(reference)


def channel_search_matches(query: str) -> List[Tuple[int, dict]]:
    query_cf = query.strip().casefold()
    if not query_cf:
        return []
    matches = []
    for index, channel in enumerate(CHANNELS, 1):
        haystack = " ".join(str(value) for value in channel.values()).casefold()
        if query_cf in haystack:
            matches.append((index, channel))
    return matches


def format_channel_matches(matches: List[Tuple[int, dict]], title: str = "Варианты каналов") -> str:
    if not matches:
        return f"{title}: ничего не найдено."
    lines = []
    for index, channel in matches[:50]:
        ref = channel.get("link") or channel.get("id")
        label = channel.get("custom_text") or channel.get("name") or ""
        suffix = f" | {html.escape(str(label))}" if label else ""
        lines.append(f"{index}. {html.escape(str(ref))}{suffix}")
    if len(matches) > 50:
        lines.append(f"\n...и еще {len(matches) - 50}. Уточните поиск.")
    return f"{title}:\n\n" + "\n".join(lines)


def resolve_channel_for_action(reference: str) -> Tuple[Optional[str], List[Tuple[int, dict]]]:
    direct = resolve_channel_reference(reference)
    if direct:
        return direct, []
    if find_channel_index(reference) is not None:
        return reference, []
    return None, channel_search_matches(reference)


def split_reference_and_value(payload: str) -> Tuple[str, str]:
    payload = payload.strip()
    if "=>" in payload:
        left, right = payload.split("=>", 1)
        return left.strip(), right.strip()
    left, separator, right = payload.partition(" ")
    if not separator:
        return payload, ""
    return left.strip(), right.strip()


async def show_keyword_search(chat_id: int, query: str) -> None:
    matches = keyword_search_matches(query)
    if not matches:
        await show_admin_screen(chat_id, "Ничего не нашёл по ключевым словам.", keyword_list_keyboard())
        return
    lines = [f"{index + 1}. {html.escape(value)}" for index, value in enumerate(matches[:50])]
    await show_admin_screen(chat_id, "Нашёл ключи:\n\n" + "\n".join(lines), keyword_list_keyboard())


def format_channel_list(limit: int = 80) -> str:
    if not CHANNELS:
        return "Каналы пока пустые."
    lines = []
    for index, channel in enumerate(CHANNELS[:limit], 1):
        ref = channel.get("link") or channel.get("id")
        label = channel.get("custom_text") or channel.get("name") or ""
        suffix = f" | {html.escape(str(label))}" if label else ""
        lines.append(f"{index}. {html.escape(str(ref))}{suffix}")
    if len(CHANNELS) > limit:
        lines.append(f"\n...и еще {len(CHANNELS) - limit}. Используйте «Найти».")
    return "Каналы:\n\n" + "\n".join(lines)


async def show_channel_list(chat_id: int, message_id: Optional[int] = None) -> None:
    await show_admin_screen(chat_id, format_channel_list(), channel_list_keyboard(), message_id)


async def show_channel_search(chat_id: int, query: str) -> None:
    matches = channel_search_matches(query)
    if not matches:
        await show_admin_screen(chat_id, "Ничего не нашёл по каналам.", channel_list_keyboard())
        return
    await show_admin_screen(chat_id, format_channel_matches(matches, "Нашёл каналы"), channel_list_keyboard())


async def show_stats(chat_id: int) -> None:
    await show_admin_screen(
        chat_id,
        "Статус:\n"
        f"Ключей: {len(KEYWORDS)}\n"
        f"Каналов в базе: {len(CHANNELS)}\n"
        f"Каналов подключено: {len(CHANNEL_ENTITIES)}\n"
        f"Однословных лемм: {len(SINGLE_WORD_LEMMAS)}\n"
        f"Фраз: {len(PHRASES_LC)}\n"
        f"Обработано в памяти: {len(PROCESSED_LOOKUP)}\n"
        f"База: {html.escape(str(DB_PATH.name))}",
        back_keyboard(),
    )


async def show_errors(chat_id: int) -> None:
    if not ERROR_LOG_PATH.exists():
        await show_admin_screen(chat_id, "Файл ошибок пока пуст.", back_keyboard())
        return
    lines = ERROR_LOG_PATH.read_text(encoding="utf-8", errors="replace").splitlines()[-20:]
    await show_admin_screen(chat_id, "Последние ошибки:\n\n" + html.escape("\n".join(lines) or "Ошибок нет."), back_keyboard())


def parse_channel_payload(payload: str, private: bool = False) -> dict:
    channel = parse_channel_input(payload)
    if private and "link" in channel and "t.me/+" not in channel["link"] and "joinchat" not in channel["link"]:
        raise ValueError("Для закрытого канала пришлите invite-ссылку вида https://t.me/+hash или ID -100..., если аккаунт уже состоит в канале.")
    return channel


async def add_channel_and_refresh(text: str, private: bool = False) -> str:
    try:
        channel = parse_channel_payload(text, private=private)
    except ValueError as exc:
        return str(exc)
    if not add_channel_db(channel):
        return "Такой канал уже есть."
    refresh_memory_from_db()
    joined = await join_channel(channel)
    await refresh_channel_filters()
    if joined:
        return "Канал добавлен. Если он был открытый или была рабочая invite-ссылка, аккаунт Telethon уже попробовал подписаться."
    return "Канал сохранён, но пока недоступен. Проверьте ссылку/ID и доступ аккаунта Telethon."


async def handle_admin_text(chat_id: int, text: str, message_id: Optional[int] = None) -> None:
    text = text.strip()
    mode = ADMIN_MODES.pop(chat_id, "")
    await delete_message_quiet(chat_id, message_id)

    if mode == "add":
        result = "Добавил." if add_keyword(text) else "Такой ключ уже есть или текст пустой."
        await show_admin_screen(chat_id, result + "\n\n" + format_keyword_list(), keyword_list_keyboard())
    elif mode == "delete":
        target, suggestions = resolve_keyword_for_action(text)
        if target and delete_keyword(target):
            await show_admin_screen(chat_id, "Удалил.\n\n" + format_keyword_list(), keyword_list_keyboard())
        else:
            ADMIN_MODES[chat_id] = "delete"
            suggestion_text = format_numbered_items(suggestions, "Похожие ключи")
            await show_admin_screen(
                chat_id,
                "Точного совпадения не нашёл. Выберите номер из списка ниже или уточните название.\n\n"
                + suggestion_text
                + "\n\n"
                + format_keyword_list(),
                back_keyboard("kw:list"),
            )
    elif mode == "rename":
        old, new = split_reference_and_value(text)
        if not old or not new:
            ADMIN_MODES[chat_id] = "rename"
            await show_admin_screen(
                chat_id,
                prompt_with_keyword_list(
                    "Напишите через пробел: номер новое_название\n"
                    "Пример: 3 Астраханская область\n"
                    "Можно и так: старое название => новое название"
                ),
                back_keyboard("kw:list"),
            )
            return
        target, suggestions = resolve_keyword_for_action(old)
        if target and rename_keyword(target, new):
            await show_admin_screen(chat_id, "Изменил.\n\n" + format_keyword_list(), keyword_list_keyboard())
        else:
            ADMIN_MODES[chat_id] = "rename"
            await show_admin_screen(
                chat_id,
                "Не нашёл старый ключ. Вот похожие варианты, можно повторить с номером.\n\n"
                + format_numbered_items(suggestions, "Похожие ключи")
                + "\n\nПример: 3 Новое название",
                back_keyboard("kw:list"),
            )
    elif mode == "search":
        await show_keyword_search(chat_id, text)
    elif mode == "channel_add_public":
        await show_admin_screen(chat_id, await add_channel_and_refresh(text, private=False) + "\n\n" + format_channel_list(), channel_list_keyboard())
    elif mode == "channel_add_private":
        await show_admin_screen(chat_id, await add_channel_and_refresh(text, private=True) + "\n\n" + format_channel_list(), channel_list_keyboard())
    elif mode == "channel_delete":
        target, suggestions = resolve_channel_for_action(text)
        if target:
            await show_admin_screen(chat_id, await delete_channel_and_refresh(target) + "\n\n" + format_channel_list(), channel_list_keyboard())
        else:
            ADMIN_MODES[chat_id] = "channel_delete"
            await show_admin_screen(
                chat_id,
                "Точного канала не нашёл. Выберите номер из вариантов ниже или уточните запрос.\n\n"
                + format_channel_matches(suggestions),
                back_keyboard("ch:list"),
            )
    elif mode == "channel_label":
        reference, label = split_reference_and_value(text)
        if not reference or not label:
            ADMIN_MODES[chat_id] = "channel_label"
            await show_admin_screen(
                chat_id,
                prompt_with_channel_list(
                    "Напишите через пробел: номер новая_метка\n"
                    "Пример: 2 РИА Новости\n"
                    "Можно и так: @rian_ru => РИА Новости"
                ),
                back_keyboard("ch:list"),
            )
            return
        target, suggestions = resolve_channel_for_action(reference)
        if target:
            await show_admin_screen(chat_id, await set_channel_label_and_refresh(f"{target} => {label}") + "\n\n" + format_channel_list(), channel_list_keyboard())
        else:
            ADMIN_MODES[chat_id] = "channel_label"
            await show_admin_screen(
                chat_id,
                "Не нашёл канал. Вот похожие варианты, можно повторить с номером.\n\n"
                + format_channel_matches(suggestions)
                + "\n\nПример: 2 Новая метка",
                back_keyboard("ch:list"),
            )
    elif mode == "channel_search":
        await show_channel_search(chat_id, text)
    elif mode == "channel_check":
        target, suggestions = resolve_channel_for_action(text)
        if target:
            await show_admin_screen(chat_id, await check_channel_access(target), channel_list_keyboard())
        else:
            ADMIN_MODES[chat_id] = "channel_check"
            await show_admin_screen(
                chat_id,
                "Точного канала не нашёл. Выберите номер из вариантов ниже или уточните запрос.\n\n"
                + format_channel_matches(suggestions),
                back_keyboard("ch:list"),
            )
    elif text.startswith("/start") or text.startswith("/menu"):
        await send_admin_menu(chat_id)
    elif text.startswith("/add "):
        await show_admin_screen(chat_id, "Добавил." if add_keyword(text[5:]) else "Такой ключ уже есть или текст пустой.", keyword_list_keyboard())
    elif text.startswith("/del "):
        await show_admin_screen(chat_id, "Удалил." if delete_keyword(text[5:]) else "Не нашёл такой ключ.", keyword_list_keyboard())
    elif text.startswith("/rename "):
        payload = text[8:].strip()
        if "=>" not in payload:
            await show_admin_screen(chat_id, "Формат: /rename старое => новое", keyword_list_keyboard())
            return
        old, new = [part.strip() for part in payload.split("=>", 1)]
        await show_admin_screen(chat_id, "Изменил." if rename_keyword(old, new) else "Не нашёл старый ключ.", keyword_list_keyboard())
    elif text.startswith("/search "):
        await show_keyword_search(chat_id, text[8:])
    elif text.startswith("/list"):
        await show_keyword_list(chat_id)
    elif text.startswith("/stats"):
        await show_stats(chat_id)
    elif text.startswith("/errors"):
        await show_errors(chat_id)
    elif text.startswith("/ch_add "):
        await show_admin_screen(chat_id, await add_channel_and_refresh(text[8:]) + "\n\n" + format_channel_list(), channel_list_keyboard())
    elif text.startswith("/ch_del "):
        await show_admin_screen(chat_id, await delete_channel_and_refresh(text[8:]) + "\n\n" + format_channel_list(), channel_list_keyboard())
    elif text.startswith("/ch_label "):
        await show_admin_screen(chat_id, await set_channel_label_and_refresh(text[10:]) + "\n\n" + format_channel_list(), channel_list_keyboard())
    elif text.startswith("/ch_check "):
        await show_admin_screen(chat_id, await check_channel_access(resolve_channel_reference(text[10:]) or text[10:]), channel_list_keyboard())
    elif text.startswith("/ch_search "):
        await show_channel_search(chat_id, text[11:])
    elif text.startswith("/ch_list"):
        await show_channel_list(chat_id)
    elif text.startswith("/reload") or text.startswith("/ch_reload"):
        await show_admin_screen(chat_id, await reload_all_from_db(), admin_keyboard())
    else:
        await send_admin_menu(chat_id)


async def handle_callback(chat_id: int, callback: Any) -> None:
    data = callback.data or ""
    message_id = callback.message.message_id if callback.message else None
    if data == "menu:back":
        await send_admin_menu(chat_id, message_id)
    elif data == "kw:list":
        ADMIN_MODES.pop(chat_id, None)
        await show_keyword_list(chat_id, message_id)
    elif data == "kw:add":
        ADMIN_MODES[chat_id] = "add"
        await show_admin_screen(chat_id, "Отправьте ключевое слово или фразу.", back_keyboard("kw:list"), message_id)
    elif data == "kw:delete":
        ADMIN_MODES[chat_id] = "delete"
        await show_admin_screen(
            chat_id,
            prompt_with_keyword_list(
                "Что удалить?\n"
                "Отправьте номер из списка, точное название или часть названия.\n"
                "Пример: 4\n"
                "Пример: район"
            ),
            back_keyboard("kw:list"),
            message_id,
        )
    elif data == "kw:rename":
        ADMIN_MODES[chat_id] = "rename"
        await show_admin_screen(
            chat_id,
            prompt_with_keyword_list(
                "Что изменить?\n"
                "Пишите через пробел: номер новое_название\n"
                "Пример: 3 Астраханская область\n"
                "Или старый вариант через стрелку: старое название => новое название"
            ),
            back_keyboard("kw:list"),
            message_id,
        )
    elif data == "kw:search":
        ADMIN_MODES[chat_id] = "search"
        await show_admin_screen(chat_id, "Отправьте часть слова. Я учту леммы и похожие варианты.", back_keyboard("kw:list"), message_id)
    elif data == "ch:list":
        ADMIN_MODES.pop(chat_id, None)
        await show_channel_list(chat_id, message_id)
    elif data == "ch:add":
        await show_admin_screen(chat_id, "Какой канал добавляем?", channel_type_keyboard(), message_id)
    elif data == "ch:add_public":
        ADMIN_MODES[chat_id] = "channel_add_public"
        await show_admin_screen(
            chat_id,
            "Открытый канал.\n\n"
            "Пришлите @username или ссылку. Метку можно написать через пробел.\n"
            "Пример: @rian_ru РИА Новости\n"
            "Пример: https://t.me/rian_ru РИА Новости\n"
            "Если аккаунт Telethon не подписан, бот попробует подписаться сам.",
            back_keyboard("ch:list"),
            message_id,
        )
    elif data == "ch:add_private":
        ADMIN_MODES[chat_id] = "channel_add_private"
        await show_admin_screen(
            chat_id,
            "Закрытый канал.\n\n"
            "Лучше пришлите invite-ссылку вида https://t.me/+hash, метку можно написать через пробел.\n"
            "Пример: https://t.me/+hash Закрытый канал\n"
            "Если аккаунт уже состоит в канале, можно указать ID вида -1001234567890.",
            back_keyboard("ch:list"),
            message_id,
        )
    elif data == "ch:delete":
        ADMIN_MODES[chat_id] = "channel_delete"
        await show_admin_screen(
            chat_id,
            prompt_with_channel_list(
                "Что удалить?\n"
                "Отправьте номер из списка, ссылку, @username, ID или часть метки.\n"
                "Пример: 2\n"
                "Пример: РИА"
            ),
            back_keyboard("ch:list"),
            message_id,
        )
    elif data == "ch:check":
        ADMIN_MODES[chat_id] = "channel_check"
        await show_admin_screen(
            chat_id,
            prompt_with_channel_list(
                "Что проверить?\n"
                "Отправьте номер из списка, ссылку, @username, ID или часть метки.\n"
                "Пример: 1"
            ),
            back_keyboard("ch:list"),
            message_id,
        )
    elif data == "ch:label":
        ADMIN_MODES[chat_id] = "channel_label"
        await show_admin_screen(
            chat_id,
            prompt_with_channel_list(
                "Какую метку поставить?\n"
                "Пишите через пробел: номер новая_метка\n"
                "Пример: 2 РИА Новости\n"
                "Или так: @rian_ru => РИА Новости"
            ),
            back_keyboard("ch:list"),
            message_id,
        )
    elif data == "ch:search":
        ADMIN_MODES[chat_id] = "channel_search"
        await show_admin_screen(chat_id, "Отправьте часть ссылки, ID или метки канала.", back_keyboard("ch:list"), message_id)
    elif data == "stats:show":
        await show_stats(chat_id)
    elif data == "errors:last":
        await show_errors(chat_id)
    elif data == "all:reload":
        await show_admin_screen(chat_id, await reload_all_from_db(), admin_keyboard(), message_id)
    await answer_callback(callback)


async def bot_control_loop() -> None:
    global BOT_UPDATE_OFFSET
    while True:
        try:
            updates = await bot.get_updates(
                offset=BOT_UPDATE_OFFSET,
                timeout=10,
                allowed_updates=["message", "callback_query"],
            )
            for update in updates:
                BOT_UPDATE_OFFSET = update.update_id + 1
                if update.callback_query:
                    chat_id = update.callback_query.message.chat_id
                    if is_admin(chat_id):
                        await handle_callback(chat_id, update.callback_query)
                    else:
                        await answer_callback(update.callback_query, "Нет доступа")
                elif update.message and update.message.text:
                    chat_id = update.message.chat_id
                    if is_admin(chat_id):
                        await handle_admin_text(chat_id, update.message.text, update.message.message_id)
                    else:
                        await safe_send_text("Нет доступа к управлению ботом.", chat_id)
        except Exception as exc:
            log.error("bot_control_loop: %s", exc)
            await asyncio.sleep(BOT_CONTROL_INTERVAL)


async def build_filters() -> Tuple[Dict[str, dict], Set[int], Set[str], Set[str]]:
    entities = {}
    ids = set()
    usernames = set()
    id_strings = set()
    for channel in CHANNELS:
        try:
            entity = await get_channel_entity(channel)
            key = str(channel.get("id") or channel.get("link"))
            if channel.get("link") and "t.me/+" not in channel["link"]:
                username = channel["link"].rsplit("/", 1)[-1].lstrip("@")
                usernames.add(username.lower())
                key = username

            entities[key] = {
                "entity": entity,
                "custom_text": channel.get("custom_text", ""),
                "name": channel.get("name", "Unknown"),
            }
            peer_id = get_peer_id(entity)
            ids.add(peer_id)
            id_strings.add(str(peer_id))
            if not get_last_seen(peer_id):
                async for item in client.iter_messages(entity, limit=1):
                    set_last_seen(peer_id, item.id)
                    break
        except Exception as exc:
            log.error("Не удалось получить канал %s: %s", channel, exc)
    return entities, ids, usernames, id_strings


async def main() -> None:
    init_db()
    migrate_json_to_db()
    refresh_memory_from_db()

    try:
        await client.connect()
        if not await client.is_user_authorized():
            await client.send_code_request(CONFIG.phone_number)
            try:
                code = input("Введите код из Telegram/SMS: ")
                await client.sign_in(CONFIG.phone_number, code)
            except SessionPasswordNeededError:
                password = input("Введите пароль двухэтапной аутентификации (2FA): ")
                await client.sign_in(password=password)
    except Exception as exc:
        log.error("Ошибка авторизации: %s", exc)
        return

    for channel in CHANNELS:
        await join_channel(channel)
        await asyncio.sleep(0.2)

    await refresh_channel_filters()
    log.info("Слушаем каналы: %s", ", ".join(CHANNEL_ENTITIES.keys()))

    try:
        await client.get_dialogs(limit=0)
    except Exception as exc:
        log.warning("get_dialogs для синхронизации: %s", exc)

    background_tasks = [
        asyncio.create_task(keep_updates_alive()),
        asyncio.create_task(polling_loop()),
        asyncio.create_task(bot_control_loop()),
    ]

    @client.on(events.NewMessage)
    async def handler(event):
        chat = await event.get_chat()
        username = getattr(chat, "username", None)
        chat_id = event.chat_id

        if chat_id in ALLOWED_IDS:
            pass
        elif username and username.lower() in ALLOWED_USERNAMES:
            pass
        elif str(chat_id) in ALLOWED_ID_STRINGS:
            pass
        else:
            log.debug("skip chat_id=%s username=%s", chat_id, username)
            return

        await process_and_maybe_forward(chat, event.message, await event.get_input_chat())

    log.info("Бот запущен. Управление доступно через /menu.")
    try:
        await client.run_until_disconnected()
    except asyncio.CancelledError:
        log.info("Остановка бота...")
    except Exception as exc:
        log.error("Ошибка выполнения: %s", exc)
    finally:
        for task in background_tasks:
            task.cancel()
        await asyncio.gather(*background_tasks, return_exceptions=True)
        await client.disconnect()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        log.info("Бот остановлен пользователем.")
