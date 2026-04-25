import asyncio
import html
import json
import logging
import os
import re
import sys
import tempfile
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

import pymorphy2
from telegram import Bot, InlineKeyboardButton, InlineKeyboardMarkup, error
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


logging.basicConfig(level=logging.INFO, format="%(levelname)s:%(name)s:%(message)s")
log = logging.getLogger("forwarder")
logging.getLogger("telethon.client.updates").setLevel(logging.WARNING)
logging.getLogger("telethon.client.users").setLevel(logging.WARNING)


def app_path() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


BASE_DIR = app_path()
DATA_DIR = BASE_DIR / "data"
CONFIG_PATH = BASE_DIR / "config_telegram.json"
KEYWORDS_PATH = BASE_DIR / "keywords.json"
CHANNELS_PATH = BASE_DIR / "channels.json"
STATE_PATH = BASE_DIR / "state.json"

RATE_LIMIT_DELAY = 0.8
SEND_DELAY = 0.4
POLL_INTERVAL = 20
POLL_LIMIT_PER_CHANNEL = 5
PROCESSED_MAX_ITEMS = 5000
BOT_CONTROL_INTERVAL = 1.2

word_re = re.compile(r"\w+", flags=re.UNICODE)


@dataclass
class AppConfig:
    api_id: int
    api_hash: str
    phone_number: str
    bot_token: str
    channel_chat_id: str
    admin_chat_ids: Set[int]


def load_json(path: Path) -> Any:
    if not path.exists():
        raise FileNotFoundError(f"Не найден файл: {path}")
    try:
        with path.open("r", encoding="utf-8-sig") as f:
            return json.load(f)
    except json.JSONDecodeError as exc:
        raise ValueError(f"Файл {path.name} содержит ошибку JSON: {exc}") from exc


def save_json(path: Path, data: Any) -> None:
    with path.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
        f.write("\n")


def load_config() -> AppConfig:
    raw = load_json(CONFIG_PATH)
    required = ("api_id", "api_hash", "phone_number", "bot_token", "channel_chat_id")
    missing = [name for name in required if raw.get(name) in (None, "")]
    if missing:
        raise ValueError(
            "Заполните поля в config_telegram.json: " + ", ".join(missing)
        )

    try:
        api_id = int(raw["api_id"])
    except (TypeError, ValueError) as exc:
        raise ValueError("api_id должен быть числом") from exc

    admins = raw.get("admin_chat_ids") or []
    admin_chat_ids = {int(x) for x in admins}
    return AppConfig(
        api_id=api_id,
        api_hash=str(raw["api_hash"]),
        phone_number=str(raw["phone_number"]),
        bot_token=str(raw["bot_token"]),
        channel_chat_id=str(raw["channel_chat_id"]),
        admin_chat_ids=admin_chat_ids,
    )


try:
    CONFIG = load_config()
    RAW_KEYWORDS: List[str] = load_json(KEYWORDS_PATH)
    CHANNELS: List[dict] = load_json(CHANNELS_PATH)
except Exception as exc:
    log.error("%s", exc)
    sys.exit(1)


morph = pymorphy2.MorphAnalyzer(path=str(DATA_DIR))
client = TelegramClient(str(BASE_DIR / "session_name"), CONFIG.api_id, CONFIG.api_hash)
bot = Bot(token=CONFIG.bot_token)

RESOLVE_CACHE: Dict[str, Any] = {}
PROCESSED = deque(maxlen=PROCESSED_MAX_ITEMS)
PROCESSED_LOOKUP: Set[Tuple[int, int]] = set()
LAST_SEEN_ID: Dict[int, int] = {}
CHANNEL_ENTITIES: Dict[str, dict] = {}
ALLOWED_IDS: Set[int] = set()
ALLOWED_USERNAMES: Set[str] = set()
ALLOWED_ID_STRINGS: Set[str] = set()
ADMIN_MODES: Dict[int, str] = {}
BOT_UPDATE_OFFSET = 0

SINGLE_WORD_LEMMAS: Set[str] = set()
PHRASES_LC: List[str] = []
KEYWORDS: List[str] = []


def is_admin(chat_id: int) -> bool:
    if CONFIG.admin_chat_ids:
        return chat_id in CONFIG.admin_chat_ids
    return str(chat_id) == str(CONFIG.channel_chat_id)


def remember_processed(key: Tuple[int, int]) -> bool:
    if key in PROCESSED_LOOKUP:
        return False
    if len(PROCESSED) == PROCESSED.maxlen and PROCESSED:
        oldest = PROCESSED[0]
        PROCESSED_LOOKUP.discard(oldest)
    PROCESSED.append(key)
    PROCESSED_LOOKUP.add(key)
    return True


def lemma(text: str) -> str:
    return morph.parse(text)[0].normal_form


def rebuild_keyword_index() -> None:
    SINGLE_WORD_LEMMAS.clear()
    PHRASES_LC.clear()
    seen = set()
    KEYWORDS.clear()

    for item in RAW_KEYWORDS:
        keyword = str(item or "").strip()
        if not keyword:
            continue
        key = keyword.casefold()
        if key in seen:
            continue
        seen.add(key)
        KEYWORDS.append(keyword)
        parts = word_re.findall(keyword)
        if len(parts) <= 1:
            SINGLE_WORD_LEMMAS.add(lemma(keyword.lower()))
        else:
            PHRASES_LC.append(keyword.lower())


def save_keywords() -> None:
    save_json(KEYWORDS_PATH, KEYWORDS)


def add_keyword(keyword: str) -> bool:
    keyword = keyword.strip()
    if not keyword:
        return False
    existing = {k.casefold() for k in KEYWORDS}
    if keyword.casefold() in existing:
        return False
    RAW_KEYWORDS.append(keyword)
    rebuild_keyword_index()
    save_keywords()
    return True


def delete_keyword(keyword: str) -> bool:
    keyword_cf = keyword.strip().casefold()
    if not keyword_cf:
        return False
    before = len(RAW_KEYWORDS)
    RAW_KEYWORDS[:] = [k for k in RAW_KEYWORDS if str(k).strip().casefold() != keyword_cf]
    changed = len(RAW_KEYWORDS) != before
    if changed:
        rebuild_keyword_index()
        save_keywords()
    return changed


def rename_keyword(old: str, new: str) -> bool:
    old_cf = old.strip().casefold()
    new = new.strip()
    if not old_cf or not new:
        return False
    changed = False
    for index, value in enumerate(RAW_KEYWORDS):
        if str(value).strip().casefold() == old_cf:
            RAW_KEYWORDS[index] = new
            changed = True
            break
    if changed:
        rebuild_keyword_index()
        save_keywords()
    return changed


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


def format_forward_text(chat: Any, message: Any, triggers: List[str]) -> str:
    phrases, words = find_triggers(message.text or "")
    highlighted = highlight_text(message.text or "", phrases, words)
    message_link = message_link_for(chat, message.id)
    title = html.escape(getattr(chat, "title", "Источник"))
    custom_text = html.escape(get_channel_custom_text(chat))

    if custom_text:
        header = f'Найден пост в {custom_text} <a href="{message_link}">{title}</a>'
    else:
        header = f'Найден пост в <a href="{message_link}">{title}</a>'

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


async def join_channel(channel: dict) -> bool:
    if "id" in channel:
        try:
            entity = await client.get_input_entity(channel["id"])
            await asyncio.sleep(0.2)
            await client(JoinChannelRequest(entity))
            log.info("Подписались на канал ID %s", channel["id"])
        except UserAlreadyParticipantError:
            log.info("Уже подписаны на канал ID %s", channel["id"])
        except Exception as exc:
            log.error("Не удалось подключить канал ID %s: %s", channel["id"], exc)
            return False
        return True

    link = channel.get("link", "")
    try:
        if "joinchat" in link or "t.me/+" in link:
            invite_hash = link.split("/")[-1].replace("+", "")
            try:
                await asyncio.sleep(0.2)
                await client(ImportChatInviteRequest(invite_hash))
                log.info("Подписались по инвайт-ссылке: %s", link)
                return True
            except FloodWaitError as exc:
                log.warning("FloodWait %ss для %s", exc.seconds, link)
                await asyncio.sleep(exc.seconds)
                await client(ImportChatInviteRequest(invite_hash))
                return True
            except (InviteHashExpiredError, InviteHashInvalidError) as exc:
                log.error("Проблема с инвайт-ссылкой %s: %s", link, exc)
                return False
            except UserAlreadyParticipantError:
                log.info("Уже подписаны: %s", link)
                return True

        username = link.rsplit("/", 1)[-1].lstrip("@")
        entity = await resolve_username_once(username)
        try:
            await asyncio.sleep(0.2)
            await client(JoinChannelRequest(entity))
            log.info("Подписались на канал: %s", link)
        except UserAlreadyParticipantError:
            log.info("Уже подписаны: %s", link)
        except Exception as exc:
            log.error("Не удалось подписаться на %s: %s", link, exc)
            return False
        return True
    except Exception as exc:
        log.error("Не удалось обработать канал %s: %s", link, exc)
        return False


async def safe_send_text(text: str, chat_id: Optional[int] = None, reply_markup=None) -> None:
    target = chat_id if chat_id is not None else CONFIG.channel_chat_id
    attempts = 0
    while True:
        try:
            await asyncio.sleep(SEND_DELAY)
            await bot.send_message(
                chat_id=target,
                text=text[:4096],
                parse_mode="HTML",
                disable_web_page_preview=True,
                reply_markup=reply_markup,
            )
            return
        except (error.TimedOut, asyncio.TimeoutError) as exc:
            attempts += 1
            if attempts >= 3:
                log.error("Сообщение не отправилось после повторов: %s", exc)
                return
            await asyncio.sleep(2**attempts)
        except error.BadRequest as exc:
            log.error("Ошибка отправки сообщения: %s", exc)
            return
        except Exception as exc:
            log.error("Непредвиденная ошибка отправки: %s", exc)
            return


async def safe_send_media(text: str, media_path: Path, media_kind: str) -> None:
    attempts = 0
    caption = text if len(text) <= 1000 else "Найден пост с медиа. Текст отправлен отдельным сообщением."
    while True:
        try:
            await asyncio.sleep(SEND_DELAY)
            with media_path.open("rb") as media:
                if media_kind == "photo":
                    await bot.send_photo(
                        chat_id=CONFIG.channel_chat_id,
                        photo=media,
                        caption=caption,
                        parse_mode="HTML",
                    )
                elif media_kind == "video":
                    await bot.send_video(
                        chat_id=CONFIG.channel_chat_id,
                        video=media,
                        caption=caption,
                        parse_mode="HTML",
                    )
                else:
                    await bot.send_document(
                        chat_id=CONFIG.channel_chat_id,
                        document=media,
                        caption=caption,
                        parse_mode="HTML",
                    )
            if len(text) > 1024:
                await safe_send_text(text)
            return
        except (error.TimedOut, asyncio.TimeoutError) as exc:
            attempts += 1
            if attempts >= 3:
                log.error("Медиа не отправилось после повторов: %s", exc)
                return
            await asyncio.sleep(2**attempts)
        except error.BadRequest as exc:
            log.error("Ошибка отправки медиа: %s", exc)
            await safe_send_text(text)
            return
        except Exception as exc:
            log.error("Непредвиденная ошибка отправки медиа: %s", exc)
            await safe_send_text(text)
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


async def forward_to_target(chat: Any, message: Any, text: str) -> None:
    kind = media_kind_for(message)
    if not kind:
        await safe_send_text(text)
        return

    temp_path = None
    try:
        with tempfile.TemporaryDirectory() as temp_dir:
            downloaded = await client.download_media(message, file=temp_dir)
            if not downloaded:
                await safe_send_text(text)
                return
            temp_path = Path(downloaded)
            await safe_send_media(text, temp_path, kind)
    except Exception as exc:
        log.error("Не удалось переслать медиа, отправляю только текст: %s", exc)
        await safe_send_text(text)


async def process_and_maybe_forward(chat: Any, message: Any) -> None:
    if not message:
        return
    key = (message.chat_id, message.id)
    if not remember_processed(key):
        return
    if not getattr(message, "text", None):
        return

    should, triggers = should_forward(message.text)
    log.info("Текст: %r | найдено ключей: %s", message.text, triggers)
    if not should:
        return

    text = format_forward_text(chat, message, triggers)
    await forward_to_target(chat, message, text)


async def keep_updates_alive() -> None:
    while True:
        try:
            await client.get_dialogs(limit=0)
        except Exception as exc:
            log.warning("keepalive/get_dialogs: %s", exc)
        await asyncio.sleep(20)


def load_state() -> None:
    global LAST_SEEN_ID
    if not STATE_PATH.exists():
        return
    try:
        raw = load_json(STATE_PATH)
        LAST_SEEN_ID = {int(k): int(v) for k, v in raw.get("last_seen_id", {}).items()}
    except Exception as exc:
        log.warning("Не удалось загрузить state.json: %s", exc)


def save_state() -> None:
    save_json(STATE_PATH, {"last_seen_id": {str(k): v for k, v in LAST_SEEN_ID.items()}})


async def polling_loop() -> None:
    while True:
        try:
            for info in CHANNEL_ENTITIES.values():
                entity = info["entity"]
                chat_id = get_peer_id(entity)
                last_id = LAST_SEEN_ID.get(chat_id, 0)
                new_msgs = []

                async for message in client.iter_messages(entity, limit=POLL_LIMIT_PER_CHANNEL):
                    if last_id and message.id <= last_id:
                        break
                    new_msgs.append(message)

                for message in reversed(new_msgs):
                    chat = await message.get_chat()
                    await process_and_maybe_forward(chat, message)
                    LAST_SEEN_ID[chat_id] = max(LAST_SEEN_ID.get(chat_id, 0), message.id)
                    save_state()
                    await asyncio.sleep(0.1)

                await asyncio.sleep(0.1)
        except Exception as exc:
            log.warning("polling_loop: %s", exc)

        await asyncio.sleep(POLL_INTERVAL)


def admin_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("➕ Добавить", callback_data="kw:add"),
                InlineKeyboardButton("➖ Удалить", callback_data="kw:delete"),
            ],
            [
                InlineKeyboardButton("✏️ Изменить", callback_data="kw:rename"),
                InlineKeyboardButton("🔎 Найти", callback_data="kw:search"),
            ],
            [
                InlineKeyboardButton("📋 Список", callback_data="kw:list"),
                InlineKeyboardButton("📊 Статус", callback_data="kw:stats"),
            ],
            [
                InlineKeyboardButton("🔄 Перезагрузить", callback_data="kw:reload"),
            ],
        ]
    )


async def send_admin_menu(chat_id: int) -> None:
    await safe_send_text(
        "Панель управления ключевыми словами.\n\n"
        "Можно пользоваться кнопками или командами:\n"
        "/add слово\n"
        "/del слово\n"
        "/rename старое => новое\n"
        "/search часть_слова\n"
        "/list\n"
        "/stats",
        chat_id=chat_id,
        reply_markup=admin_keyboard(),
    )


async def answer_callback(callback: Any, text: str = "Готово") -> None:
    try:
        await bot.answer_callback_query(callback_query_id=callback.id, text=text)
    except Exception:
        pass


async def handle_admin_text(chat_id: int, text: str) -> None:
    text = text.strip()
    mode = ADMIN_MODES.pop(chat_id, "")

    if mode == "add":
        added = add_keyword(text)
        await safe_send_text("Добавил." if added else "Такой ключ уже есть или текст пустой.", chat_id)
        return
    if mode == "delete":
        deleted = delete_keyword(text)
        await safe_send_text("Удалил." if deleted else "Не нашёл такой ключ.", chat_id)
        return
    if mode == "rename":
        if "=>" not in text:
            await safe_send_text("Формат: старое => новое", chat_id)
            return
        old, new = [part.strip() for part in text.split("=>", 1)]
        renamed = rename_keyword(old, new)
        await safe_send_text("Изменил." if renamed else "Не нашёл старый ключ.", chat_id)
        return
    if mode == "search":
        await send_keyword_search(chat_id, text)
        return

    if text.startswith("/start") or text.startswith("/menu"):
        await send_admin_menu(chat_id)
    elif text.startswith("/add "):
        added = add_keyword(text[5:])
        await safe_send_text("Добавил." if added else "Такой ключ уже есть или текст пустой.", chat_id)
    elif text.startswith("/del "):
        deleted = delete_keyword(text[5:])
        await safe_send_text("Удалил." if deleted else "Не нашёл такой ключ.", chat_id)
    elif text.startswith("/rename "):
        payload = text[8:].strip()
        if "=>" not in payload:
            await safe_send_text("Формат: /rename старое => новое", chat_id)
            return
        old, new = [part.strip() for part in payload.split("=>", 1)]
        renamed = rename_keyword(old, new)
        await safe_send_text("Изменил." if renamed else "Не нашёл старый ключ.", chat_id)
    elif text.startswith("/search "):
        await send_keyword_search(chat_id, text[8:])
    elif text.startswith("/list"):
        await send_keyword_list(chat_id)
    elif text.startswith("/stats"):
        await send_stats(chat_id)
    elif text.startswith("/reload"):
        reload_keywords_from_file()
        await safe_send_text("Перезагрузил keywords.json.", chat_id)
    else:
        await send_admin_menu(chat_id)


async def send_keyword_list(chat_id: int) -> None:
    lines = [f"{index + 1}. {html.escape(value)}" for index, value in enumerate(KEYWORDS)]
    text = "Ключевые слова:\n\n" + "\n".join(lines)
    for start in range(0, len(text), 3500):
        await safe_send_text(text[start : start + 3500], chat_id)


async def send_keyword_search(chat_id: int, query: str) -> None:
    query_cf = query.strip().casefold()
    if not query_cf:
        await safe_send_text("Введите часть ключа для поиска.", chat_id)
        return
    matches = [item for item in KEYWORDS if query_cf in item.casefold()]
    if not matches:
        await safe_send_text("Ничего не нашёл.", chat_id)
        return
    lines = [f"{index + 1}. {html.escape(value)}" for index, value in enumerate(matches[:50])]
    await safe_send_text("Нашёл:\n\n" + "\n".join(lines), chat_id)


async def send_stats(chat_id: int) -> None:
    await safe_send_text(
        "Статус:\n"
        f"Ключей: {len(KEYWORDS)}\n"
        f"Каналов: {len(CHANNEL_ENTITIES) or len(CHANNELS)}\n"
        f"Однословных лемм: {len(SINGLE_WORD_LEMMAS)}\n"
        f"Фраз: {len(PHRASES_LC)}\n"
        f"Обработано в памяти: {len(PROCESSED_LOOKUP)}",
        chat_id,
    )


def reload_keywords_from_file() -> None:
    RAW_KEYWORDS[:] = load_json(KEYWORDS_PATH)
    rebuild_keyword_index()


async def handle_callback(chat_id: int, callback: Any) -> None:
    data = callback.data or ""
    if data == "kw:add":
        ADMIN_MODES[chat_id] = "add"
        await answer_callback(callback, "Отправьте новый ключ")
        await safe_send_text("Отправьте ключевое слово или фразу одним сообщением.", chat_id)
    elif data == "kw:delete":
        ADMIN_MODES[chat_id] = "delete"
        await answer_callback(callback, "Отправьте ключ для удаления")
        await safe_send_text("Отправьте точный ключ, который нужно удалить.", chat_id)
    elif data == "kw:rename":
        ADMIN_MODES[chat_id] = "rename"
        await answer_callback(callback, "Формат: старое => новое")
        await safe_send_text("Отправьте изменение в формате: старое => новое", chat_id)
    elif data == "kw:search":
        ADMIN_MODES[chat_id] = "search"
        await answer_callback(callback, "Отправьте строку поиска")
        await safe_send_text("Отправьте часть ключевого слова для поиска.", chat_id)
    elif data == "kw:list":
        await answer_callback(callback)
        await send_keyword_list(chat_id)
    elif data == "kw:stats":
        await answer_callback(callback)
        await send_stats(chat_id)
    elif data == "kw:reload":
        reload_keywords_from_file()
        await answer_callback(callback)
        await safe_send_text("Перезагрузил keywords.json.", chat_id)


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
                        await handle_admin_text(chat_id, update.message.text)
                    else:
                        await safe_send_text("Нет доступа к управлению ботом.", chat_id)
        except Exception as exc:
            log.warning("bot_control_loop: %s", exc)
            await asyncio.sleep(BOT_CONTROL_INTERVAL)


async def build_filters() -> Tuple[Dict[str, dict], Set[int], Set[str], Set[str]]:
    entities = {}
    ids = set()
    usernames = set()
    id_strings = set()

    for channel in CHANNELS:
        try:
            if "id" in channel:
                entity = await client.get_input_entity(channel["id"])
                key = str(channel["id"])
            else:
                link = channel["link"]
                if "joinchat" in link or "t.me/+" in link:
                    entity = await resolve_link_once(link)
                    key = link
                else:
                    username = link.rsplit("/", 1)[-1].lstrip("@")
                    entity = await resolve_username_once(username)
                    key = username
                    usernames.add(username.lower())

            entities[key] = {
                "entity": entity,
                "custom_text": channel.get("custom_text", ""),
                "name": channel.get("name", "Unknown"),
            }
            peer_id = get_peer_id(entity)
            ids.add(peer_id)
            id_strings.add(str(peer_id))

            if peer_id not in LAST_SEEN_ID:
                try:
                    async for message in client.iter_messages(entity, limit=1):
                        LAST_SEEN_ID[peer_id] = message.id
                        break
                except Exception:
                    LAST_SEEN_ID[peer_id] = 0
        except Exception as exc:
            log.error("Не удалось получить канал %s: %s", channel, exc)

    save_state()
    return entities, ids, usernames, id_strings


async def main() -> None:
    rebuild_keyword_index()
    load_state()

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

    retry_queue = []
    for channel in CHANNELS:
        ok = await join_channel(channel)
        if not ok:
            retry_queue.append((channel, 1))
        await asyncio.sleep(0.2)

    for channel, attempt in retry_queue:
        while attempt <= 3:
            ok = await join_channel(channel)
            if ok:
                break
            attempt += 1
            await asyncio.sleep(30)
        if attempt > 3:
            log.warning("Пропускаю канал после 3 попыток: %s", channel)

    global CHANNEL_ENTITIES, ALLOWED_IDS, ALLOWED_USERNAMES, ALLOWED_ID_STRINGS
    CHANNEL_ENTITIES, ALLOWED_IDS, ALLOWED_USERNAMES, ALLOWED_ID_STRINGS = await build_filters()

    log.info("Слушаем каналы: %s", ", ".join(CHANNEL_ENTITIES.keys()))

    try:
        await client.get_dialogs(limit=0)
    except Exception as exc:
        log.warning("get_dialogs для синхронизации: %s", exc)

    asyncio.create_task(keep_updates_alive())
    asyncio.create_task(polling_loop())
    asyncio.create_task(bot_control_loop())

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

        if not event.message or not event.message.text:
            return

        await process_and_maybe_forward(chat, event.message)

    log.info("Бот запущен. Управление ключами доступно через /menu у админов.")
    try:
        await client.run_until_disconnected()
    except Exception as exc:
        log.error("Ошибка выполнения: %s", exc)


if __name__ == "__main__":
    asyncio.run(main())
