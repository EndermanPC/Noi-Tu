# Copyright (c) 2025 EndermanPC - Bùi Nguyễn Tấn Sang

import discord
from discord.ext import commands
from discord.utils import format_dt
import asyncio
import unicodedata
import sqlite3
import json
import os
import random
import re
import logging
import calendar
import time
from datetime import datetime, timedelta
from collections import defaultdict
import requests
from urllib.parse import quote
from wordfreq import word_frequency
from functools import lru_cache
import secrets

# ====== CONFIGURATION ======
ADMIN = 999999999999999999
banned_users = set()
DB_PATH = "databases.db"

# ====== LOGGING ======
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# ====== DISCORD BOT INITIALIZATION ======
intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix="NT", intents=intents)

# ====== UTILITY LOCKS & GLOBALS ======
channel_locks = {}  # channel_id -> asyncio.Lock()
game_state = {}  # channel_id -> dict (normal games)
match_state = {}  # channel_id -> match info (tournament games)
user_stats = {}  # user_id(str) -> {"rank": int, "solan": int, "streak": int}
hall_of_fame = {}  # team_name -> {"points": int, "streak": int, "members": [user_ids]}
season_info = {
    "seasons": 1,
    "start": datetime.utcnow().isoformat(),
    "end": (datetime.utcnow() + timedelta(days=90)).isoformat()
}

# ====== BOT PLAY SYSTEM ======
# Zobrist hashing tables
_ZOBRIST_PHRASE_TABLE = {}
_ZOBRIST_LAST_WORD = {}
_ZOBRIST_SIDE = {"bot": secrets.randbits(64), "player": secrets.randbits(64)}

def _zobrist_key(last_word, used_phrases_frozen, turn):
    h = 0
    # last word
    h ^= _ZOBRIST_LAST_WORD.setdefault(last_word, secrets.randbits(64))
    # used phrases
    for phrase in used_phrases_frozen:
        h ^= _ZOBRIST_PHRASE_TABLE.setdefault(phrase, secrets.randbits(64))
    # turn
    h ^= _ZOBRIST_SIDE.get(turn, 0)
    return h

# ====== PHRASE DICTIONARY ======
VALID_PHRASES = set()
FIRST_WORDS = {}
WORD_TRAP_SCORES = {}

# ====== ANTI CHEAT SYSTEM ======
last_action_time = {}
violation_count = defaultdict(int)
ANTI_SCRIPT_INTERVAL = timedelta(seconds=6.0)
MAX_VIOLATIONS = 5

# ====== DATABASES ======

def init_db():
    try:
        with sqlite3.connect(DB_PATH) as conn:
            cur = conn.cursor()
            # Dictionary
            cur.execute("""
                CREATE TABLE IF NOT EXISTS phrases (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    word1 TEXT NOT NULL,
                    word2 TEXT NOT NULL,
                    full_phrase TEXT UNIQUE NOT NULL,
                    freq REAL DEFAULT 0.0
                )
            """)
            cur.execute("CREATE INDEX IF NOT EXISTS idx_word1 ON phrases(word1)")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_word2 ON phrases(word2)")
            # Seasons
            cur.execute("""
                CREATE TABLE IF NOT EXISTS season_info (
                    id INTEGER PRIMARY KEY CHECK (id = 1),
                    seasons INTEGER DEFAULT 1,
                    start TEXT NOT NULL,
                    end TEXT NOT NULL
                )
            """)
            # Rank and Hall of Fame
            cur.execute("""
                CREATE TABLE IF NOT EXISTS user_stats (
                    user_id TEXT PRIMARY KEY,
                    rank INTEGER DEFAULT 0,
                    solan INTEGER DEFAULT 0,
                    streak INTEGER DEFAULT 0
                )
            """)
            cur.execute("""
                CREATE TABLE IF NOT EXISTS hall_of_fame (
                    team_name TEXT PRIMARY KEY,
                    points INTEGER DEFAULT 0,
                    streak INTEGER DEFAULT 0,
                    members TEXT DEFAULT '[]'
                )
            """)
    except Exception as e:
        logging.error(f"Error initializing database: {e}")

def load_season_info():
    global season_info
    if os.path.exists(DB_PATH):
        try:
            with sqlite3.connect(DB_PATH) as conn:
                cur = conn.cursor()
                cur.execute("SELECT seasons, start, end FROM season_info WHERE id = 1")
                row = cur.fetchone()
                if row:
                    seasons, start, end = row
                    season_info = {
                        "seasons": seasons,
                        "start": start,
                        "end": end
                    }
                else:
                    # Nếu chưa có dữ liệu, khởi tạo mặc định
                    season_info = {
                        "seasons": 1,
                        "start": "2025-07-28T00:00:00",
                        "end": "2025-08-01T00:00:00"
                    }
                    save_season_info()
        except Exception as e:
            logging.error(f"Error loading season from database: {e}")

def save_season_info():
    try:
        with sqlite3.connect(DB_PATH) as conn:
            cur = conn.cursor()
            cur.execute("""
                INSERT INTO season_info (id, seasons, start, end)
                VALUES (1, ?, ?, ?)
                ON CONFLICT(id) DO UPDATE SET
                    seasons = excluded.seasons,
                    start = excluded.start,
                    end = excluded.end
            """, (
                season_info["seasons"],
                season_info["start"],
                season_info["end"]
            ))
    except Exception as e:
        logging.error(f"Error saving season to database: {e}")

def load_user_stats():
    global user_stats
    if os.path.exists(DB_PATH):
        try:
            user_stats.clear()
            with sqlite3.connect(DB_PATH) as conn:
                cur = conn.cursor()
                for uid, rank, solan, streak in cur.execute("SELECT * FROM user_stats"):
                    user_stats[uid] = {"rank": rank, "solan": solan, "streak": streak}
            is_changed = False
            for uid in list(user_stats.keys()):
                if not isinstance(uid, str):
                    user_stats[str(uid)] = user_stats.pop(uid)
                    is_changed = True
            if is_changed:
                save_user_stats()
        except Exception as e:
            logging.error(f"Error loading rank from database: {e}")
            user_stats = {}
    else:
        logging.info("Database file not found.")
        user_stats = {}

def save_user_stats():
    if os.path.exists(DB_PATH):
        try:
            with sqlite3.connect(DB_PATH) as conn:
                cur = conn.cursor()
                for uid, data in user_stats.items():
                    cur.execute("""
                        INSERT INTO user_stats (user_id, rank, solan, streak)
                        VALUES (?, ?, ?, ?)
                        ON CONFLICT(user_id) DO UPDATE SET
                            rank=excluded.rank, solan=excluded.solan, streak=excluded.streak
                    """, (uid, data["rank"], data["solan"], data["streak"]))
        except Exception as e:
            logging.error(f"Error saving rank to database: {e}")

def load_hall_of_fame():
    global hall_of_fame
    if os.path.exists(DB_PATH):
        try:
            hall_of_fame.clear()
            with sqlite3.connect(DB_PATH) as conn:
                cur = conn.cursor()
                for team_name, points, streak, members_json in cur.execute("SELECT * FROM hall_of_fame"):
                    members = json.loads(members_json)
                    members = [str(m) for m in members]
                    hall_of_fame[team_name] = {
                        "points": points,
                        "streak": streak,
                        "members": members
                    }
            is_changed = False
            for team, info in list(hall_of_fame.items()):
                normalized_members = [str(m) for m in info["members"]]
                if normalized_members != info["members"]:
                    hall_of_fame[team]["members"] = normalized_members
                    is_changed = True
            if is_changed:
                save_hall_of_fame()
        except Exception as e:
            logging.error(f"Error loading teams from database: {e}")
            hall_of_fame = {}
    else:
        logging.info("Database file not found.")
        hall_of_fame = {}

def save_hall_of_fame():
    try:
        with sqlite3.connect(DB_PATH) as conn:
            cur = conn.cursor()
            for team, data in hall_of_fame.items():
                members_as_str = [str(m) for m in data["members"]]
                cur.execute("""
                    INSERT INTO hall_of_fame (team_name, points, streak, members)
                    VALUES (?, ?, ?, ?)
                    ON CONFLICT(team_name) DO UPDATE SET
                        points=excluded.points, streak=excluded.streak, members=excluded.members
                """, (team, data["points"], data["streak"], json.dumps(members_as_str)))
    except Exception as e:
        logging.error(f"Error saving teams to database: {e}")

def load_dictionary_from_db():
    global VALID_PHRASES, FIRST_WORDS
    if os.path.exists(DB_PATH):
        try:
            VALID_PHRASES.clear()
            FIRST_WORDS.clear()

            with sqlite3.connect(DB_PATH) as conn:
                cur = conn.cursor()
                for full_phrase, w1, w2 in cur.execute("SELECT full_phrase, word1, word2 FROM phrases"):
                    VALID_PHRASES.add(full_phrase)
                    FIRST_WORDS.setdefault(w1, set()).add(w2)
        except Exception as e:
            logging.error(f"Error loading dictionary from database: {e}")
    else:
        logging.info("Database file not found.")
        VALID_PHRASES = {}

def add_phrase_to_db(phrase):
    try:
        phrase = normalize_phrase(phrase)
        words = phrase.split()
        if len(words) != 2:
            return False
        w1, w2 = words
        freq = word_frequency(phrase, "vi", wordlist="best")
        try:
            with sqlite3.connect(DB_PATH) as conn:
                conn.execute("""
                    INSERT OR IGNORE INTO phrases (word1, word2, full_phrase, freq)
                    VALUES (?, ?, ?, ?)
                """, (w1, w2, phrase, freq))
            return True
        except:
            return False
    except Exception as e:
        logging.error(f"Error adding phrase to database: {e}")

def remove_phrase_from_db(phrase):
    try:
        phrase = normalize_phrase(phrase)
        words = phrase.split()
        if len(words) != 2:
            return False
        w1, w2 = words
        with sqlite3.connect(DB_PATH) as conn:
            conn.execute("DELETE FROM phrases WHERE full_phrase = ?", (phrase,))
            if w1 in FIRST_WORDS and w2 in FIRST_WORDS[w1]:
                FIRST_WORDS[w1].remove(w2)
                if not FIRST_WORDS[w1]:
                    del FIRST_WORDS[w1]
        return True
    except Exception as e:
        logging.error(f"Error removing phrase from database: {e}")
        return False
    
def get_phrase_freq(phrase: str) -> float:
    with sqlite3.connect(DB_PATH) as conn:
        cur = conn.cursor()
        cur.execute("SELECT freq FROM phrases WHERE full_phrase = ?", (phrase,))
        row = cur.fetchone()
        return row[0] if row else 0.0
    
def precompute_trap_scores():
    global WORD_TRAP_SCORES
    WORD_TRAP_SCORES.clear()
    for word, next_words_set in FIRST_WORDS.items():
        WORD_TRAP_SCORES[word] = len(next_words_set)
    logging.info(f"Precomputed trap scores for {len(WORD_TRAP_SCORES)} words.")

# ====== INIT ======
# Sqlite database initialization
init_db()

load_dictionary_from_db()
precompute_trap_scores()
load_season_info()
load_hall_of_fame()
load_user_stats()

# ====== HELPERS ======

def reset_streak_for_all(channel_id):
    state = game_state.get(channel_id) or match_state.get(channel_id)
    if not state:
        return
    affected = set(state.get("players", []))
    if "surrender_votes" in state:
        affected.update(state.get("surrender_votes", set()))
    for uid in affected:
        uid_str = str(uid)
        if uid_str in user_stats:
            user_stats[uid_str]["streak"] = 0
    save_user_stats()

def normalize_phrase(phrase):
    return unicodedata.normalize("NFC", phrase.strip().lower())

def is_valid_vietnamese_phrase(phrase):
    words = phrase.split()
    if len(words) != 2:
        return False
    return all(c.isalpha() or c.isspace() for c in phrase)

def check_word_in_online(word):
    encoded_word = quote(word)
    # Tratu Soha
    url_tratu = f"http://tratu.soha.vn/dict/vn_vn/{encoded_word}"
    # Wiktionary
    url_wiktionary = f"https://vi.wiktionary.org/wiki/{encoded_word}"
    # Wikipedia
    url_wikipedia = f"https://vi.wikipedia.org/wiki/{encoded_word}"

    try:
        # Check Tratu Soha
        response = requests.get(url_tratu, timeout=5)
        if response.status_code != 404 and "(Trang này hiện chưa có gì)" not in response.text:
            return True
        
        # Check Wiktionary
        response = requests.get(url_wiktionary, timeout=5)
        if response.status_code != 404 and "Wiktionary tiếng Việt chưa có mục từ nào có tên này." not in response.text:
            return True

        # Check Wikipedia
        response = requests.get(url_wikipedia, timeout=5)
        if response.status_code != 404 and "Wikipedia hiện chưa có bài viết nào với tên này." not in response.text:
            return True

        return False
    except Exception as e:
        logging.error(f"Error accessing online dictionaries: {e}")
        return False

def select_balanced_start_phrase(max_samples=50, forced_win_lookahead=5, time_budget=0.3):
    start_time = time.monotonic()
    candidates = []
    all_phrases = list(VALID_PHRASES)
    random.shuffle(all_phrases)
    checked = 0

    def player_has_quick_win(w2, w1):
        history = [w1, w2]
        used_phrases = frozenset(f"{w1} {w2}")
        last_word = w2
        can_win, depth = insane_search(
            last_word,
            used_phrases,
            set(history),
            'bot',
            forced_win_lookahead,
            {}
        )
        return can_win

    while checked < max_samples and time.monotonic() - start_time < time_budget and checked < len(all_phrases):
        phrase = all_phrases[checked]
        checked += 1
        w1, w2 = phrase.split()
        has_continuation = any(
            f"{w2} {next_w}" in VALID_PHRASES and next_w != w1
            for next_w in FIRST_WORDS.get(w2, set())
        )
        if not has_continuation:
            continue

        if player_has_quick_win(w2, w1):
            continue

        candidates.append(phrase)
        if len(candidates) >= 1:
            break

    if candidates:
        return random.choice(candidates)

    attempts = 0
    max_attempts = 100
    selected_phrase = None
    while attempts < max_attempts:
        phrase = random.choice(list(VALID_PHRASES))
        w1, w2 = phrase.split()
        has_continuation = any(
            f"{w2} {next_w}" in VALID_PHRASES and next_w != w1
            for next_w in FIRST_WORDS.get(w2, set())
        )
        if has_continuation:
            selected_phrase = phrase
            break
        attempts += 1
    return selected_phrase

def select_start_phrase(
    *,
    max_samples=50,
    forced_win_lookahead=5,
    time_budget=0.1,
    safety_filter=True
):
    if safety_filter:
        return select_balanced_start_phrase(
            max_samples=max_samples,
            forced_win_lookahead=forced_win_lookahead,
            time_budget=time_budget
        )
    attempts = 0
    max_attempts = 100
    while attempts < max_attempts:
        phrase = random.choice(list(VALID_PHRASES))
        w1, w2 = phrase.split()
        has_continuation = any(
            f"{w2} {next_w}" in VALID_PHRASES and next_w != w1
            for next_w in FIRST_WORDS.get(w2, set())
        )
        if has_continuation:
            return phrase
        attempts += 1
    return None

def is_tournament(ctx_or_message):
    channel = getattr(ctx_or_message, "channel", ctx_or_message)
    return hasattr(channel, "id") and channel.id in match_state and match_state[channel.id].get("mode") == "tournament"

def check_auto_play(user_id: str):
    now = datetime.utcnow()
    last = last_action_time.get(user_id)
    if last and (now - last) < ANTI_SCRIPT_INTERVAL:
        violation_count[user_id] += 1
        if violation_count[user_id] >= MAX_VIOLATIONS:
            banned_users.add(user_id)
            return "banned"
        return "warning"
    last_action_time[user_id] = now
    return "ok"

def phrase_score(phrase):
    freq = get_phrase_freq(phrase)
    if freq == 0.0:
        return 0.0
    elif freq >= 1e-4:
        return 1.0
    else:
        return round(min(1.0, freq / 1e-5), 3)

def classify_phrase(freq):
    if freq == 0.0:
        return "🔴 Cực kì hiếm"
    elif freq < 1e-6:
        return "🟠 Rất hiếm"
    elif freq < 1e-5:
        return "🟡 Hiếm"
    elif freq < 1e-4:
        return "🟢 Tương đối phổ biến"
    else:
        return "🔵 Phổ biến"

def is_rare_phrase_robust(phrase, lang='vi', phrase_thresh=1e-7, word_thresh=1e-6):
    freq_phrase = get_phrase_freq(phrase)
    words = phrase.strip().lower().split()
    if len(words) != 2:
        return True, freq_phrase, [], 0.0, ""
    freq1 = word_frequency(words[0], lang, wordlist='best')
    freq2 = word_frequency(words[1], lang, wordlist='best')
    is_rare = (freq_phrase < phrase_thresh) and (freq1 < word_thresh or freq2 < word_thresh)
    score = phrase_score(phrase)
    label = classify_phrase(freq_phrase)
    return is_rare, freq_phrase, [freq1, freq2], score, label

def mutual_exclusion_check(channel_id):
    # Only one mode can exist per channel
    if channel_id in game_state:
        del game_state[channel_id]
    if channel_id in match_state:
        del match_state[channel_id]

def to_roman(n):
    roman_map = [
        (1000, 'M'), (900, 'CM'), (500, 'D'), (400, 'CD'),
        (100, 'C'), (90, 'XC'), (50, 'L'), (40, 'XL'),
        (10, 'X'), (9, 'IX'), (5, 'V'), (4, 'IV'), (1, 'I')
    ]
    result = ''
    for (arabic, roman) in roman_map:
        while n >= arabic:
            result += roman
            n -= arabic
    return result

# ====== BOT EVENTS ======

@bot.event
async def on_ready():
    print(f"Logged in as {bot.user.name}")
    await bot.change_presence(activity=discord.Game(name="Nối Từ - NTstart để chơi!"))

@bot.event
async def on_command_error(ctx, error):
    if isinstance(error, commands.CommandNotFound):
        return
    raise error

@bot.event
async def on_message(message):
    await bot.process_commands(message)
    if message.author.bot or message.content.startswith(bot.command_prefix):
        return
    if message.channel.id not in game_state and message.channel.id not in match_state:
        return

    # Concurrency: lock per channel
    lock = channel_locks.setdefault(message.channel.id, asyncio.Lock())
    async with lock:
        # Determine mode
        state = None
        tournament = is_tournament(message)
        if tournament:
            state = match_state.get(message.channel.id)
        else:
            state = game_state.get(message.channel.id)
        if not state:
            return

        # Normalize input
        text = normalize_phrase(re.sub(r"[^\w\s]", "", message.content))
        words = text.split()
        if len(words) != 2:
            return
        
        author_id_str = str(message.author.id)

        # Ban and surrender validation
        if author_id_str in banned_users:
            await message.add_reaction("🚫")
            await message.channel.send("🚫 Bạn đã bị cấm chơi trò này. Vui lòng bổ túc một khóa Tiếng Việt để tham gia.")
            return
        if "surrender_votes" in state and author_id_str in state["surrender_votes"]:
            await message.add_reaction("🚫")
            await message.channel.send("🚫 Bạn đã đầu hàng và không thể chơi cho đến khi bắt đầu trò chơi mới.")
            return

        user_stats.setdefault(author_id_str, {"rank": 0, "solan": 0, "streak": 0})

        # Tournament: team and turn checks
        if tournament:
            user_team = None
            for t, info in hall_of_fame.items():
                if author_id_str in info["members"]:
                    user_team = t
                    break
            if not user_team or user_team not in state["teams"]:
                return
            if user_team != state["current_team"]:
                await message.add_reaction("🚫")
                await message.channel.send("🚫 Đến lượt đội khác chơi.")
                return
        else:
            # Consecutive turns check (except single-player)
            if author_id_str == state.get("last_player_id"):
                if len(state["players"]) < 2:
                    await message.channel.send("⚠️ Chế độ luyện tập. Chờ người khác để vào xếp hạng.")
                    pass
                else:
                    await message.add_reaction("⏭️")
                    await message.channel.send("🚫 Không được chơi hai lượt liên tiếp.")
                    return

        # First word check
        if words[0] != state["last_word"]:
            await message.add_reaction("🔄")
            await message.channel.send(f"⚠️ Chữ đầu phải là `{state['last_word']}`.")
            user_stats[author_id_str]["streak"] = 0
            if tournament:
                hall_of_fame[user_team]["streak"] = 0
                save_hall_of_fame()
            save_user_stats()
            return

        phrase = f"{words[0]} {words[1]}"

        # Dictionary check
        if phrase not in VALID_PHRASES:
            if not check_word_in_online(phrase):
                await message.add_reaction("❌")
                await message.channel.send(f"❌ Cụm từ `{phrase}` không có trong từ điển.")
                user_stats[author_id_str]["streak"] = 0
                if tournament:
                    hall_of_fame[user_team]["streak"] = 0
                    save_hall_of_fame()
                save_user_stats()
                return
            else:
                try:
                    w1w2 = phrase.split()
                    if len(w1w2) == 2:
                        w1, w2 = w1w2
                        VALID_PHRASES.add(phrase)
                        FIRST_WORDS.setdefault(w1, set()).add(w2)
                        if add_phrase_to_db(phrase):
                            await message.channel.send(
                                f"⚠️ Cụm từ `{phrase}` không có trong từ điển hiện tại nhưng có trên từ điển trực tuyến. Đã thêm vào từ điển!"
                            )
                            logging.info(f"Added phrase from online: {phrase}")
                        else:
                            await message.channel.send("❌ Lỗi khi thêm cụm từ vào từ điển.")
                except Exception as e:
                    await message.channel.send("❌ Lỗi khi thêm cụm từ vào từ điển.")
                    logging.error(f"Error adding phrase: {e}")     

        # Check duplicate phrase/word in history
        history_phrases = {" ".join(state["history"][i:i+2]) for i in range(len(state["history"]) - 1)}
        history_words = set(state["history"])
        if phrase in history_phrases:
            await message.add_reaction("⚠️")
            await message.channel.send("🔁 Cụm từ đã dùng trong lượt này.")
            user_stats[author_id_str]["streak"] = 0
            if tournament:
                hall_of_fame[user_team]["streak"] = 0
                save_hall_of_fame()
            save_user_stats()
            return
        if words[1] in history_words:
            await message.add_reaction("♻️")
            await message.channel.send("🔁 Từ này đã được dùng làm chữ cuối.")
            user_stats[author_id_str]["streak"] = 0
            if tournament:
                hall_of_fame[user_team]["streak"] = 0
                save_hall_of_fame()
            save_user_stats()
            return

        await message.add_reaction("✅")
        state["history"].append(words[1])
        state["last_word"] = words[1]
        state["last_player_id"] = author_id_str
        if author_id_str not in state["players"]:
            state["players"].append(author_id_str)

        # Tournament: switch team
        if tournament:
            hall_of_fame[user_team]["streak"] += 1
            teams = state["teams"]
            state["current_team"] = teams[1] if state["current_team"] == teams[0] else teams[0]

        # Stats update
        user_stats[author_id_str]["solan"] += 1
        user_stats[author_id_str]["streak"] += 1

        # Next move calculation
        possible_next_phrases = []
        for next_w in FIRST_WORDS.get(words[1], set()):
            potential_phrase = f"{words[1]} {next_w}"
            if (
                potential_phrase in VALID_PHRASES and
                potential_phrase not in history_phrases and
                next_w not in history_words and
                words[1] != next_w
            ):
                possible_next_phrases.append(potential_phrase)

        # Anti-cheat
        result = check_auto_play(author_id_str)
        if result == "banned":
            await message.channel.send(f"🚫 <@{author_id_str}> đã bị cấm vì nghi dùng auto!")
            return
        elif result == "warning":
            await message.channel.send("⚠️ Bạn đang chơi quá nhanh, có thể bị cấm nếu tiếp tục.")

        is_rare, freq, word_freqs, score, label = is_rare_phrase_robust(phrase)
        if score < 0.5:
            await message.channel.send(
                f"⚠️ Cảnh báo cụm tự lạ hoặc hiếm từ <@{author_id_str}>:\n"
                f" - Cụm từ `{phrase}` có tần suất thấp: {freq:.2e} ({label}).\n"
                f" - Tần suất từng từ:  {[f'{w:.2e}' for w in word_freqs]}\n"
                f" - Điểm số phổ biến: {score}"
            )
            if is_rare and author_id_str not in banned_users:
                violation_count[author_id_str] += 1
                await message.channel.send(f"❗ **Cảnh cáo hành vi gian lận từ <@{author_id_str}>**: Cụm từ `{phrase}` có tần suất rất thấp. Tổng vi phạm là {violation_count[author_id_str]}")
                if violation_count[author_id_str] >= MAX_VIOLATIONS:
                    banned_users.add(author_id_str)
                    user_stats[author_id_str]["rank"] = max(0, user_stats[author_id_str]["rank"] - 5)
                    await message.channel.send(f"🚫 <@{author_id_str}> đã bị **cấm tạm thời** vì gian lận!")
                    # If no possible next phrases, award win to previous player
                    if not possible_next_phrases:
                        # Find previous player (before banned user)
                        prev_player_id = None
                        if len(state["players"]) >= 2:
                            # The last player is the cheater, so previous is -2
                            prev_player_id = state["players"][-2]
                        if prev_player_id:
                            prev_player_id_str = str(prev_player_id)
                            user_stats.setdefault(prev_player_id_str, {"rank": 0, "solan": 0, "streak": 0})
                            bonus = 1
                            if user_stats[prev_player_id_str]["streak"] >= 5:
                                bonus += 1
                                bonus += (user_stats[prev_player_id_str]["streak"] // 5) - 1
                            user_stats[prev_player_id_str]["rank"] += bonus
                            user_stats[prev_player_id_str]["streak"] = 0
                            reset_streak_for_all(message.channel.id)
                            save_user_stats()
                            await message.channel.send(
                                f"🏁 Không còn từ để nối!\n🎉 Người chơi <@{prev_player_id_str}> thắng và được +{bonus} điểm (do người chơi sau bị ban)!"
                            )
                        else:
                            await message.channel.send(
                                "🏁 Không còn từ để nối!\n🎉 Không có người chơi nào thắng vì không đủ người chơi."
                            )
                        # End game
                        if message.channel.id in game_state:
                            del game_state[message.channel.id]
                    else:
                        if tournament:
                            save_hall_of_fame()
                        save_user_stats()
                        state["possible_phrases"] = possible_next_phrases
                        if state.get("with_bot"):
                            bot_choice = await choose_bot_phrase(state["last_word"], set(state["history"]), {" ".join(state["history"][i:i+2]) for i in range(len(state["history"]) - 1)}, state.get("bot_difficulty", "medium"))
                            if bot_choice:
                                _, bot_next = bot_choice.split()
                                state["history"].append(bot_next)
                                prev_last = state["last_word"]
                                state["last_word"] = bot_next
                                state["last_player_id"] = str(bot.user.id)
                                new_possible = []
                                for next_w in FIRST_WORDS.get(bot_next, set()):
                                    potential = f"{bot_next} {next_w}"
                                    if (
                                        potential in VALID_PHRASES and
                                        potential not in {" ".join(state["history"][i:i+2]) for i in range(len(state["history"]) - 1)} and
                                        next_w not in set(state["history"]) and
                                        bot_next != next_w
                                    ):
                                        new_possible.append(potential)
                                state["possible_phrases"] = new_possible
                                await message.channel.send(f"🤖 Bot nối: `{bot_choice}`")
                                if not new_possible:
                                    await message.channel.send("😅 Bot đã chặn bạn. Chúc may mắn lần sau!")
                                    user_id = str(message.author.id)
                                    user_stats.setdefault(user_id, {"rank":0,"solan":0,"streak":0})
                                    user_stats[user_id]["streak"] = 0
                                    reset_streak_for_all(message.channel.id)
                                    save_user_stats()
                                    del game_state[message.channel.id]
                                    return
                        await message.channel.send(f"🤣 Còn {len(new_possible) if state.get('with_bot') else len(possible_next_phrases)} từ để nối tiếp.")
                    return

        # Win detection
        if not possible_next_phrases:
            if tournament:
                # The winning team is the current (before switch)
                winner_team = None
                teams = state["teams"]
                winner_team = teams[1] if state["current_team"] == teams[0] else teams[0]
                await end_match(message, winner_team)
                return
            # Pratice mode
            if len(state["players"]) < 2 or (len(state["players"]) == 2 and str(bot.user.id) in state["players"] and len(state["history"]) <= 3):
                await message.channel.send(
                    f"🏁 Không còn từ để nối!\n🎉 Người chơi <@{author_id_str}> thắng!"
                )
                user_stats[author_id_str]["streak"] = 0
                reset_streak_for_all(message.channel.id)
                save_user_stats()
                del game_state[message.channel.id]
                return
            # Normal mode
            bonus = 1
            if user_stats[author_id_str]["streak"] >= 5:
                bonus += 1
                bonus += (user_stats[author_id_str]["streak"] // 5) - 1
            user_stats[author_id_str]["rank"] += bonus
            user_stats[author_id_str]["streak"] = 0
            reset_streak_for_all(message.channel.id)
            save_user_stats()
            await message.channel.send(
                f"🏁 Không còn từ để nối!\n🎉 Người chơi <@{author_id_str}> thắng và được +{bonus} điểm!"
            )
            del game_state[message.channel.id]
        else:
            if tournament:
                save_hall_of_fame()
            save_user_stats()
            state["possible_phrases"] = possible_next_phrases
            if state.get("with_bot"):
                bot_choice = await choose_bot_phrase(state["last_word"], set(state["history"]), {" ".join(state["history"][i:i+2]) for i in range(len(state["history"]) - 1)}, state.get("bot_difficulty", "medium"))
                if bot_choice:
                    _, bot_next = bot_choice.split()
                    state["history"].append(bot_next)
                    prev_last = state["last_word"]
                    state["last_word"] = bot_next
                    state["last_player_id"] = str(bot.user.id)
                    new_possible = []
                    for next_w in FIRST_WORDS.get(bot_next, set()):
                        potential = f"{bot_next} {next_w}"
                        if (
                            potential in VALID_PHRASES and
                            potential not in {" ".join(state["history"][i:i+2]) for i in range(len(state["history"]) - 1)} and
                            next_w not in set(state["history"]) and
                            bot_next != next_w
                        ):
                            new_possible.append(potential)
                    state["possible_phrases"] = new_possible
                    await message.channel.send(f"🤖 Bot nối: `{bot_choice}`")
                    if not new_possible:
                        await message.channel.send("😅 Bot đã chặn bạn. Chúc may mắn lần sau!")
                        user_id = str(message.author.id)
                        user_stats.setdefault(user_id, {"rank":0,"solan":0,"streak":0})
                        user_stats[user_id]["streak"] = 0
                        reset_streak_for_all(message.channel.id)
                        save_user_stats()
                        del game_state[message.channel.id]
                        return
            await message.channel.send(f"🤣 Còn {len(new_possible) if state.get('with_bot') else len(possible_next_phrases)} từ để nối tiếp.")

# --- BOT PLAY SYSTEM ---
def get_valid_next_phrases(last_word, used_phrases, history_words):
    candidates = []
    for next_w in FIRST_WORDS.get(last_word, set()):
        potential = f"{last_word} {next_w}"
        if (
            potential in VALID_PHRASES and
            potential not in used_phrases and
            next_w not in history_words and
            last_word != next_w
        ):
            candidates.append(potential)
    return candidates

def evaluate_heuristic(last_word, candidates):
    # Weights to balance elements, can be tweaked later
    W_MOBILITY = 0.3
    W_TRAP = 0.5
    W_RARITY = 10000.0 # Very low frequency, need large weighting

    # Mobility: Number of possible moves
    mobility_score = len(candidates)

    # Trap Score: Number of escape routes of the last word
    # The more escape routes the word has, the safer it is
    trap_score = WORD_TRAP_SCORES.get(last_word, 0)

    # Rarity: Frequency of the final word
    # The rarer the word (lower frequency), the more difficult it is for the opponent
    rarity_score = word_frequency(last_word, 'vi', wordlist='best')

    # Summary formula:
    # - More options (mobility) the better
    # - More safety (high trap_score) the better
    # - More rarity (low rarity_score) the better
    final_score = (W_MOBILITY * mobility_score) + (W_TRAP * trap_score) - (W_RARITY * rarity_score)
    
    # Normalize the scores to a small range so as not to affect the absolute win/loss scores (-1 and 1)
    return final_score / 100.0

def negamax(last_word, used_phrases, history_words, depth, alpha, beta, turn, memo):
    # Check the Transposition Table using Zobrist key 
    key = _zobrist_key(last_word, frozenset(used_phrases), turn)
    if key in memo and memo[key]["depth"] >= depth:
        return memo[key]["value"]

    # Check the end state (win/lose)
    # This is the most important stopping point of the recursion.
    candidates = get_valid_next_phrases(last_word, frozenset(used_phrases), history_words)
    if not candidates:
        # If it is the current player's turn and he does not make a move, he loses.
        # A score of -1 represents a certain loss.
        return -1

    # Check if maximum search depth reached
    if depth == 0:
        # Using advanced heuristics to evaluate the position at the leaf
        return evaluate_heuristic(last_word, candidates)

    # Start recursive search
    best_value = -float("inf")
    next_turn = "player" if turn == "bot" else "bot"

    # Arrange moves to increase the effectiveness of Alpha-Beta pruning (optional but recommended)
    # Prioritize moves that limit your opponent's options
    def ordering_score(phrase):
        _, next_word = phrase.split()
        opp_candidates = get_valid_next_phrases(next_word, frozenset(used_phrases | {phrase}), history_words | {next_word})
        return len(opp_candidates)
    
    candidates.sort(key=ordering_score)

    # Loop through possible moves
    for phrase in candidates:
        _, next_word = phrase.split()
        
        # Create new state for next move
        new_used_phrases = used_phrases | {phrase}
        new_history_words = history_words | {next_word}

        # Recursively call Negamax for next move
        # The leading minus sign is the core of the Negamax algorithm
        val = -negamax(next_word, new_used_phrases, new_history_words, depth - 1, -beta, -alpha, next_turn, memo)

        # Update best value and perform Alpha-Beta pruning
        if val > best_value:
            best_value = val
        alpha = max(alpha, val)
        if alpha >= beta:
            break  # Pruning the search branch

    # Save the result to the memory table and return it.
    memo[key] = {"value": best_value, "depth": depth}
    return best_value

def insane_search(last_word, used_phrases, history_words, turn, max_depth, memo):
    key = (last_word, tuple(sorted(used_phrases)), turn)
    if key in memo:
        return memo[key]
    if max_depth == 0:
        memo[key] = (False, None)
        return (False, None)

    next_phrases = get_valid_next_phrases(last_word, used_phrases, history_words)
    if not next_phrases:
        if turn == 'bot':
            result = (False, None)
        else:
            result = (True, 0)
        memo[key] = result
        return result

    if turn == 'bot':
        best_depth = None
        for phrase in next_phrases:
            _, next_word = phrase.split()
            new_used = set(used_phrases); new_used.add(phrase)
            new_history_words = set(history_words); new_history_words.add(next_word)
            opp_can_win, opp_depth = insane_search(next_word, frozenset(new_used), new_history_words, 'player', max_depth - 1, memo)
            if opp_can_win:
                depth = (opp_depth + 1) if opp_depth is not None else 1
                if best_depth is None or depth < best_depth:
                    best_depth = depth
        if best_depth is not None:
            memo[key] = (True, best_depth)
            return (True, best_depth)
        memo[key] = (False, None)
        return (False, None)
    else:  # player's turn: try to avoid bot win => if there is a move that makes bot unable to force win then player “escapes”
        worst_depth = None
        for phrase in next_phrases:
            _, next_word = phrase.split()
            new_used = set(used_phrases); new_used.add(phrase)
            new_history_words = set(history_words); new_history_words.add(next_word)
            bot_can_win, bot_depth = insane_search(next_word, frozenset(new_used), new_history_words, 'bot', max_depth - 1, memo)
            if not bot_can_win:
                memo[key] = (False, None)
                return (False, None)
            # all moves lead to bot win: player will choose longest path to delay
            depth = (bot_depth + 1) if bot_depth is not None else 1
            if worst_depth is None or depth > worst_depth:
                worst_depth = depth
        memo[key] = (True, worst_depth)
        return (True, worst_depth)

def choose_insane_move(state, max_depth=10, time_budget=0.5):
    start = time.monotonic()
    last_word = state["last_word"]
    history_list = list(state["history"])
    used_phrases = frozenset(" ".join(history_list[i:i+2]) for i in range(len(history_list) - 1))
    history_words = set(history_list)

    # quick shallow lookahead: find win in <=4 turns
    for shallow in range(2, 5):  # depth 2..4
        memo = {}
        can_win, win_depth = insane_search(last_word, used_phrases, history_words, 'bot', shallow, memo)
        if can_win:
            # Find specific moves that lead to shortest win
            candidates = get_valid_next_phrases(last_word, used_phrases, history_words)
            best = None
            best_sub_depth = None
            for phrase in candidates:
                _, next_word = phrase.split()
                new_used = set(used_phrases); new_used.add(phrase)
                new_history_words = set(history_words); new_history_words.add(next_word)
                opp_can_win, opp_depth = insane_search(next_word, frozenset(new_used), new_history_words, 'player', shallow - 1, memo)
                if opp_can_win:
                    depth = (opp_depth + 1) if opp_depth is not None else 1
                    if best_sub_depth is None or depth < best_sub_depth:
                        best_sub_depth = depth
                        best = phrase
            if best:
                return best  # quick win
        if time.monotonic() - start > time_budget:
            return None

    # iterative deepening to max_depth, keep track best forced win (smallest)
    best_move = None
    best_win_depth = None
    for depth in range(5, max_depth + 1):
        if time.monotonic() - start > time_budget:
            break
        memo = {}
        candidates = get_valid_next_phrases(last_word, used_phrases, history_words)
        # ordering: try moves that narrow down your options first
        def opponent_options(phrase):
            _, next_word = phrase.split()
            tmp_used = set(used_phrases); tmp_used.add(phrase)
            tmp_history = set(history_words); tmp_history.add(next_word)
            return len(get_valid_next_phrases(next_word, frozenset(tmp_used), tmp_history))
        candidates.sort(key=opponent_options)  # reduce competitor selection

        for phrase in candidates:
            _, next_word = phrase.split()
            new_used = set(used_phrases); new_used.add(phrase)
            new_history_words = set(history_words); new_history_words.add(next_word)
            opp_can_win, opp_depth = insane_search(next_word, frozenset(new_used), new_history_words, 'player', depth - 1, memo)
            if opp_can_win:
                win_depth = (opp_depth + 1) if opp_depth is not None else 1
                if best_win_depth is None or win_depth < best_win_depth:
                    best_win_depth = win_depth
                    best_move = phrase
        if best_move and best_win_depth == 1:
            break
    return best_move

async def choose_insane_move_async(state, max_depth=10, time_budget=0.5):
    return await asyncio.to_thread(
        choose_insane_move,
        state,
        max_depth,
        time_budget
    )

def choose_strategic_move(last_word, used_phrases, history_words, candidates, depth, principal_variation_move=None):
    best_moves = []
    best_score = -float("inf")
    memo = {}

    # --- MOVE ORDERING ---
    # Reorder the candidate list.
    # Prioritize the best move from the previous loop (principal_variation_move).
    sorted_candidates = []
    if principal_variation_move and principal_variation_move in candidates:
        sorted_candidates.append(principal_variation_move)
        # Create a list of remaining candidates
        other_candidates = [c for c in candidates if c != principal_variation_move]
    else:
        other_candidates = candidates

    # Sort the remaining candidates using the usual heuristic (limiting the choice of competitors)
    def opponent_options(phrase):
        _, next_word = phrase.split()
        tmp_used = set(used_phrases) | {phrase}
        tmp_history = set(history_words) | {next_word}
        return len(get_valid_next_phrases(next_word, frozenset(tmp_used), tmp_history))
    
    other_candidates.sort(key=opponent_options)
    sorted_candidates.extend(other_candidates)
    # --- END MOVE ORDERING ---

    for phrase in sorted_candidates:
        _, next_word = phrase.split()
        new_used = used_phrases | {phrase}
        new_history = history_words | {next_word}

        score = -negamax(next_word, frozenset(new_used), new_history, depth - 1, -float("inf"), float("inf"), "player", memo)
        
        if score > best_score:
            best_score = score
            best_moves = [phrase]
        elif score == best_score:
            best_moves.append(phrase)

    return random.choice(best_moves) if best_moves else None

async def choose_bot_phrase(last_word, history_words, history_phrases, difficulty):
    history_words_set = set(history_words)
    history_phrases_set = frozenset(history_phrases)
    candidates = get_valid_next_phrases(last_word, history_phrases_set, history_words_set)
    if not candidates:
        return None

    if difficulty == "easy":
        candidates.sort(key=lambda p: get_phrase_freq(p), reverse=True)
        return candidates[0] if candidates else None
    elif difficulty == "hard":
        candidates.sort(key=lambda p: get_phrase_freq(p))
        return candidates[0] if candidates else None
    
    elif difficulty.startswith("insane"):
        # --- LOGIC IDDFS (Iterative Deepening) ---
        best_move_overall = None
        
        # Set maximum time and depth
        if difficulty == "insane-min": time_limit, max_depth = 1.5, 6
        elif difficulty == "insane-mid": time_limit, max_depth = 3.0, 8
        else: time_limit, max_depth = 5.0, 12
        
        start_time = time.monotonic()

        # Deepening loop
        for depth in range(1, max_depth + 1):
            time_spent = time.monotonic() - start_time
            if time_spent >= time_limit:
                # logging.info(f"IDDFS: Time limit reached. Stopping at depth {depth-1}.")
                break
            
            remaining_time = time_limit - time_spent
            # logging.info(f"IDDFS: Starting search at depth {depth} with {remaining_time:.2f}s remaining.")

            try:
                # Run search in a separate thread to not block Discord
                # principal_variation_move is passed to optimize Move Ordering
                current_best_move = await asyncio.wait_for(
                    asyncio.to_thread(
                        choose_strategic_move,
                        last_word, history_phrases_set, history_words_set,
                        candidates, depth, best_move_overall
                    ),
                    timeout=remaining_time
                )

                if current_best_move:
                    best_move_overall = current_best_move
                    # logging.info(f"IDDFS: Found best move '{best_move_overall}' at depth {depth}.")
                else:
                    # logging.warning(f"IDDFS: Search at depth {depth} returned no move.")
                    break
            
            except asyncio.TimeoutError:
                # logging.info(f"IDDFS: Search at depth {depth} timed out.")
                break
        
        # Returns the best move from the last completed loop
        if best_move_overall:
            return best_move_overall
        else:
            # Fallback if IDDFS finds nothing (e.g. times out at depth 1)
            return random.choice(candidates)
        # --- END OF IDDFS ---

    else:
        return random.choice(candidates)

# ====== BOT COMMANDS ======
@bot.command()
async def ping(ctx):
    """Check bot latency."""
    latency = round(bot.latency * 1000)
    await ctx.send(f"🏓 Pong! Latency: {latency}ms")

# --- HELP/RULES ---
@bot.command(name="rule")
async def show_rules(ctx):
    embed = discord.Embed(
        title="📚 Luật chơi Nối Từ",
        description="**Người chơi phải nối các cụm từ có nghĩa theo luật sau:**",
        color=discord.Color.blue()
    )

    embed.add_field(
        name="🎮 Chế độ Thường",
        value=(
            "1. Mỗi cụm từ phải gồm đúng **2 từ có nghĩa**, ví dụ: `hoa hồng`, `cá voi`.\n"
            "2. **Từ đầu tiên** của cụm từ mới **phải trùng** với **từ cuối** của cụm từ trước.\n"
            "3. Không được lặp lại cụm từ đã dùng.\n"
            "4. Mỗi người chơi có **1 lần trợ giúp (`NThint`)** để bot gợi ý.\n"
            "5. Lệnh bắt đầu game: `NTstart`.\n"
            "6. Lệnh dừng game: `NTstop` (chỉ người khởi tạo game dùng được).\n"
            "7. Lệnh đầu hàng: `NTsurrender` để chấp nhận thua."
        ),
        inline=False
    )

    embed.add_field(
        name="🏆 Chế độ Giải Đấu (Tournament)",
        value=(
            "1. Admin khởi tạo hai đội bằng lệnh `NTcreate_team`.\n"
            "2. Bắt đầu trận bằng `NTstart_match` với 2 đội đã có.\n"
            "3. Trong chế độ này, **chỉ Admin mới có quyền dùng lệnh trợ giúp (`NThint`)**.\n"
            "4. Mỗi đội có thể `NTteam_surrender` nếu muốn đầu hàng (tính theo số người bỏ phiếu).\n"
            "5. Đội thắng được +1 điểm kèm bonus, mỗi thành viên +1 điểm cá nhân kèm bonus theo streak của đội và bản thân.\n"
            "6. Thắng liên tiếp 3 trận sẽ nhận thêm bonus.\n"
            "7. Lệnh `NTstop_match` chỉ có Admin sử dụng để dừng trận."
        ),
        inline=False
    )

    embed.add_field(
        name="📈 Xếp hạng và danh vọng",
        value=(
            "- Xem điểm cá nhân: `NTrank`.\n"
            "- Xem bảng vàng các đội: `NThalloffame`.\n"
            "- Xếp hạng dựa trên điểm xếp hạng và số lượt nối đúng.\n"
            "- Điểm xếp hạng tăng khi thắng trận, streak càng cao thì bonus càng lớn (mỗi 5 streak để +1 điểm).\n"
            "- Một mùa giải kéo dài 1 tháng, sau đó reset xếp hạng (bao gồm cả xếp hạng cá nhân và xếp hạng đội).\n"
            "- Tất cả dữ liệu được lưu tự động. Hành vi gian lận sẽ bị xử lý. Cấm vì lý do gian lận sẽ bị trừ 5 điểm rank và reset số lượt nối."
        ),
        inline=False
    )

    embed.add_field(
        name="❔ Các lệnh khác",
        value=(
            "- Xem thông tin trận đấu hiện tại: `NTinfo`."
            "- Chơi với bot: `NTstart_bot <difficulty>` (có 3 độ khó: easy, medium, hard, insane-min, insane-mid, insane-max).\n"
        ),
        inline=False
    )
    embed.set_footer(text=f"Yêu cầu bởi {ctx.author.display_name}", icon_url=ctx.author.avatar.url if ctx.author.avatar else None)
    await ctx.send(embed=embed)

# --- ADMIN DICTIONARY MANAGEMENT ---
@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def add_word(ctx, *, phrase: str):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    normalized_phrase = normalize_phrase(phrase)
    if not is_valid_vietnamese_phrase(normalized_phrase):
        await ctx.send("⚠️ Định dạng sai: `từ1 từ2` (chỉ chữ cái và khoảng trắng).")
        return
    try:
        w1w2 = normalized_phrase.split()
        if len(w1w2) == 2:
            w1, w2 = normalized_phrase.split()
            FIRST_WORDS.setdefault(w1, set()).add(w2)
            VALID_PHRASES.add(normalized_phrase)
            if add_phrase_to_db(phrase):
                await ctx.send(f"✅ Đã thêm cụm từ `{normalized_phrase}` vào từ điển.")
                logging.info(f"Added phrase: {normalized_phrase}")
            else:
                await ctx.send("❌ Lỗi khi thêm cụm từ vào từ điển.")
    except Exception as e:
        await ctx.send("❌ Lỗi khi thêm cụm từ vào từ điển.")
        logging.error(f"Error adding phrase: {e}")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def remove_word(ctx, *, phrase: str):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    normalized_phrase = normalize_phrase(phrase)
    try:
        w1w2 = normalized_phrase.split()
        if len(w1w2) == 2:
            w1, w2 = w1w2
            if w1 in FIRST_WORDS and w2 in FIRST_WORDS[w1]:
                FIRST_WORDS[w1].remove(w2)
            VALID_PHRASES.discard(normalized_phrase)
            if remove_phrase_from_db(phrase):
                await ctx.send(f"✅ Đã xóa cụm từ `{normalized_phrase}` khỏi từ điển.")
                logging.info(f"Removed phrase: {normalized_phrase}")
            else:
                await ctx.send("❌ Lỗi khi xóa cụm từ khỏi từ điển.")
    except Exception as e:
        await ctx.send("❌ Lỗi khi xóa cụm từ khỏi từ điển.")
        logging.error(f"Error removing phrase: {e}")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def reload_dict(ctx):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    load_dictionary_from_db()
    await ctx.send(f"✅ Đã tải lại từ điển, có {len(VALID_PHRASES)} cụm từ.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def reload_rank(ctx):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    try:
        load_user_stats()
        await ctx.send("✅ Đã tải lại danh sách xếp hạng.")
    except Exception as e:
        await ctx.send("❌ Lỗi khi tải lại danh sách xếp hạng.")
        logging.error(f"Error reloading rank file: {e}")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def reload_hall_of_fame(ctx):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    try:
        load_hall_of_fame()
        await ctx.send("✅ Đã tải lại danh sách đội.")
    except Exception as e:
        await ctx.send("❌ Lỗi khi tải lại danh sách đội.")
        logging.error(f"Error reloading team file: {e}")

# --- ADMIN MATCH/PLAYER MANAGEMENT ---
@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def set_winner(ctx, member: discord.Member):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    if not member:
        await ctx.send("⚠️ Bạn cần chỉ định người thắng.")
        return
    if ctx.channel.id not in game_state:
        await ctx.send("⚠️ Không có trò chơi nào đang diễn ra.")
        return
    uid_str = str(member.id)
    user_stats.setdefault(uid_str, {"rank": 0, "solan": 0, "streak": 0})
    bonus = 1
    if user_stats[uid_str]["streak"] >= 5:
        bonus += 1
        bonus += (user_stats[uid_str]["streak"] // 5) - 1
    user_stats[uid_str]["rank"] += bonus
    user_stats[uid_str]["streak"] = 0
    reset_streak_for_all(ctx.channel.id)
    save_user_stats()
    del game_state[ctx.channel.id]
    await ctx.send(f"🏆 Đã đặt <@{uid_str}> là người thắng với +{bonus} điểm.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def set_winner_team(ctx, winner_team: str):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    await end_match(ctx, winner_team, surrender=False)

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def set_rank(ctx, member: discord.Member, rank: int):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    if not member:
        await ctx.send("⚠️ Bạn cần chỉ định người dùng.")
        return
    if not isinstance(rank, int) or rank < 0:
        await ctx.send("⚠️ Điểm xếp hạng phải là một số nguyên không âm.")
        return
    uid_str = str(member.id)
    user_stats.setdefault(uid_str, {"rank": 0, "solan": 0, "streak": 0})
    user_stats[uid_str]["rank"] = rank
    save_user_stats()
    await ctx.send(f"✅ Đã đặt điểm xếp hạng của <@{uid_str}> thành {rank}.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def set_solan(ctx, member: discord.Member, solan: int):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    if not member:
        await ctx.send("⚠️ Bạn cần chỉ định người dùng.")
        return
    if not isinstance(solan, int) or solan < 0:
        await ctx.send("⚠️ Số lượt nối đúng phải là một số nguyên không âm.")
        return
    uid_str = str(member.id)
    user_stats.setdefault(uid_str, {"rank": 0, "solan": 0, "streak": 0})
    user_stats[uid_str]["solan"] = solan
    save_user_stats()
    await ctx.send(f"✅ Đã đặt số lượt nối đúng của <@{uid_str}> thành {solan}.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def set_streak(ctx, member: discord.Member, streak: int):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    if not member:
        await ctx.send("⚠️ Bạn cần chỉ định người dùng.")
        return
    if not isinstance(streak, int) or streak < 0:
        await ctx.send("⚠️ Chuỗi nối đúng phải là một số nguyên không âm.")
        return
    uid_str = str(member.id)
    user_stats.setdefault(uid_str, {"rank": 0, "solan": 0, "streak": 0})
    user_stats[uid_str]["streak"] = streak
    save_user_stats()
    await ctx.send(f"✅ Đã đặt chuỗi nối đúng của <@{uid_str}> thành {streak}.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def set_team_streak(ctx, team_name: str, streak: int):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    if team_name not in hall_of_fame:
        await ctx.send("⚠️ Đội không tồn tại.")
        return
    if not isinstance(streak, int) or streak < 0:
        await ctx.send("⚠️ Chuỗi nối đúng phải là một số nguyên không âm.")
        return
    hall_of_fame[team_name]["streak"] = streak
    save_hall_of_fame()
    await ctx.send(f"✅ Đã đặt chuỗi nối đúng của đội **{team_name}** là {streak}.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def warn(ctx, member: discord.Member):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    if not member:
        await ctx.send("⚠️ Bạn cần chỉ định người dùng.")
        return
    user_id = str(member.id)
    if user_id in banned_users:
        await ctx.send("⚠️ Người dùng đã bị cấm.")
        return
    violation_count[user_id] += 1
    if violation_count[user_id] >= MAX_VIOLATIONS:
        banned_users.add(user_id)
        user_stats[user_id]["rank"] = max(0, user_stats[user_id]["rank"] - 5)
        await ctx.send(f"🚫 <@{user_id}> đã bị cấm vì gian lận!")
    else:
        await ctx.send(f"⚠️ Đã cảnh cáo <@{user_id}> về hành vi gian lận. Tổng vi phạm là {violation_count[user_id]}")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def reset_warn(ctx, member: discord.Member):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    if not member:
        await ctx.send("⚠️ Bạn cần chỉ định người dùng.")
        return
    user_id = str(member.id)
    if violation_count[user_id] == 0:
        await ctx.send("✅ Người dùng chưa có dấu hiệu gian lận.")
        return
    violation_count[user_id] = 0
    await ctx.send(f"✅ Đã reset cảnh cáo gian lận cho <@{user_id}>.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def show_warn(ctx, member: discord.Member):
    if not member:
        await ctx.send("⚠️ Bạn cần chỉ định người dùng.")
        return
    user_id = str(member.id)
    if not violation_count[user_id] and violation_count[user_id] == 0:
        await ctx.send("✅ Người dùng chưa có dấu hiệu gian lận.")
        return
    if user_id in banned_users:
        await ctx.send("⚠️ Người dùng đã bị cấm.")
        return
    else:
        await ctx.send(f"⚠️ Tổng vi phạm của <@{user_id}> là {violation_count[user_id]} lần.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def ban(ctx, member: discord.Member):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    if not member:
        await ctx.send("⚠️ Bạn cần chỉ định người dùng.")
        return
    user_id = str(member.id)
    if user_id in banned_users:
        await ctx.send("⚠️ Người dùng đã bị cấm rồi.")
        return
    banned_users.add(user_id)
    user_stats[user_id]["rank"] = max(0, user_stats[user_id]["rank"] - 5)
    await ctx.send(f"🚫 Đã cấm <@{user_id}> khỏi trò chơi Nối Từ.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def unban(ctx, member: discord.Member):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    if not member:
        await ctx.send("⚠️ Bạn cần chỉ định người dùng.")
        return
    user_id = str(member.id)
    if user_id not in banned_users:
        await ctx.send("⚠️ Người dùng chưa bị cấm.")
        return
    banned_users.remove(user_id)
    await ctx.send(f"✅ Đã bỏ cấm <@{user_id}> khỏi trò chơi Nối Từ.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def show_ban(ctx, member: discord.Member):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Bạn không có quyền sử dụng lệnh này.")
        return
    if not member:
        banned_list = [f"<@{uid}>" for uid in banned_users]
        if not banned_list:
            await ctx.send("✅ Không có người dùng nào bị cấm.")
            return
        embed = discord.Embed(
            title="🚫 Danh sách người dùng bị cấm",
            description="\n".join(banned_list),
            color=discord.Color.red()
        )
        embed.set_footer(text=f"Yêu cầu bởi {ctx.author.display_name}", icon_url=ctx.author.avatar.url if ctx.author.avatar else None)
        await ctx.send(embed=embed)
    else:
        user_id = str(member.id)
        if user_id in banned_users:
            await ctx.send(f"🚫 <@{user_id}> hiện đang bị cấm.")
        else:
            await ctx.send(f"✅ <@{user_id}> không bị cấm.")

# --- TEAM & TOURNAMENT ---
@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def create_team(ctx, team_name: str, *members: discord.Member):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Chỉ Admin mới được tạo đội.")
        return
    if not team_name or len(team_name) < 3:
        await ctx.send("⚠️ Tên đội phải có ít nhất 3 ký tự.")
        return
    if team_name in hall_of_fame:
        await ctx.send("⚠️ Tên đội đã tồn tại.")
        return
    if len(members) < 2:
        await ctx.send("⚠️ Cần ít nhất 2 thành viên để tạo đội.")
        return
    member_ids = [str(m.id) for m in members]
    hall_of_fame[team_name] = {"points": 0, "streak": 0, "members": member_ids}
    save_hall_of_fame()
    await ctx.send(f"✅ Đã tạo đội **{team_name}** với các thành viên: {', '.join(m.mention for m in members)}.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def add_member(ctx, team_name: str, *members: discord.Member):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Chỉ Admin mới được thêm thành viên vào đội.")
        return
    if team_name not in hall_of_fame:
        await ctx.send("⚠️ Đội không tồn tại.")
        return
    if len(members) == 0:
        await ctx.send("⚠️ Cần ít nhất 1 thành viên để thêm vào đội.")
        return
    for m in members:
        mid = str(m.id)
        if mid not in hall_of_fame[team_name]["members"]:
            hall_of_fame[team_name]["members"].append(mid)
    save_hall_of_fame()
    await ctx.send(f"✅ Đã thêm {', '.join(m.mention for m in members)} vào đội **{team_name}**.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def remove_member(ctx, team_name: str, *members: discord.Member):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Chỉ Admin mới được xóa thành viên khỏi đội.")
        return
    if team_name not in hall_of_fame:
        await ctx.send("⚠️ Đội không tồn tại.")
        return
    if len(members) == 0:
        await ctx.send("⚠️ Cần ít nhất 1 thành viên để xóa khỏi đội.")
        return
    for m in members:
        mid = str(m.id)
        if mid in hall_of_fame[team_name]["members"]:
            hall_of_fame[team_name]["members"].remove(mid)
    save_hall_of_fame()
    await ctx.send(f"✅ Đã xóa {', '.join(m.mention for m in members)} khỏi đội **{team_name}**.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def start_match(ctx, team_a: str, team_b: str):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Chỉ Admin mới được bắt đầu trận đấu.")
        return
    if ctx.channel.id in game_state or ctx.channel.id in match_state:
        await ctx.send("⚠️ Đang có trò chơi hoặc trận đấu khác đang diễn ra.")
        return
    if not team_a or not team_b:
        await ctx.send("⚠️ Vui lòng cung cấp tên của hai đội.")
        return
    if team_a not in hall_of_fame or team_b not in hall_of_fame:
        await ctx.send("⚠️ Một trong hai đội không tồn tại.")
        return
    if team_a == team_b:
        await ctx.send("⚠️ Hai đội không thể giống nhau.")
        return
    selected_phrase = select_start_phrase(
        safety_filter=False
    )
    if not selected_phrase:
        await ctx.send("😔 Không thể tìm được cụm từ bắt đầu có thể nối tiếp. Vui lòng thử lại hoặc thêm từ vào từ điển.")
        return
    w1, w2 = selected_phrase.split()
    mutual_exclusion_check(ctx.channel.id)
    match_state[ctx.channel.id] = {
        "teams": [team_a, team_b],
        "team_streak": {team_a: 0, team_b: 0},
        "member_streak": {},
        "current_team": team_a,
        "history": [w1, w2],
        "players": [],
        "last_word": w2,
        "last_player_id": None,
        "surrender_votes": {team_a: set(), team_b: set()},
        "mode": "tournament",
        "possible_phrases": [
            f"{w2} {next_w}" for next_w in FIRST_WORDS.get(w2, set())
            if f"{w2} {next_w}" in VALID_PHRASES and next_w != w1
        ]
    }
    await ctx.send(
        f"🏆 Trận đấu giữa **{team_a}** và **{team_b}** đã bắt đầu!\n"
        f"Cụm từ đầu: `{w1} {w2}`\nAi nối tiếp với: `{w2}`?"
    )

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def team_surrender(ctx):
    match = match_state.get(ctx.channel.id)
    if not (match and match.get("mode") == "tournament"):
        await ctx.send("⚠️ Không có trận đấu giải nào đang diễn ra.")
        return
    uid_str = str(ctx.author.id)
    team = None
    for t, info in hall_of_fame.items():
        if uid_str in info["members"]:
            team = t
            break
    if not team or team not in match["teams"]:
        await ctx.send("🚫 Bạn không thuộc đội nào trong trận này.")
        return
    if uid_str in match["surrender_votes"][team]:
        await ctx.send("⚠️ Bạn đã bỏ phiếu đầu hàng rồi.")
        return
    match["surrender_votes"][team].add(uid_str)
    team_members = set(hall_of_fame[team]["members"])
    if match["surrender_votes"][team] >= team_members:
        winner = [t for t in match["teams"] if t != team][0]
        await end_match(ctx, winner, surrender=True)
    else:
        await ctx.send(f"🗳️ <@{uid_str}> đã bỏ phiếu đầu hàng ({len(match['surrender_votes'][team])}/{len(team_members)}).")

async def end_match(source, winner_team, surrender=False):
    channel = source.channel if hasattr(source, 'channel') else source
    match = match_state.get(channel.id)
    if not match:
        await channel.send("⚠️ Không có trận đấu nào đang diễn ra.")
        return
    hall_of_fame[winner_team]["points"] += 1
    streak = hall_of_fame[winner_team]["streak"]
    bonus = 1 + (streak // 5) if streak % 5 == 0 else 1
    hall_of_fame[winner_team]["points"] += (bonus - 1)
    for uid in hall_of_fame[winner_team]["members"]:
        uid_str = str(uid)
        user_stats.setdefault(uid_str, {"rank": 0, "solan": 0, "streak": 0})
        user_streak = user_stats[uid_str]["streak"]
        user_bonus = 1 + (user_streak // 5) if user_streak % 5 == 0 else 1
        user_stats[uid_str]["rank"] += user_bonus + bonus
        user_stats[uid_str]["streak"] = 0
    loser_team = [t for t in match["teams"] if t != winner_team][0]
    hall_of_fame[loser_team]["streak"] = 0
    for uid in hall_of_fame[loser_team]["members"]:
        uid_str = str(uid)
        user_stats.setdefault(uid_str, {"rank": 0, "solan": 0, "streak": 0})
        user_stats[uid_str]["streak"] = 0
    save_hall_of_fame()
    save_user_stats()
    del match_state[channel.id]
    if surrender:
        await channel.send(f"🏁 Không còn từ để nối!\n🏆 Đội **{winner_team}** thắng vì đối thủ đầu hàng! Đội và mỗi thành viên được +{bonus} điểm.")
    else:
        await channel.send(f"🏁 Không còn từ để nối!\n🏆 Đội **{winner_team}** thắng trận! Đội và mỗi thành viên được +{bonus} điểm.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def stop_match(ctx):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Chỉ Admin mới được dừng trận đấu.")
        return
    if is_tournament(ctx) and ctx.channel.id in match_state:
        match = match_state[ctx.channel.id]
        for team in match["teams"]:
            hall_of_fame[team]["streak"] = 0
            for member_id in hall_of_fame[team]["members"]:
                uid_str = str(member_id)
                user_stats.setdefault(uid_str, {"rank": 0, "solan": 0, "streak": 0})
                user_stats[uid_str]["streak"] = 0
        save_hall_of_fame()
        save_user_stats()
        del match_state[ctx.channel.id]
        await ctx.send("🛑 Trận đấu đã bị dừng.")
    else:
        await ctx.send("⚠️ Không có trận đấu nào đang diễn ra.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def team(ctx, team_name: str = None):
    team_info = None
    if team_name:
        team_info = hall_of_fame.get(team_name)
    else:
        uid_str = str(ctx.author.id)
        team_info = None
        for team, info in hall_of_fame.items():
            if uid_str in info["members"]:
                team_info = info
                team_name = team
                break
    if not team_info and not team_name:
        await ctx.send("⚠️ Bạn không thuộc đội nào.")
        return
    if not team_info:
        await ctx.send("⚠️ Đội không tồn tại.")
        return
    members = [f"<@{mid}>" for mid in team_info["members"]]
    embed = discord.Embed(
        title=f"Đội {team_name}",
        description=f"Điểm: {team_info['points']}, Chuỗi: {team_info['streak']}",
        color=discord.Color.green()
    )
    embed.add_field(name="Thành viên", value=", ".join(members) if members else "Không có thành viên.")
    embed.set_footer(text=f"Yêu cầu bởi {ctx.author.display_name}", icon_url=ctx.author.avatar.url if ctx.author.avatar else None)
    await ctx.send(embed=embed)

# --- NORMAL GAME COMMANDS ---
@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def start(ctx):
    if is_tournament(ctx):
        await ctx.send("🚫 Không thể bắt đầu trò chơi thường khi đang có trận đấu giải đấu.")
        return
    if str(ctx.author.id) in banned_users:
        await ctx.send("🚫 Bạn đã bị cấm chơi trò này.")
        return
    if not VALID_PHRASES:
        await ctx.send("⚠️ Không có từ vựng nào được tải. Vui lòng kiểm tra file từ điển.")
        return
    if ctx.channel.id in game_state or ctx.channel.id in match_state:
        await ctx.send("⚠️ Đã có trò chơi hoặc trận đấu khác đang diễn ra.")
        return
    selected_phrase = select_start_phrase(
        max_samples=30,
        forced_win_lookahead=5,
        time_budget=0.1,
        safety_filter=True
    )
    if not selected_phrase:
        await ctx.send("😔 Không thể tìm được cụm từ bắt đầu có thể nối tiếp. Vui lòng thử lại hoặc thêm từ vào từ điển.")
        return
    w1, w2 = selected_phrase.split()
    mutual_exclusion_check(ctx.channel.id)
    game_state[ctx.channel.id] = {
        "starter_id": str(ctx.author.id),
        "history": [w1, w2],
        "players": [],
        "last_word": w2,
        "possible_phrases": [
            f"{w2} {next_w}" for next_w in FIRST_WORDS.get(w2, set())
            if f"{w2} {next_w}" in VALID_PHRASES and next_w != w1
        ],
        "last_player_id": None,
        "surrender_votes": set()
    }
    await ctx.send(f"🎮 Trò chơi bắt đầu!\nCụm từ đầu: `{w1} {w2}`\nAi nối tiếp với: `{w2}`?")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def surrender(ctx):
    if is_tournament(ctx):
        await ctx.send("🚫 Vui lòng sử dụng `NTteam_surrender` trong chế độ giải đấu.")
        return
    state = game_state.get(ctx.channel.id)
    uid_str = str(ctx.author.id)
    if not state:
        await ctx.send("⚠️ Không có trò chơi nào đang diễn ra.")
        return
    last_player_id = state.get("last_player_id")
    if last_player_id is None:
        await ctx.send("⚠️ Chưa có lượt chơi nào để đầu hàng.")
        return
    if uid_str == last_player_id:
        await ctx.send("🚫 Người vừa chơi không thể bỏ phiếu đầu hàng.")
        return
    if uid_str not in state["players"]:
        await ctx.send("🚫 Bạn không phải là người tham gia trò chơi này.")
        return
    if uid_str in state["surrender_votes"]:
        await ctx.send("⚠️ Bạn đã bỏ phiếu đầu hàng rồi.")
        return
    state["surrender_votes"].add(uid_str)
    total_voters = [pid for pid in state["players"] if pid != last_player_id]
    votes_needed = len(total_voters)
    await ctx.send(f"🗳️ <@{uid_str}> đã bỏ phiếu đầu hàng ({len(state['surrender_votes'])}/{votes_needed}).")
    if len(state["surrender_votes"]) >= votes_needed and votes_needed > 0:
        last_player_id_str = str(last_player_id)
        if last_player_id_str == str(bot.user.id):
            reset_streak_for_all(ctx.channel.id)
            save_user_stats()
            del game_state[ctx.channel.id]
            await ctx.send("💥 Đa số đã đồng ý đầu hàng. Bot đã chặn bạn thành công!")
        else:
            user_stats.setdefault(last_player_id_str, {"rank": 0, "solan": 0, "streak": 0})
            bonus = 1
            if user_stats[last_player_id_str]["streak"] >= 5:
                bonus += 1
            user_stats[last_player_id_str]["rank"] += bonus
            user_stats[last_player_id_str]["streak"] = 0
            reset_streak_for_all(ctx.channel.id)
            save_user_stats()
            del game_state[ctx.channel.id]
            await ctx.send(f"💥 Đa số đã đồng ý đầu hàng. <@{last_player_id}> thắng và được +{bonus} điểm!")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def stop(ctx):
    if is_tournament(ctx):
        await ctx.send("🚫 Không được dừng trò chơi trong chế độ giải đấu.")
        return
    state = game_state.get(ctx.channel.id)
    if not state:
        await ctx.send("⚠️ Không có trò chơi nào đang diễn ra.")
        return
    starter_id = state.get("starter_id")
    if ctx.author.id != ADMIN and str(ctx.author.id) != starter_id:
        await ctx.send("🚫 Chỉ người bắt đầu trò chơi mới được dừng trò chơi này.")
        return
    last_player_id = state.get("last_player_id")
    if last_player_id and str(last_player_id) in user_stats:
        user_stats[str(last_player_id)]["streak"] = 0
        reset_streak_for_all(ctx.channel.id)
        save_user_stats()
    del game_state[ctx.channel.id]
    await ctx.send("🛑 Trò chơi đã kết thúc.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def info(ctx):
    if is_tournament(ctx):
        state = match_state.get(ctx.channel.id)
        if not state:
            await ctx.send("⚠️ Không có trận đấu giải nào đang diễn ra.")
            return
        embed = discord.Embed(
            title="Thông tin Trận Đấu Giải",
            description=f"Đội hiện tại: {state['current_team']}\n**Cụm từ cuối:** `{state['last_word']}`\nChuỗi hiện tại: {state['team_streak']}",
            color=discord.Color.blue()
        )
        embed.add_field(name="Lịch sử", value=", ".join(state["history"]) if state["history"] else "Chưa có lịch sử.", inline=False)
        embed.add_field(name="Thành viên đã chơi", value=", ".join(f"<@{pid}>" for pid in state["players"]) if state["players"] else "Chưa có người chơi.", inline=False)
        embed.set_footer(text=f"Yêu cầu bởi {ctx.author.display_name}", icon_url=ctx.author.avatar.url if ctx.author.avatar else None)
        await ctx.send(embed=embed)
    else:
        state = game_state.get(ctx.channel.id)
        if not state:
            await ctx.send("⚠️ Không có trò chơi nào đang diễn ra.")
            return
        embed = discord.Embed(
            title="Thông tin Trò Chơi",
            description=f"**Cụm từ cuối:** `{state['last_word']}`",
            color=discord.Color.blue()
        )
        embed.add_field(name="Lịch sử", value=", ".join(state["history"]) if state["history"] else "Chưa có lịch sử.", inline=False)
        embed.add_field(name="Người chơi", value=", ".join(f"<@{pid}>" for pid in state["players"]) if state["players"] else "Chưa có người chơi.", inline=False)
        embed.set_footer(text=f"Yêu cầu bởi {ctx.author.display_name}", icon_url=ctx.author.avatar.url if ctx.author.avatar else None)
        await ctx.send(embed=embed)

# --- BOT PLAY SYSTEM ---
@bot.command(name="start_bot")
@commands.cooldown(1, 5, commands.BucketType.user)
async def start_bot(ctx, difficulty: str = "medium"):
    difficulty = difficulty.lower()
    if difficulty not in ("easy", "medium", "hard", "insane-min", "insane-mid", "insane-max"):
        await ctx.send("⚠️ Độ khó không hợp lệ. Chọn một trong: easy, medium, hard, insane-min, insane-mid, insane-max.")
        return
    if is_tournament(ctx):
        await ctx.send("🚫 Không thể bắt đầu trò chơi thường khi đang có trận đấu giải đấu.")
        return
    if str(ctx.author.id) in banned_users:
        await ctx.send("🚫 Bạn đã bị cấm chơi trò này.")
        return
    if not VALID_PHRASES:
        await ctx.send("⚠️ Không có từ vựng nào được tải. Vui lòng kiểm tra từ điển.")
        return
    if ctx.channel.id in game_state or ctx.channel.id in match_state:
        await ctx.send("⚠️ Đã có trò chơi hoặc trận đấu khác đang diễn ra.")
        return
    selected_phrase = selected_phrase = select_start_phrase(
        max_samples=100,
        forced_win_lookahead=5,
        time_budget=0.3,
        safety_filter=True
    )
    if not selected_phrase:
        await ctx.send("😔 Không thể tìm được cụm từ bắt đầu có thể nối tiếp. Vui lòng thử lại hoặc thêm từ vào từ điển.")
        return
    w1, w2 = selected_phrase.split()
    mutual_exclusion_check(ctx.channel.id)
    game_state[ctx.channel.id] = {
        "starter_id": str(ctx.author.id),
        "history": [w1, w2],
        "players": [str(bot.user.id)],
        "last_word": w2,
        "possible_phrases": [
            f"{w2} {next_w}" for next_w in FIRST_WORDS.get(w2, set())
            if f"{w2} {next_w}" in VALID_PHRASES and next_w != w1
        ],
        "last_player_id": None,
        "surrender_votes": set(),
        "with_bot": True,
        "bot_difficulty": difficulty,
        "bot_last_word": w2
    }
    await ctx.send(f"🤖 Trò chơi với bot ({difficulty}) bắt đầu!\nCụm từ đầu: `{w1} {w2}`\nBạn đi trước với: `{w2}`?")

# --- RANKING & HALL OF FAME & SEASON ---
def reset_season():
    global user_stats, hall_of_fame, season_info
    for uid, data in user_stats.items():
        data["rank"] = 0
        data["streak"] = 0
        # Do not reset "solan"
    for team, info in hall_of_fame.items():
        info["rank"] = 0
        info["streak"] = 0
    save_user_stats()
    save_hall_of_fame()
    season_info["seasons"] += 1
    season_info["start"] = datetime.utcnow().isoformat()
    
    current_date = datetime.now()
    if current_date.month == 12:
        next_month = 1
        next_year = current_date.year + 1
    else:
        next_month = current_date.month + 1
        next_year = current_date.year
    _, num_days_next_month = calendar.monthrange(next_year, next_month)
    season_info["end"] = (datetime.utcnow() + timedelta(days=num_days_next_month)).isoformat()
    save_season_info()

def check_season_end():
    end = datetime.fromisoformat(season_info["end"])
    now = datetime.utcnow()
    if now >= end:
        reset_season()
        return True
    return False

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def start_season(ctx):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Chỉ Admin mới được bắt đầu mùa giải mới.")
        return
    reset_season()
    await ctx.send(f"✅ Đã bắt đầu mùa giải mới: Season {to_roman(season_info['seasons'])}!")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def end_season(ctx):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Chỉ Admin mới được kết thúc mùa giải.")
        return
    reset_season()
    await ctx.send(f"✅ Đã kết thúc và bắt đầu mùa giải mới: Season {to_roman(season_info['seasons'])}!")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def extend_season(ctx, days: int = 5):
    if ctx.author.id != ADMIN:
        await ctx.send("🚫 Chỉ Admin mới được gia hạn mùa giải.")
        return
    end = datetime.fromisoformat(season_info["end"])
    season_info["end"] = (end + timedelta(days=days)).isoformat()
    save_season_info()
    await ctx.send(f"✅ Đã gia hạn mùa giải thêm {days} ngày.")

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def season(ctx):
    if check_season_end():
        await ctx.send(f"🔄 Mùa giải đã kết thúc! Đã bắt đầu Season {to_roman(season_info['seasons'])}")

    # Find top player
    top_player = None
    if user_stats:
        sorted_players = sorted(
            user_stats.items(),
            key=lambda x: (-x[1].get("rank", 0), -x[1].get("solan", 0), -x[1].get("streak", 0))
        )
        if sorted_players:
            uid = sorted_players[0][0]
            top_player = f"<@{uid}>"

    # Find top team
    top_team = None
    if hall_of_fame:
        sorted_teams = sorted(
            hall_of_fame.items(),
            key=lambda x: (-x[1]["points"], -x[1]["streak"])
        )
        if sorted_teams:
            top_team = sorted_teams[0][0]

    start_time = datetime.fromisoformat(season_info['start'])
    end_time = datetime.fromisoformat(season_info['end'])
    embed = discord.Embed(
        title=f"Thông tin Mùa Giải - Season {to_roman(season_info['seasons'])}",
        description=(
            f"**Người chơi xuất sắc nhất:** {top_player or 'Chưa có.'}\n"
            f"**Đội chơi xuất sắc nhất:** `{top_team or 'Chưa có.'}`\n"
            f"**Bắt đầu:** {format_dt(start_time, 'F')}\n"
            f"**Kết thúc:** {format_dt(end_time, 'R')}"
        ),
        color=discord.Color.blue()
    )
    embed.set_footer(text=f"Yêu cầu bởi {ctx.author.display_name}", icon_url=ctx.author.avatar.url if ctx.author.avatar else None)
    await ctx.send(embed=embed)

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def rank(ctx):
    if not user_stats or all(data["solan"] == 0 for data in user_stats.values()):
        await ctx.send("📉 Chưa có ai chơi hoặc chưa có lượt chơi nào hợp lệ.")
        return
    if check_season_end():
        await ctx.send(f"🔄 Mùa giải đã kết thúc! Đã bắt đầu Season {to_roman(season_info['seasons'])}")
    sorted_stats = sorted(
        user_stats.items(),
        key=lambda x: (-x[1].get("rank", 0), -x[1].get("solan", 0), -x[1].get("streak", 0))
    )
    embed = discord.Embed(
        title=f"🏆 BẢNG XẾP HẠNG TOP 10 - Season {to_roman(season_info['seasons'])}",
        description="Dưới đây là danh sách người chơi dẫn đầu!",
        color=discord.Color.gold()
    )
    medals = ["🥇", "🥈", "🥉"]
    for i, (uid, data) in enumerate(sorted_stats[:10], 1):
        try:
            user = bot.get_user(int(uid)) or await bot.fetch_user(int(uid))
            name = user.display_name
        except:
            name = f"ID:{uid}"
        medal_or_number = medals[i - 1] if i <= 3 else f"#{i}"
        value = (
            f"**Điểm:** {data['rank']} | **Lượt:** {data['solan']} | **Chuỗi:** {data['streak']}"
        )
        embed.add_field(name=f"{medal_or_number} {name}", value=value, inline=False)
    embed.set_footer(text=f"Yêu cầu bởi {ctx.author.display_name}", icon_url=ctx.author.avatar.url if ctx.author.avatar else None)
    await ctx.send(embed=embed)

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def halloffame(ctx):
    if not hall_of_fame or all(data["points"] == 0 for data in hall_of_fame.values()):
        await ctx.send("📉 Chưa có đội nào.")
        return
    if check_season_end():
        await ctx.send(f"🔄 Mùa giải đã kết thúc! Đã bắt đầu Season {to_roman(season_info['seasons'])}")
    sorted_teams = sorted(hall_of_fame.items(), key=lambda x: (-x[1]["points"], -x[1]["streak"]))
    medals = ["🥇", "🥈", "🥉"]
    embed = discord.Embed(title=f"🏆 Hall of Fame - Season {to_roman(season_info['seasons'])}", color=discord.Color.gold())
    for i, (team, data) in enumerate(sorted_teams, 1):
        medal = medals[i-1] if i <= 3 else f"#{i}"
        members = ", ".join(f"<@{uid}>" for uid in data["members"])
        embed.add_field(
            name=f"{medal} {team}",
            value=f"Điểm: {data['points']} | Chuỗi: {data['streak']}\nThành viên: {members}",
            inline=False
        )
    embed.set_footer(text=f"Yêu cầu bởi {ctx.author.display_name}", icon_url=ctx.author.avatar.url if ctx.author.avatar else None)
    await ctx.send(embed=embed)

# --- HINT/HELP ---
def difficulize(phrase):
    vowels = 'aeiouáàảãạăắằẳẵặâấầẩẫậéèẻẽẹêếềểễệíìỉĩịóòỏõọôốồổỗộơớờởỡợúùủũụưứừửữựýỳỷỹỵ'
    state_1 = ' '.join([w[0] + '_' * (len(w) - 1) for w in phrase.split()])
    state_2 = ''.join(
        c if c.lower() in vowels else ' ' if c == ' ' else '_'
        for c in phrase
    )
    state_3_part = []
    for word in phrase.split():
        temp = ''
        for i, c in enumerate(word):
            if i == 0 or c.lower() in vowels:
                temp += c
            else:
                temp += '_'
        state_3_part.append(temp)
    state_3 = f"{' '.join(state_3_part)}"
    return (
        f"{state_1}, "
        f"{state_2}, "
        f"{state_3}"
    )

@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def hint(ctx):
    tournament = is_tournament(ctx)
    if tournament and ctx.author.id != ADMIN:
        await ctx.send("🚫 Không được dùng trợ giúp trong chế độ giải đấu.")
        return
    state = None
    if tournament:
        state = match_state.get(ctx.channel.id)
    else:
        state = game_state.get(ctx.channel.id)
    if not state:
        await ctx.send("⚠️ Không có trò chơi nào đang diễn ra.")
        return
    if "help_used" not in state:
        state["help_used"] = set()
    if str(ctx.author.id) in state["help_used"]:
        await ctx.send("⚠️ Bạn chỉ được dùng trợ giúp 1 lần mỗi game.")
        return
    last_word = state["last_word"]
    history_phrases = {" ".join(state["history"][i:i+2]) for i in range(len(state["history"]) - 1)}
    history_words = set(state["history"])
    suggestion = None
    for next_w in FIRST_WORDS.get(last_word, set()):
        potential_phrase = f"{last_word} {next_w}"
        if (
            potential_phrase in VALID_PHRASES and
            potential_phrase not in history_phrases and
            next_w not in history_words and
            last_word != next_w
        ):
            suggestion = potential_phrase
            break        
    state["help_used"].add(str(ctx.author.id))
    if suggestion:
        await ctx.send(f"💡 Gợi ý cho bạn: `{difficulize(suggestion)}`")
    else:
        await ctx.send("😔 Không còn cụm từ hợp lệ để nối tiếp.")

# ======= Start Discord Bot =======

bot.run("YOUR_DISCORD_BOT_TOKEN")

# Link: https://discord.com/oauth2/authorize?client_id=1396131015843385437&permissions=274877978688&integration_type=0&scope=bot
