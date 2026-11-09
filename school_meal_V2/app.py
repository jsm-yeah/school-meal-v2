# -*- coding: utf-8 -*-
"""
학교 급식 웹 서버 (Flask + SQLite)

환경변수
  SECRET_KEY      세션 암호화 키 (Render 환경변수에 반드시 설정)
  DATABASE_PATH   SQLite 파일 경로 (기본: app.py 옆 data.db)
  MEAL_CSV        급식 CSV 경로 (기본: app.py 옆 meals.csv)
  DEFAULT_MEAL    기본으로 보여줄 식사명 (기본: 중식, 없으면 석식 → 조식 순으로 대체)
  ADMIN_USERNAME  기본 관리자 아이디 (기본: admin)
  ADMIN_PASSWORD  기본 관리자 비밀번호 (기본: 1234, 계정이 없을 때 생성용)
"""
import csv
import html
import io
import json
import os
import re
import sqlite3
import threading
from datetime import date, datetime, timedelta, timezone
from functools import wraps

from flask import Flask, g, jsonify, render_template, request, session
from werkzeug.exceptions import HTTPException
from werkzeug.security import check_password_hash, generate_password_hash

# =========================================================
# 설정
# =========================================================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.environ.get("DATABASE_PATH") or os.path.join(BASE_DIR, "data.db")
CSV_PATH = os.environ.get("MEAL_CSV") or os.path.join(BASE_DIR, "meals.csv")
DEFAULT_MEAL = (os.environ.get("DEFAULT_MEAL") or "중식").strip()
ADMIN_USERNAME = (os.environ.get("ADMIN_USERNAME") or "admin").strip()
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD") or "1234"
KST = timezone(timedelta(hours=9))

ROLE_ADMIN = "admin"
ROLE_USER = "user"
MEAL_PRIORITY = ("중식", "석식", "조식")
USERNAME_RE = re.compile(r"[A-Za-z0-9_]{4,20}")

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY") or "school-meal-secret-change-me"
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=bool(os.environ.get("RENDER")),
    PERMANENT_SESSION_LIFETIME=timedelta(days=7),
)
try:
    app.json.ensure_ascii = False
    app.json.sort_keys = False
except AttributeError:
    app.config["JSON_AS_ASCII"] = False
    app.config["JSON_SORT_KEYS"] = False


# =========================================================
# 공통 유틸
# =========================================================
def today_str():
    return datetime.now(KST).strftime("%Y-%m-%d")


def clean(value):
    return "" if value is None else str(value).strip()


def request_data():
    data = request.get_json(silent=True)
    if isinstance(data, dict):
        return data
    return request.form.to_dict()


def ok(message, status=200, **extra):
    payload = {"success": True, "message": message}
    payload.update(extra)
    return jsonify(payload), status


def fail(message, status=400):
    return jsonify({"success": False, "message": message}), status


_DATE_RE = re.compile(r"(\d{4})\D{0,3}?(\d{1,2})\D{0,3}?(\d{1,2})")


def normalize_date(value):
    """'20260302', '2026-3-2', '2026.03.02' -> '2026-03-02'"""
    match = _DATE_RE.search(clean(value))
    if not match:
        return None
    try:
        return date(int(match.group(1)), int(match.group(2)), int(match.group(3))).strftime("%Y-%m-%d")
    except ValueError:
        return None


def month_prefix(year, month):
    """year=2026, month=3 / month='2026-03' / month='202603' -> '2026-03'"""
    year, month = clean(year), clean(month)
    if month and not year:
        match = re.fullmatch(r"(\d{4})\D?(\d{1,2})", month)
        if not match:
            return None
        year, month = match.group(1), match.group(2)
    if not (year.isdigit() and month.isdigit()):
        return None
    y, m = int(year), int(month)
    if not (1 <= m <= 12 and 1900 <= y <= 2999):
        return None
    return f"{y:04d}-{m:02d}"


# =========================================================
# 메뉴 가공 (알레르기 번호 괄호는 절대 삭제하지 않음)
# =========================================================
_SEP_RE = re.compile(r"<\s*br\s*/?\s*>|\r\n|\r|\n", re.IGNORECASE)
_ALLERGY_TAIL_RE = re.compile(r"\s*\(\s*(?:\d{1,2}\s*\.?\s*)+\)\s*$")
_OPEN, _CLOSE = "([{（［｛", ")]}）］｝"


def split_outside_brackets(text, sep=","):
    """괄호 바깥의 구분자로만 분리 -> 괄호 안 내용은 그대로 보존"""
    parts, buf, depth = [], [], 0
    for ch in text:
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE and depth > 0:
            depth -= 1
        if ch == sep and depth == 0:
            parts.append("".join(buf))
            buf = []
        else:
            buf.append(ch)
    parts.append("".join(buf))
    return parts


def _tidy(text):
    return re.sub(r"\s+", " ", text).strip()


def split_menu(raw):
    """
    CSV 요리명 -> 메뉴 리스트
    '쌀밥  <br/>돈까스  (1.2.5.6.)' -> ['쌀밥', '돈까스 (1.2.5.6.)']
    """
    text = html.unescape(clean(raw))
    parts = _SEP_RE.split(text)
    if len(parts) == 1:
        parts = split_outside_brackets(text, ",")
    return [item for item in (_tidy(p) for p in parts) if item]


def split_items(raw):
    """문자열 또는 배열 -> 메뉴 리스트 (줄바꿈, <br>, 괄호 밖 쉼표 모두 구분자)"""
    if isinstance(raw, (list, tuple)):
        raw = "\n".join(clean(x) for x in raw if x is not None)
    text = html.unescape(clean(raw))
    items = []
    for part in _SEP_RE.split(text):
        for piece in split_outside_brackets(part, ","):
            piece = _tidy(piece)
            if piece:
                items.append(piece)
    return items


def base_name(item):
    """비교용 이름: 알레르기 괄호, *, 공백 제거 ('돈까스 (1.2.5.6.)' -> '돈까스')"""
    name = _ALLERGY_TAIL_RE.sub("", item).replace("*", "")
    return re.sub(r"\s+", "", name).lower()


def format_kcal(raw):
    """'1083.0 Kcal' -> '1083 Kcal'"""
    text = clean(raw)
    match = re.search(r"\d+(?:\.\d+)?", text.replace(",", ""))
    if not match:
        return text
    number = match.group()
    if "." in number:
        number = number.rstrip("0").rstrip(".")
    return f"{number} Kcal"


def apply_notice(menu, notice):
    """
    원본 메뉴 + 공지 -> 최종 메뉴
    - removed_menus 에 해당하는 항목만 제거 (알레르기 괄호 유무와 관계없이 이름으로 비교)
    - new_menu 항목은 첫 번째로 제거된 자리에 삽입 (제거된 항목이 없으면 맨 뒤에 추가)
    - 나머지 메뉴와 알레르기 괄호는 그대로 유지
    """
    removed = {base_name(m) for m in notice["removed_menus"] if base_name(m)}
    added = split_items(notice["new_menu"])
    result, insert_at = [], None
    for item in menu:
        if base_name(item) in removed:
            if insert_at is None:
                insert_at = len(result)
            continue
        result.append(item)
    if insert_at is None:
        insert_at = len(result)
    existing = {base_name(m) for m in result}
    added = [a for a in added if base_name(a) not in existing]
    return result[:insert_at] + added + result[insert_at:]


# =========================================================
# 데이터베이스 (sqlite3, 기존 테이블 구성 유지)
# =========================================================
SCHEMA = """
CREATE TABLE IF NOT EXISTS users (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    username TEXT UNIQUE NOT NULL,
    password TEXT NOT NULL,
    role TEXT NOT NULL DEFAULT 'user'
);
CREATE TABLE IF NOT EXISTS reviews (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    date TEXT NOT NULL,
    username TEXT NOT NULL,
    rating INTEGER NOT NULL,
    comment TEXT
);
CREATE TABLE IF NOT EXISTS notices (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    date TEXT NOT NULL,
    original_menu TEXT,
    new_menu TEXT NOT NULL,
    reason TEXT
);
"""

# 리뷰는 한 사람당 날짜별 1개
INDEXES = (
    "CREATE UNIQUE INDEX IF NOT EXISTS idx_reviews_date_user ON reviews(date, username)",
    "CREATE INDEX IF NOT EXISTS idx_reviews_date ON reviews(date)",
    "CREATE INDEX IF NOT EXISTS idx_notices_date ON notices(date)",
)


def init_db():
    folder = os.path.dirname(DB_PATH)
    if folder:
        os.makedirs(folder, exist_ok=True)
    conn = sqlite3.connect(DB_PATH, timeout=30)
    try:
        conn.executescript(SCHEMA)
        for ddl in INDEXES:
            try:
                conn.execute(ddl)
            except sqlite3.IntegrityError:
                app.logger.warning("기존 데이터 중복으로 인덱스를 만들지 못했습니다: %s", ddl)
        row = conn.execute("SELECT id, role FROM users WHERE username = ?", (ADMIN_USERNAME,)).fetchone()
        try:
            if row is None:
                conn.execute(
                    "INSERT INTO users (username, password, role) VALUES (?, ?, ?)",
                    (ADMIN_USERNAME, generate_password_hash(ADMIN_PASSWORD), ROLE_ADMIN),
                )
            elif row[1] != ROLE_ADMIN:
                conn.execute("UPDATE users SET role = ? WHERE id = ?", (ROLE_ADMIN, row[0]))
        except sqlite3.IntegrityError:
            pass  # 여러 워커가 동시에 시작한 경우
        conn.commit()
    finally:
        conn.close()


def get_db():
    if "db" not in g:
        conn = sqlite3.connect(DB_PATH, timeout=30)
        conn.row_factory = sqlite3.Row
        g.db = conn
    return g.db


@app.teardown_appcontext
def close_db(_exc):
    conn = g.pop("db", None)
    if conn is not None:
        conn.close()


# =========================================================
# 세션 로그인 / 권한
# =========================================================
def current_user():
    """세션의 user_id 로 DB 에서 매번 역할을 다시 확인 (세션 값 위조/권한 변경 대비)"""
    if "user" in g:
        return g.user
    user = None
    user_id = session.get("user_id")
    if user_id is not None:
        row = get_db().execute("SELECT id, username, role FROM users WHERE id = ?", (user_id,)).fetchone()
        if row is None:
            session.clear()
        else:
            role = ROLE_ADMIN if (row["role"] or "").lower() == ROLE_ADMIN else ROLE_USER
            user = {"id": row["id"], "username": row["username"], "role": role}
    g.user = user
    return user


def login_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if current_user() is None:
            return fail("로그인이 필요합니다.", 401)
        return view(*args, **kwargs)
    return wrapped


def admin_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        user = current_user()
        if user is None or user["role"] != ROLE_ADMIN:
            return fail("관리자만 사용할 수 있습니다.", 403)
        return view(*args, **kwargs)
    return wrapped


# =========================================================
# 페이지
# =========================================================
@app.route("/")
def index():
    return render_template("index.html")


@app.route("/healthz")
def healthz():
    return "ok", 200


# =========================================================
# 회원가입 / 로그인 / 로그아웃 / 유저확인
# =========================================================
@app.route("/api/register", methods=["POST"])
def register():
    data = request_data()
    username = clean(data.get("username"))
    password = clean(data.get("password"))

    if not username or not password:
        return fail("아이디와 비밀번호를 입력해주세요.")
    if not USERNAME_RE.fullmatch(username):
        return fail("아이디는 영문/숫자/_ 4~20자로 입력해주세요.")
    if len(password) < 4:
        return fail("비밀번호는 4자 이상이어야 합니다.")
    if username.lower() == ADMIN_USERNAME.lower():
        return fail("사용할 수 없는 아이디입니다.")

    db = get_db()
    if db.execute("SELECT 1 FROM users WHERE username = ?", (username,)).fetchone():
        return fail("이미 사용 중인 아이디입니다.", 409)
    try:
        # 일반 회원가입은 요청 내용과 관계없이 무조건 'user'
        db.execute("INSERT INTO users (username, password, role) VALUES (?, ?, ?)",
                   (username, generate_password_hash(password), ROLE_USER))
        db.commit()
    except sqlite3.IntegrityError:
        return fail("이미 사용 중인 아이디입니다.", 409)
    return ok("회원가입이 완료되었습니다. 로그인해주세요.", 201)


@app.route("/api/login", methods=["POST"])
def login():
    data = request_data()
    username = clean(data.get("username"))
    password = clean(data.get("password"))
    if not username or not password:
        return fail("아이디와 비밀번호를 입력해주세요.")

    row = get_db().execute("SELECT id, username, password FROM users WHERE username = ?",
                           (username,)).fetchone()
    try:
        valid = row is not None and check_password_hash(row["password"], password)
    except (ValueError, TypeError):
        valid = False
    if not valid:
        return fail("아이디 또는 비밀번호가 올바르지 않습니다.", 401)

    session.clear()
    session.permanent = True
    session["user_id"] = row["id"]
    g.pop("user", None)
    user = current_user()
    session["username"] = user["username"]
    session["role"] = user["role"]
    return ok("로그인되었습니다.", user=user_payload(user))


@app.route("/api/logout", methods=["GET", "POST"])
def logout():
    session.clear()
    g.pop("user", None)
    return ok("로그아웃되었습니다.")


def user_payload(user):
    if user is None:
        return {"logged_in": False, "username": None, "role": None, "is_admin": False}
    return {
        "logged_in": True,
        "username": user["username"],
        "name": user["username"],
        "role": user["role"],
        "is_admin": user["role"] == ROLE_ADMIN,
    }


@app.route("/api/user", methods=["GET"])
def api_user():
    return jsonify(user_payload(current_user()))


# =========================================================
# 익명 리뷰
# =========================================================
@app.route("/api/reviews", methods=["GET"])
def list_reviews():
    user = current_user()
    raw_date = request.args.get("date")
    sql = "SELECT id, date, username, rating, comment FROM reviews"
    params = ()
    if raw_date:
        key = normalize_date(raw_date)
        if not key:
            return fail("날짜 형식이 올바르지 않습니다. (YYYY-MM-DD)")
        sql += " WHERE date = ?"
        params = (key,)
    rows = get_db().execute(sql + " ORDER BY id DESC", params).fetchall()
    return jsonify([
        {
            "id": r["id"],
            "date": r["date"],
            "author": "익명",
            "rating": r["rating"],
            "comment": r["comment"] or "",
            "is_mine": bool(user and r["username"] == user["username"]),
        }
        for r in rows
    ])


@app.route("/api/reviews", methods=["POST"])
@login_required
def create_review():
    user = current_user()
    data = request_data()

    key = normalize_date(data.get("date")) if clean(data.get("date")) else today_str()
    if not key:
        return fail("날짜 형식이 올바르지 않습니다. (YYYY-MM-DD)")
    try:
        rating = int(float(data.get("rating")))
    except (TypeError, ValueError):
        return fail("별점을 선택해주세요.")
    if not 1 <= rating <= 5:
        return fail("별점은 1~5점 사이여야 합니다.")
    comment = clean(data.get("comment") or data.get("content"))
    if not comment:
        return fail("한 줄 평을 입력해주세요.")
    if len(comment) > 200:
        return fail("한 줄 평은 200자 이하로 입력해주세요.")

    db = get_db()
    if db.execute("SELECT 1 FROM reviews WHERE date = ? AND username = ?", (key, user["username"])).fetchone():
        return fail("이 날짜에는 이미 리뷰를 작성했습니다.", 409)
    try:
        cur = db.execute("INSERT INTO reviews (date, username, rating, comment) VALUES (?, ?, ?, ?)",
                         (key, user["username"], rating, comment))
        db.commit()
    except sqlite3.IntegrityError:
        return fail("이 날짜에는 이미 리뷰를 작성했습니다.", 409)
    return ok("리뷰가 등록되었습니다.", 201, id=cur.lastrowid)


@app.route("/api/reviews/<int:review_id>", methods=["DELETE"])
@login_required
def delete_review(review_id):
    user = current_user()
    db = get_db()
    row = db.execute("SELECT username FROM reviews WHERE id = ?", (review_id,)).fetchone()
    if row is None:
        return fail("리뷰를 찾을 수 없습니다.", 404)
    if not (user["role"] == ROLE_ADMIN or row["username"] == user["username"]):
        return fail("본인이 작성한 리뷰만 삭제할 수 있습니다.", 403)
    db.execute("DELETE FROM reviews WHERE id = ?", (review_id,))
    db.commit()
    return ok("리뷰가 삭제되었습니다.")


# =========================================================
# 급식 메뉴 수정 공지 (날짜당 1건, notices.original_menu 에 removed_menus 를 JSON 배열로 저장)
# =========================================================
def decode_removed(raw):
    text = clean(raw)
    if not text:
        return []
    try:
        value = json.loads(text)
        if isinstance(value, list):
            return [clean(v) for v in value if clean(v)]
    except ValueError:
        pass
    return split_items(text)  # 예전 형식(쉼표 구분 문자열) 호환


def notice_payload(row):
    removed = decode_removed(row["original_menu"])
    return {
        "id": row["id"],
        "date": normalize_date(row["date"]) or row["date"],
        "removed_menus": removed,
        "old_menu": ", ".join(removed),
        "new_menu": row["new_menu"] or "",
        "reason": row["reason"] or "",
    }


def notices_by_date():
    """날짜별 공지 1건 (같은 날짜에 여러 건이 남아 있으면 가장 최근 것)"""
    rows = get_db().execute(
        "SELECT id, date, original_menu, new_menu, reason FROM notices ORDER BY id ASC"
    ).fetchall()
    result = {}
    for row in rows:
        item = notice_payload(row)
        key = normalize_date(item["date"])
        if key:
            item["date"] = key
            result[key] = item
    return result


def date_filter_from_args(args):
    key = prefix = start = end = None
    if clean(args.get("date")):
        key = normalize_date(args.get("date"))
        if not key:
            return None, "날짜 형식이 올바르지 않습니다. (YYYY-MM-DD)"
    if clean(args.get("month")):
        prefix = month_prefix(args.get("year"), args.get("month"))
        if not prefix:
            return None, "연도/월 형식이 올바르지 않습니다. (?year=YYYY&month=M)"
    if clean(args.get("start")):
        start = normalize_date(args.get("start"))
        if not start:
            return None, "시작 날짜 형식이 올바르지 않습니다."
    if clean(args.get("end")):
        end = normalize_date(args.get("end"))
        if not end:
            return None, "종료 날짜 형식이 올바르지 않습니다."

    def keep(d):
        return ((not key or d == key)
                and (not prefix or d.startswith(prefix + "-"))
                and (not start or d >= start)
                and (not end or d <= end))
    return keep, None


@app.route("/api/notice", methods=["GET"])
def list_notices():
    keep, error = date_filter_from_args(request.args)
    if error:
        return fail(error)
    notices = [n for d, n in sorted(notices_by_date().items()) if keep(d)]
    return jsonify(notices)


@app.route("/api/notice", methods=["POST"])
@admin_required
def save_notice():
    data = request_data()
    key = normalize_date(data.get("date"))
    removed_raw = data.get("removed_menus")
    if removed_raw is None:
        removed_raw = data.get("old_menu") or data.get("original_menu")
    if not isinstance(removed_raw, (list, tuple, str, type(None))):
        return fail("removed_menus 는 메뉴 이름 배열이어야 합니다.")
    removed = split_items(removed_raw) if isinstance(removed_raw, str) else [
        _tidy(clean(m)) for m in (removed_raw or []) if clean(m)
    ]
    new_menu = clean(data.get("new_menu"))
    reason = clean(data.get("reason"))

    if not key:
        return fail("날짜를 올바르게 입력해주세요. (YYYY-MM-DD)")
    if not removed and not new_menu:
        return fail("제공되지 않는 메뉴 또는 새 메뉴를 입력해주세요.")
    if len(removed) > 50 or len(new_menu) > 1000 or len(reason) > 500:
        return fail("입력 내용이 너무 깁니다.")

    removed_json = json.dumps(removed, ensure_ascii=False)
    db = get_db()
    existing = [r["id"] for r in db.execute("SELECT id, date FROM notices ORDER BY id ASC").fetchall()
                if normalize_date(r["date"]) == key]
    if existing:
        keep_id = existing[-1]
        db.execute("UPDATE notices SET date = ?, original_menu = ?, new_menu = ?, reason = ? WHERE id = ?",
                   (key, removed_json, new_menu, reason, keep_id))
        if len(existing) > 1:
            db.executemany("DELETE FROM notices WHERE id = ?", [(i,) for i in existing[:-1]])
        message, status = "식단 변경 공지가 수정되었습니다.", 200
    else:
        keep_id = db.execute("INSERT INTO notices (date, original_menu, new_menu, reason) VALUES (?, ?, ?, ?)",
                             (key, removed_json, new_menu, reason)).lastrowid
        message, status = "식단 변경 공지가 등록되었습니다.", 201
    db.commit()

    row = db.execute("SELECT id, date, original_menu, new_menu, reason FROM notices WHERE id = ?",
                     (keep_id,)).fetchone()
    return ok(message, status, notice=notice_payload(row))


@app.route("/api/notice/<date_str>", methods=["DELETE"])
@admin_required
def delete_notice(date_str):
    key = normalize_date(date_str)
    if not key:
        return fail("날짜 형식이 올바르지 않습니다. (YYYY-MM-DD)")
    db = get_db()
    ids = [r["id"] for r in db.execute("SELECT id, date FROM notices").fetchall()
           if normalize_date(r["date"]) == key]
    if not ids:
        return fail("해당 날짜의 공지가 없습니다.", 404)
    db.executemany("DELETE FROM notices WHERE id = ?", [(i,) for i in ids])
    db.commit()
    return ok("공지가 삭제되었습니다.", date=key)


# =========================================================
# 급식 CSV
# =========================================================
_csv_cache = {"mtime": None, "rows": []}
_csv_lock = threading.Lock()


def _find_col(header, *names):
    normalized = [re.sub(r"\s+", "", h).lstrip("﻿").upper() for h in header]
    for name in names:
        if name.upper() in normalized:
            return normalized.index(name.upper())
    return None


def _cell(row, idx):
    return row[idx] if idx is not None and idx < len(row) else ""


def parse_meal_csv(path):
    with open(path, "rb") as f:
        raw = f.read()
    for encoding in ("utf-8-sig", "cp949"):
        try:
            text = raw.decode(encoding)
            break
        except UnicodeDecodeError:
            continue
    else:
        text = raw.decode("utf-8", errors="replace")

    rows = list(csv.reader(io.StringIO(text.lstrip("﻿"))))
    if not rows:
        return []
    header = rows[0]
    date_idx = _find_col(header, "급식일자", "MLSV_YMD")
    menu_idx = _find_col(header, "요리명", "DDISH_NM")
    kcal_idx = _find_col(header, "칼로리정보", "CAL_INFO")
    meal_idx = _find_col(header, "식사명", "MMEAL_SC_NM")
    if date_idx is None or menu_idx is None:
        app.logger.warning("급식 CSV 에 급식일자/요리명 컬럼이 없습니다: %s", path)
        return []

    merged = {}
    for row in rows[1:]:
        key = normalize_date(_cell(row, date_idx))
        if not key:
            continue
        meal = clean(_cell(row, meal_idx))
        merged[(key, meal)] = {
            "date": key,
            "meal": meal,
            "menu": split_menu(_cell(row, menu_idx)),
            "kcal": format_kcal(_cell(row, kcal_idx)),
        }
    return list(merged.values())


def load_meals():
    """CSV 가 수정되면(mtime 변경) 자동으로 다시 읽음"""
    try:
        mtime = os.path.getmtime(CSV_PATH)
    except OSError:
        app.logger.warning("급식 CSV 를 찾을 수 없습니다: %s", CSV_PATH)
        return []
    with _csv_lock:
        if _csv_cache["mtime"] != mtime:
            try:
                _csv_cache["rows"] = parse_meal_csv(CSV_PATH)
            except (OSError, csv.Error) as exc:
                app.logger.warning("급식 CSV 읽기 실패: %s", exc)
                _csv_cache["rows"] = []
            _csv_cache["mtime"] = mtime
        return _csv_cache["rows"]


def _meal_rank(meal, preferred):
    if meal == preferred:
        return -1
    return MEAL_PRIORITY.index(meal) if meal in MEAL_PRIORITY else len(MEAL_PRIORITY)


def review_stats():
    stats = {}
    for row in get_db().execute("SELECT date, AVG(rating) AS avg, COUNT(*) AS cnt FROM reviews GROUP BY date"):
        key = normalize_date(row["date"])
        if key:
            stats[key] = (round(row["avg"], 1) if row["avg"] is not None else None, row["cnt"])
    return stats


def build_meals(keep, meal_param):
    """
    날짜별 급식(기본 중식 1건) + 공지 병합.
    - menu       : CSV 원본 메뉴 (알레르기 괄호 그대로)
    - notice     : 공지가 있는 날짜만 {removed_menus, new_menu, reason}, 없으면 null
    - final_menu : 공지를 반영한 최종 메뉴
    """
    by_date = {}
    for rec in load_meals():
        if keep(rec["date"]):
            by_date.setdefault(rec["date"], []).append(rec)

    notices = {d: n for d, n in notices_by_date().items() if keep(d)}
    preferred = meal_param if meal_param and meal_param != "all" else DEFAULT_MEAL
    stats = review_stats()
    result = []

    for key in sorted(set(by_date) | set(notices)):
        records = sorted(by_date.get(key, []), key=lambda r: _meal_rank(r["meal"], preferred))
        if meal_param and meal_param != "all":
            records = [r for r in records if r["meal"] == meal_param]
            if not records and key not in notices:
                continue
        elif not meal_param:
            records = records[:1]

        entries = [{"date": key, "menu": list(r["menu"]), "kcal": r["kcal"], "meal": r["meal"]} for r in records]
        if not entries:
            entries = [{"date": key, "menu": [], "kcal": "", "meal": preferred}]

        notice = notices.get(key)
        avg, cnt = stats.get(key, (None, 0))
        for i, entry in enumerate(entries):
            target_notice = notice if i == 0 else None  # 공지는 대표 식사(중식)에만 적용
            entry["notice"] = ({
                "removed_menus": target_notice["removed_menus"],
                "new_menu": target_notice["new_menu"],
                "reason": target_notice["reason"],
            } if target_notice else None)
            entry["final_menu"] = apply_notice(entry["menu"], target_notice) if target_notice else list(entry["menu"])
            entry["changed"] = target_notice is not None
            entry["avg_rating"] = avg
            entry["review_count"] = cnt
            if entry["menu"] or entry["final_menu"]:
                result.append(entry)
    return result


@app.route("/api/meals", methods=["GET"])
def api_meals():
    keep, error = date_filter_from_args(request.args)
    if error:
        return fail(error)
    return jsonify(build_meals(keep, clean(request.args.get("meal"))))


# =========================================================
# 에러 처리
# =========================================================
@app.errorhandler(HTTPException)
def handle_http_error(exc):
    if request.path.startswith("/api/"):
        return jsonify({"success": False, "message": exc.description}), exc.code
    return exc


@app.errorhandler(Exception)
def handle_unexpected_error(exc):
    if isinstance(exc, HTTPException):
        return handle_http_error(exc)
    app.logger.exception("Unhandled error: %s", exc)
    if request.path.startswith("/api/"):
        return jsonify({"success": False, "message": "서버 오류가 발생했습니다."}), 500
    return "서버 오류가 발생했습니다.", 500


init_db()

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host='0.0.0.0', port=port)
