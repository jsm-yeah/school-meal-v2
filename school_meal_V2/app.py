# -*- coding: utf-8 -*-
"""
학교 급식 달력 서버 (Flask)

환경변수
  SECRET_KEY     세션 암호화 키 (필수 권장. 없으면 서버가 켜질 때마다 임시 키를 만들어 로그인이 풀림)
  DATABASE_URL   있으면 Postgres(psycopg2), 없으면 SQLite(data.db)
  ADMIN_ID       관리자 아이디  (ADMIN_ID, ADMIN_PW 둘 다 있을 때만 관리자 계정 생성)
  ADMIN_PW       관리자 비밀번호
  NEIS_KEY       나이스 교육정보 개방 포털 인증키
  NEIS_ATPT      시도교육청코드 (예: F10)
  NEIS_SCHUL     행정표준코드(학교코드) (예: 7380042)
  DATABASE_PATH  (선택) SQLite 파일 경로
  MEAL_CSV       (선택) 예비 식단 CSV 경로 (기본: meals.csv)
"""
# --- 파이썬에 기본으로 들어 있는 도구들 ---
# calendar: 그 달의 마지막 날 계산 / csv: CSV 읽기·쓰기 / html: &amp; 같은 글자 되돌리기
# io: 메모리 안에서 파일처럼 쓰기 / json: JSON 변환 / logging: 서버 로그 / os: 환경변수·파일 경로
# re: 정규식(글자 패턴 찾기) / secrets: 무작위 키 만들기 / sqlite3: SQLite DB
# threading: 동시에 들어온 요청끼리 꼬이지 않게 잠그기 / time: 현재 시각(초) / zipfile: zip 만들기
import calendar
import csv
import html
import io
import json
import logging
import os
import re
import secrets
import sqlite3
import threading
import time
import zipfile
from datetime import date, datetime, timedelta, timezone
from functools import wraps

# --- 따로 설치하는 도구들 (requirements.txt) ---
# requests: 나이스 서버에 요청 보내기 / flask: 웹 서버 / werkzeug: 비밀번호 해시(Flask 와 함께 설치됨)
import requests
from flask import Flask, Response, g, jsonify, render_template, request, session
from werkzeug.exceptions import HTTPException
from werkzeug.security import check_password_hash, generate_password_hash

# app.py 가 들어 있는 폴더의 절대 경로 (data.db, meals.csv, .env 를 여기서 찾는다)
BASE_DIR = os.path.dirname(os.path.abspath(__file__))


def load_dotenv(path):
    """로컬 테스트용: .env 파일(KEY=VALUE)이 있으면 환경변수로 읽는다. 이미 있는 값은 덮어쓰지 않는다."""
    if not os.path.isfile(path):
        return
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            key, value = line.split("=", 1)
            os.environ.setdefault(key.strip(), value.strip().strip('"').strip("'"))


load_dotenv(os.path.join(BASE_DIR, ".env"))

# =========================================================
# 설정
# =========================================================
# DB 주소가 있으면 Postgres 를 쓰고(USE_PG=True), 없으면 SQLite 파일(data.db)을 쓴다
DATABASE_URL = (os.environ.get("DATABASE_URL") or "").strip()
USE_PG = bool(DATABASE_URL)
DB_PATH = os.environ.get("DATABASE_PATH") or os.path.join(BASE_DIR, "data.db")
CSV_PATH = os.environ.get("MEAL_CSV") or os.path.join(BASE_DIR, "meals.csv")

# 관리자 계정 정보. 코드에 직접 적지 않고 환경변수에서만 읽는다
ADMIN_ID = (os.environ.get("ADMIN_ID") or "").strip()
ADMIN_PW = os.environ.get("ADMIN_PW") or ""

# 나이스 급식 API 주소와 인증 정보
NEIS_URL = "https://open.neis.go.kr/hub/mealServiceDietInfo"
NEIS_KEY = (os.environ.get("NEIS_KEY") or "").strip()
NEIS_ATPT = (os.environ.get("NEIS_ATPT") or "").strip()
NEIS_SCHUL = (os.environ.get("NEIS_SCHUL") or "").strip()
NEIS_TIMEOUT = 5                 # 초
NEIS_CACHE_SECONDS = 6 * 60 * 60  # 성공한 달은 6시간 재사용
NEIS_RETRY_SECONDS = 5 * 60       # 실패한 달은 5분 뒤에 다시 시도 (그동안은 CSV)

# 한국 시간(UTC+9). Render 서버 시계는 UTC 라서 '오늘'을 한국 기준으로 계산하려고 쓴다
KST = timezone(timedelta(hours=9))
# 권한 이름과 식사 이름을 상수로 둔다 (오타로 인한 버그 방지)
ROLE_ADMIN = "admin"
ROLE_USER = "user"
LUNCH = "중식"
# 아이디 규칙: 영문/숫자/밑줄 4~20자
USERNAME_RE = re.compile(r"[A-Za-z0-9_]{4,20}")

# DB 종류마다 '중복 저장 오류'의 이름이 달라서, IntegrityError 라는 한 이름으로 맞춰 둔다
# psycopg2 는 Postgres 를 쓸 때만 불러오므로, 로컬(SQLite)에서는 설치하지 않아도 된다
if USE_PG:
    import psycopg2
    IntegrityError = psycopg2.IntegrityError
else:
    IntegrityError = sqlite3.IntegrityError

# Flask 앱(웹 서버 본체) 만들기
app = Flask(__name__)
app.logger.setLevel(logging.INFO)

# 세션 쿠키를 서명하는 비밀 키. 이 키를 모르면 로그인 정보를 위조할 수 없다
app.secret_key = os.environ.get("SECRET_KEY")
if not app.secret_key:
    app.secret_key = secrets.token_hex(32)
    app.logger.warning("SECRET_KEY 환경변수가 없습니다. 임시 키를 사용하므로 서버가 재시작되면 모두 로그아웃됩니다.")

# 세션 쿠키 설정: 자바스크립트가 못 읽게(HTTPONLY), 다른 사이트에서 보낸 요청에는 안 실리게(SAMESITE),
# Render 에서는 https 로만 보내게(SECURE), 로그인은 7일 유지
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=bool(os.environ.get("RENDER")),
    PERMANENT_SESSION_LIFETIME=timedelta(days=7),
)
try:
    # JSON 응답에서 한글을 \uXXXX 로 바꾸지 않고, 키 순서도 그대로 보낸다
    # (Flask 버전에 따라 설정 방법이 달라서 try / except 로 둘 다 대응)
    app.json.ensure_ascii = False
    app.json.sort_keys = False
except AttributeError:
    app.config["JSON_AS_ASCII"] = False
    app.config["JSON_SORT_KEYS"] = False


# =========================================================
# 공통 유틸
# =========================================================
# 한국 시간 기준 오늘 날짜
def today_kst():
    return datetime.now(KST).date()


# None 은 빈 문자열로, 나머지는 앞뒤 공백을 없앤 문자열로 바꾼다
def clean(value):
    return "" if value is None else str(value).strip()


# 요청 본문을 dict 로 읽는다 (JSON 이면 JSON, 아니면 폼 데이터)
def request_data():
    data = request.get_json(silent=True)
    if isinstance(data, dict):
        return data
    return request.form.to_dict()


# 성공 응답 만들기: {"success": true, "message": ...} 에 추가 값을 덧붙인다
def ok(message, status=200, **extra):
    payload = {"success": True, "message": message}
    payload.update(extra)
    return jsonify(payload), status


# 실패 응답 만들기 (상태코드 기본값 400 = 잘못된 요청)
def fail(message, status=400):
    return jsonify({"success": False, "message": message}), status


# 연(4자리)·월·일 숫자를 찾는 정규식. 사이에 -, ., / 같은 글자가 있어도 된다
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


def parse_year_month(year, month):
    """year=2026, month=3 / month='2026-03' / month='202603' -> (2026, 3)"""
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
    return y, m


# =========================================================
# 메뉴 가공 (알레르기 번호 괄호는 절대 삭제하지 않음)
# =========================================================
# 메뉴 사이 구분자: <br/> 또는 줄바꿈
_SEP_RE = re.compile(r"<\s*br\s*/?\s*>|\r\n|\r|\n", re.IGNORECASE)
# 메뉴 끝의 알레르기 괄호 '(1.2.5.6.)' 를 찾는 정규식. 이름을 비교할 때만 떼어 내고, 응답에서는 지우지 않는다
_ALLERGY_TAIL_RE = re.compile(r"\s*\(\s*(?:\d{1,2}\s*\.?\s*)+\)\s*$")
# 여는 괄호 / 닫는 괄호로 취급할 글자들
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


# 연속된 공백을 한 칸으로 줄이고 앞뒤 공백을 없앤다
def _tidy(text):
    return re.sub(r"\s+", " ", text).strip()


def split_menu(raw):
    """'쌀밥  <br/>돈까스  (1.2.5.6.)' -> ['쌀밥', '돈까스 (1.2.5.6.)']"""
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
    """원본 메뉴에서 removed_menus 를 빼고, 첫 번째로 빠진 자리에 new_menu 를 넣은 최종 메뉴"""
    # 빼야 할 메뉴 이름 집합과, 새로 넣을 메뉴 목록
    removed = {base_name(m) for m in notice["removed_menus"] if base_name(m)}
    added = split_items(notice["new_menu"])
    result, insert_at = [], None
    # 원본을 차례로 보면서 빠질 메뉴는 건너뛰고, 처음 빠진 위치(insert_at)를 기억한다
    for item in menu:
        if base_name(item) in removed:
            if insert_at is None:
                insert_at = len(result)
            continue
        result.append(item)
    if insert_at is None:
        insert_at = len(result)
    # 이미 남아 있는 메뉴와 이름이 같은 대체 메뉴는 중복으로 넣지 않는다
    existing = {base_name(m) for m in result}
    added = [a for a in added if base_name(a) not in existing]
    return result[:insert_at] + added + result[insert_at:]


# =========================================================
# 데이터베이스 (DATABASE_URL 있으면 Postgres, 없으면 SQLite)
# =========================================================
def sql(query):
    """SQL 자리표시자 통일: 코드에서는 항상 ? 로 쓰고, Postgres 일 때만 %s 로 바꾼다."""
    return query.replace("?", "%s") if USE_PG else query


# DB 연결 만들기 (Postgres 는 10초 안에 연결되지 않으면 포기)
def connect():
    if USE_PG:
        return psycopg2.connect(DATABASE_URL, connect_timeout=10)
    folder = os.path.dirname(DB_PATH)
    if folder:
        os.makedirs(folder, exist_ok=True)
    return sqlite3.connect(DB_PATH, timeout=30)


# SELECT 실행 → 각 행을 {'열이름': 값} dict 로 바꿔 리스트로 돌려준다 (두 DB 에서 결과 모양이 같아진다)
# 값은 SQL 글자에 직접 붙이지 않고 params 로 따로 넘긴다 → SQL 인젝션 방지
def _fetch(conn, query, params=()):
    cur = conn.cursor()
    try:
        cur.execute(sql(query), tuple(params))
        cols = [c[0] for c in cur.description]
        return [dict(zip(cols, row)) for row in cur.fetchall()]
    finally:
        cur.close()


def _execute(conn, query, params=(), returning_id=False):
    """INSERT/UPDATE/DELETE 실행 후 커밋. returning_id=True 면 새 행의 id, 아니면 바뀐 행 수를 돌려준다."""
    cur = conn.cursor()
    try:
        if returning_id and USE_PG:
            query += " RETURNING id"
        cur.execute(sql(query), tuple(params))
        if returning_id:
            result = cur.fetchone()[0] if USE_PG else cur.lastrowid
        else:
            result = cur.rowcount
        conn.commit()
        return result
    except Exception:
        conn.rollback()
        raise
    finally:
        cur.close()


# 요청 하나당 DB 연결 하나를 만들어 g(요청 동안만 살아 있는 저장소)에 보관한다
def get_db():
    if "db" not in g:
        g.db = connect()
    return g.db


# 아래 세 함수가 라우트에서 실제로 쓰는 DB 도구: 여러 행 조회 / 한 행 조회 / 쓰기
def db_all(query, params=()):
    return _fetch(get_db(), query, params)


def db_one(query, params=()):
    rows = _fetch(get_db(), query, params)
    return rows[0] if rows else None


def db_exec(query, params=(), returning_id=False):
    return _execute(get_db(), query, params, returning_id)


# 요청이 끝나면 Flask 가 자동으로 불러서 DB 연결을 닫는다
@app.teardown_appcontext
def close_db(_exc):
    conn = g.pop("db", None)
    if conn is not None:
        conn.close()


# 테이블·인덱스를 만드는 SQL 목록. 자동 증가 id 문법만 DB 마다 달라서 pk 로 바꿔 끼운다
def schema_statements():
    pk = "SERIAL PRIMARY KEY" if USE_PG else "INTEGER PRIMARY KEY AUTOINCREMENT"
    return (
        f"""CREATE TABLE IF NOT EXISTS users (
            id {pk},
            username TEXT UNIQUE NOT NULL,
            password TEXT NOT NULL,
            role TEXT NOT NULL DEFAULT 'user'
        )""",
        f"""CREATE TABLE IF NOT EXISTS reviews (
            id {pk},
            date TEXT NOT NULL,
            username TEXT NOT NULL,
            rating INTEGER NOT NULL,
            comment TEXT
        )""",
        f"""CREATE TABLE IF NOT EXISTS notices (
            id {pk},
            date TEXT NOT NULL,
            original_menu TEXT,
            new_menu TEXT NOT NULL,
            reason TEXT
        )""",
        # 리뷰는 한 사람당 날짜별 1개
        "CREATE UNIQUE INDEX IF NOT EXISTS idx_reviews_date_user ON reviews(date, username)",
        "CREATE INDEX IF NOT EXISTS idx_reviews_date ON reviews(date)",
        "CREATE INDEX IF NOT EXISTS idx_notices_date ON notices(date)",
    )


# 서버가 켜질 때 한 번 실행: 테이블 준비 → 관리자 계정 준비
def init_db():
    conn = connect()
    try:
        for statement in schema_statements():
            try:
                _execute(conn, statement)
            except Exception as exc:  # 여러 워커가 동시에 시작했거나, 기존 데이터 중복으로 인덱스 생성 실패
                app.logger.warning("DB 초기화 문장을 건너뜁니다 (%s): %s", type(exc).__name__, statement.split("(")[0].strip())

        if not (ADMIN_ID and ADMIN_PW):
            app.logger.warning("ADMIN_ID / ADMIN_PW 환경변수가 없어 관리자 계정을 만들지 않았습니다.")
            return
        rows = _fetch(conn, "SELECT id, password, role FROM users WHERE username = ?", (ADMIN_ID,))
        try:
            if not rows:
                _execute(conn, "INSERT INTO users (username, password, role) VALUES (?, ?, ?)",
                         (ADMIN_ID, generate_password_hash(ADMIN_PW), ROLE_ADMIN))
            elif rows[0]["role"] != ROLE_ADMIN or not verify_password(rows[0]["password"], ADMIN_PW):
                # 환경변수의 비밀번호가 항상 기준
                _execute(conn, "UPDATE users SET password = ?, role = ? WHERE id = ?",
                         (generate_password_hash(ADMIN_PW), ROLE_ADMIN, rows[0]["id"]))
        except IntegrityError:
            pass  # 다른 워커가 먼저 만든 경우
    finally:
        conn.close()


# 입력한 비밀번호가 저장된 해시와 맞는지 확인 (저장된 값이 이상해도 오류 대신 False)
def verify_password(stored_hash, password):
    try:
        return bool(stored_hash) and check_password_hash(stored_hash, password)
    except (ValueError, TypeError):
        return False


# =========================================================
# 세션 로그인 / 권한 (모든 권한 검사는 서버에서 DB 기준으로 한다)
# =========================================================
# 세션 쿠키의 user_id 로 DB 에서 사용자를 찾아 돌려준다 (로그인 안 했으면 None)
# 역할(role)은 세션에 저장하지 않고 매번 DB 에서 읽으므로, 쿠키를 고쳐도 관리자가 될 수 없다
def current_user():
    if "user" in g:
        return g.user
    user = None
    user_id = session.get("user_id")
    if user_id is not None:
        row = db_one("SELECT id, username, role FROM users WHERE id = ?", (user_id,))
        if row is None:
            session.clear()
        else:
            role = ROLE_ADMIN if (row["role"] or "").lower() == ROLE_ADMIN else ROLE_USER
            user = {"id": row["id"], "username": row["username"], "role": role}
    g.user = user
    return user


# 데코레이터: 로그인하지 않았으면 401 로 막는다. 라우트 함수 위에 @login_required 로 붙여 쓴다
def login_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if current_user() is None:
            return fail("로그인이 필요합니다.", 401)
        return view(*args, **kwargs)
    return wrapped


# 데코레이터: 관리자가 아니면 403 으로 막는다
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
# 첫 화면: templates/index.html 을 그대로 보낸다
@app.route("/")
def index():
    return render_template("index.html")


# 서버가 살아 있는지 확인하는 주소 (Render 상태 확인용)
@app.route("/healthz")
def healthz():
    return "ok", 200


# =========================================================
# 회원가입 / 로그인 / 로그아웃 / 유저확인 / 탈퇴
# =========================================================
# 회원가입: 입력 검사 → 아이디 중복 확인 → 비밀번호는 해시로 바꿔 저장 (원래 비밀번호는 저장하지 않는다)
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
    if username.lower() in {"admin", ADMIN_ID.lower()}:
        return fail("사용할 수 없는 아이디입니다.")

    if db_one("SELECT id FROM users WHERE username = ?", (username,)):
        return fail("이미 사용 중인 아이디입니다.", 409)
    try:
        # 일반 회원가입은 요청 내용과 관계없이 무조건 'user'
        db_exec("INSERT INTO users (username, password, role) VALUES (?, ?, ?)",
                (username, generate_password_hash(password), ROLE_USER))
    except IntegrityError:
        return fail("이미 사용 중인 아이디입니다.", 409)
    return ok("회원가입이 완료되었습니다. 로그인해주세요.", 201)


# 로그인: 비밀번호가 맞으면 세션에 user_id 만 저장한다
@app.route("/api/login", methods=["POST"])
def login():
    data = request_data()
    username = clean(data.get("username"))
    password = clean(data.get("password"))
    if not username or not password:
        return fail("아이디와 비밀번호를 입력해주세요.")

    row = db_one("SELECT id, password FROM users WHERE username = ?", (username,))
    if row is None or not verify_password(row["password"], password):
        return fail("아이디 또는 비밀번호가 올바르지 않습니다.", 401)

    session.clear()
    session.permanent = True
    session["user_id"] = row["id"]
    g.pop("user", None)
    return ok("로그인되었습니다.", user=user_payload(current_user()))


# 로그아웃: 세션 비우기
@app.route("/api/logout", methods=["GET", "POST"])
def logout():
    session.clear()
    g.pop("user", None)
    return ok("로그아웃되었습니다.")


# 프론트에 보내는 사용자 정보 모양
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


# 지금 로그인한 사용자 정보 (로그인 안 했으면 logged_in: false)
@app.route("/api/user", methods=["GET"])
def api_user():
    return jsonify(user_payload(current_user()))


@app.route("/api/user", methods=["DELETE"])
@login_required
def delete_account():
    """탈퇴: 로그인한 본인의 계정과 본인이 쓴 리뷰를 모두 삭제하고 로그아웃"""
    user = current_user()
    if user["role"] == ROLE_ADMIN:
        return fail("관리자 계정은 탈퇴할 수 없습니다.", 400)
    db_exec("DELETE FROM reviews WHERE username = ?", (user["username"],))
    db_exec("DELETE FROM users WHERE id = ?", (user["id"],))
    session.clear()
    g.pop("user", None)
    return ok("탈퇴가 완료되었습니다. 계정과 작성한 리뷰가 모두 삭제되었습니다.")


# =========================================================
# 익명 리뷰
# =========================================================
# 리뷰 목록. 작성자 아이디는 보내지 않고 '익명'과 내 글인지(is_mine)만 알려준다
@app.route("/api/reviews", methods=["GET"])
def list_reviews():
    user = current_user()
    raw_date = request.args.get("date")
    if raw_date:
        key = normalize_date(raw_date)
        if not key:
            return fail("날짜 형식이 올바르지 않습니다. (YYYY-MM-DD)")
        rows = db_all("SELECT id, date, username, rating, comment FROM reviews WHERE date = ? ORDER BY id DESC", (key,))
    else:
        rows = db_all("SELECT id, date, username, rating, comment FROM reviews ORDER BY id DESC")
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


# 리뷰 작성 (로그인 필요): 날짜·별점·내용 검사 → 같은 날짜에 이미 썼는지 확인 → 저장
@app.route("/api/reviews", methods=["POST"])
@login_required
def create_review():
    user = current_user()
    data = request_data()

    key = normalize_date(data.get("date")) if clean(data.get("date")) else today_kst().strftime("%Y-%m-%d")
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

    if db_one("SELECT id FROM reviews WHERE date = ? AND username = ?", (key, user["username"])):
        return fail("이 날짜에는 이미 리뷰를 작성했습니다.", 409)
    try:
        new_id = db_exec("INSERT INTO reviews (date, username, rating, comment) VALUES (?, ?, ?, ?)",
                         (key, user["username"], rating, comment), returning_id=True)
    except IntegrityError:
        return fail("이 날짜에는 이미 리뷰를 작성했습니다.", 409)
    return ok("리뷰가 등록되었습니다.", 201, id=new_id)


@app.route("/api/reviews/<int:review_id>", methods=["DELETE"])
@login_required
def delete_review(review_id):
    """내 리뷰는 본인만, 다른 사람 리뷰는 관리자만 삭제"""
    user = current_user()
    row = db_one("SELECT username FROM reviews WHERE id = ?", (review_id,))
    if row is None:
        return fail("리뷰를 찾을 수 없습니다.", 404)
    if not (user["role"] == ROLE_ADMIN or row["username"] == user["username"]):
        return fail("본인이 작성한 리뷰만 삭제할 수 있습니다.", 403)
    db_exec("DELETE FROM reviews WHERE id = ?", (review_id,))
    return ok("리뷰가 삭제되었습니다.")


# =========================================================
# 급식 변경 공지 (날짜당 1건, notices.original_menu 에 removed_menus 를 JSON 배열로 저장)
# =========================================================
# DB 에 JSON 글자로 저장된 '제공되지 않는 메뉴' 목록을 파이썬 리스트로 되돌린다
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


# DB 의 공지 한 행을 프론트에 보내는 모양으로 바꾼다
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
    result = {}
    for row in db_all("SELECT id, date, original_menu, new_menu, reason FROM notices ORDER BY id ASC"):
        item = notice_payload(row)
        key = normalize_date(item["date"])
        if key:
            item["date"] = key
            result[key] = item
    return result


def period_from_args(args):
    """
    요청에서 조회 기간을 읽는다. -> ((연, 월), 특정 날짜 또는 None), 에러 메시지
    ?year=YYYY&month=M / ?month=YYYY-MM / ?date=YYYY-MM-DD / 없으면 이번 달
    """
    if clean(args.get("date")):
        key = normalize_date(args.get("date"))
        if not key:
            return None, "날짜 형식이 올바르지 않습니다. (YYYY-MM-DD)"
        return ((int(key[:4]), int(key[5:7])), key), None
    if clean(args.get("month")) or clean(args.get("year")):
        ym = parse_year_month(args.get("year"), args.get("month"))
        if not ym:
            return None, "연도/월 형식이 올바르지 않습니다. (?year=YYYY&month=M)"
        return (ym, None), None
    today = today_kst()
    return ((today.year, today.month), None), None


# 날짜가 조회 기간(특정 하루 또는 그 달) 안에 있는지
def in_period(day, ym, only_date):
    if only_date:
        return day == only_date
    return day.startswith(f"{ym[0]:04d}-{ym[1]:02d}-")


# 공지 목록 (로그인 없이 누구나 볼 수 있다)
@app.route("/api/notice", methods=["GET"])
def list_notices():
    period, error = period_from_args(request.args)
    if error:
        return fail(error)
    ym, only_date = period
    return jsonify([n for d, n in sorted(notices_by_date().items()) if in_period(d, ym, only_date)])


# 공지 등록·수정 (관리자만). 같은 날짜에 이미 있으면 새로 만들지 않고 덮어쓴다
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
    existing = [r["id"] for r in db_all("SELECT id, date FROM notices ORDER BY id ASC")
                if normalize_date(r["date"]) == key]
    if existing:  # 같은 날짜에 이미 공지가 있으면 덮어쓰기
        keep_id = existing[-1]
        db_exec("UPDATE notices SET date = ?, original_menu = ?, new_menu = ?, reason = ? WHERE id = ?",
                (key, removed_json, new_menu, reason, keep_id))
        for old_id in existing[:-1]:
            db_exec("DELETE FROM notices WHERE id = ?", (old_id,))
        message, status = "식단 변경 공지가 수정되었습니다.", 200
    else:
        keep_id = db_exec("INSERT INTO notices (date, original_menu, new_menu, reason) VALUES (?, ?, ?, ?)",
                          (key, removed_json, new_menu, reason), returning_id=True)
        message, status = "식단 변경 공지가 등록되었습니다.", 201

    row = db_one("SELECT id, date, original_menu, new_menu, reason FROM notices WHERE id = ?", (keep_id,))
    return ok(message, status, notice=notice_payload(row))


# 공지 삭제 (관리자만): 그 날짜의 공지를 지운다
@app.route("/api/notice/<date_str>", methods=["DELETE"])
@admin_required
def delete_notice(date_str):
    key = normalize_date(date_str)
    if not key:
        return fail("날짜 형식이 올바르지 않습니다. (YYYY-MM-DD)")
    ids = [r["id"] for r in db_all("SELECT id, date FROM notices") if normalize_date(r["date"]) == key]
    if not ids:
        return fail("해당 날짜의 공지가 없습니다.", 404)
    for notice_id in ids:
        db_exec("DELETE FROM notices WHERE id = ?", (notice_id,))
    return ok("공지가 삭제되었습니다.", date=key)


# =========================================================
# 식단 데이터 1: 나이스 API (달 단위, 6시간 메모리 저장)
# =========================================================
_neis_cache = {}   # (연, 월) -> (만료 시각, 기록 리스트 또는 None)
_neis_lock = threading.Lock()


def fetch_neis_month(year, month):
    """나이스에서 한 달치 중식을 받아온다. 실패하거나 데이터가 없으면 None."""
    if not (NEIS_KEY and NEIS_ATPT and NEIS_SCHUL):
        return None
    # 1) 최근에 받아 둔 결과가 아직 유효하면 나이스를 다시 부르지 않고 그대로 쓴다
    cache_key = (year, month)
    now = time.time()
    with _neis_lock:
        cached = _neis_cache.get(cache_key)
    if cached and cached[0] > now:
        return cached[1]

    # 2) 없으면 나이스에 그 달 1일~말일의 중식을 요청한다 (5초 안에 답이 없으면 실패 처리)
    records = None
    last_day = calendar.monthrange(year, month)[1]
    try:
        resp = requests.get(NEIS_URL, timeout=NEIS_TIMEOUT, params={
            "KEY": NEIS_KEY,
            "Type": "json",
            "pIndex": 1,
            "pSize": 100,
            "ATPT_OFCDC_SC_CODE": NEIS_ATPT,
            "SD_SCHUL_CODE": NEIS_SCHUL,
            "MMEAL_SC_CODE": 2,  # 중식
            "MLSV_FROM_YMD": f"{year:04d}{month:02d}01",
            "MLSV_TO_YMD": f"{year:04d}{month:02d}{last_day:02d}",
        })
        resp.raise_for_status()
        data = resp.json()
        info = data.get("mealServiceDietInfo")
        if not info:
            # 데이터 없음(INFO-200), 키 오류(ERROR-290) 등은 RESULT 로만 온다
            result = data.get("RESULT") or {}
            app.logger.warning("나이스 응답에 식단이 없습니다 (%04d-%02d): %s %s",
                               year, month, result.get("CODE", "?"), result.get("MESSAGE", ""))
        else:
            rows = next((part["row"] for part in info if isinstance(part, dict) and "row" in part), [])
            found = []
            for row in rows:
                day = normalize_date(row.get("MLSV_YMD"))
                menu = split_menu(row.get("DDISH_NM"))
                if day and menu:
                    found.append({
                        "date": day,
                        "meal": clean(row.get("MMEAL_SC_NM")) or LUNCH,
                        "menu": menu,
                        "kcal": format_kcal(row.get("CAL_INFO")),
                    })
            records = found or None
    except (requests.RequestException, ValueError, KeyError, TypeError, AttributeError) as exc:
        # 예외 메시지에는 인증키가 들어간 주소가 포함될 수 있으므로 종류만 기록한다
        app.logger.warning("나이스 요청 실패 (%04d-%02d): %s", year, month, type(exc).__name__)

    # 3) 결과를 기억해 둔다. 성공은 6시간, 실패는 5분만
    ttl = NEIS_CACHE_SECONDS if records else NEIS_RETRY_SECONDS
    with _neis_lock:
        _neis_cache[cache_key] = (now + ttl, records)
    return records


# =========================================================
# 식단 데이터 2: meals.csv (나이스 실패 시 예비)
# =========================================================
_csv_cache = {"mtime": None, "months": {}}
_csv_lock = threading.Lock()


# CSV 첫 줄(머리글)에서 원하는 열이 몇 번째인지 찾는다 (없으면 None)
def _find_col(header, *names):
    normalized = [re.sub(r"\s+", "", h).lstrip("﻿").upper() for h in header]
    for name in names:
        if name.upper() in normalized:
            return normalized.index(name.upper())
    return None


# 행에서 idx 번째 칸의 값 (칸이 없으면 빈 문자열)
def _cell(row, idx):
    return row[idx] if idx is not None and idx < len(row) else ""


def parse_meal_csv(path):
    """CSV 전체를 읽어 {'YYYY-MM': [중식 기록...]} 으로 묶는다."""
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
        return {}
    header = rows[0]
    date_idx = _find_col(header, "급식일자", "MLSV_YMD")
    menu_idx = _find_col(header, "요리명", "DDISH_NM")
    kcal_idx = _find_col(header, "칼로리정보", "CAL_INFO")
    meal_idx = _find_col(header, "식사명", "MMEAL_SC_NM")
    if date_idx is None or menu_idx is None:
        app.logger.warning("급식 CSV 에 급식일자/요리명 열이 없습니다: %s", path)
        return {}

    by_day = {}
    for row in rows[1:]:
        day = normalize_date(_cell(row, date_idx))
        if not day:
            continue
        meal = clean(_cell(row, meal_idx))
        if meal_idx is not None and meal != LUNCH:
            continue
        by_day[day] = {
            "date": day,
            "meal": meal or LUNCH,
            "menu": split_menu(_cell(row, menu_idx)),
            "kcal": format_kcal(_cell(row, kcal_idx)),
        }
    months = {}
    for day, record in by_day.items():
        months.setdefault(day[:7], []).append(record)
    return months


def csv_month(year, month):
    """CSV 가 수정되면(mtime 변경) 자동으로 다시 읽는다."""
    try:
        mtime = os.path.getmtime(CSV_PATH)
    except OSError:
        app.logger.warning("급식 CSV 를 찾을 수 없습니다: %s", CSV_PATH)
        return []
    with _csv_lock:
        if _csv_cache["mtime"] != mtime:
            try:
                _csv_cache["months"] = parse_meal_csv(CSV_PATH)
            except (OSError, csv.Error) as exc:
                app.logger.warning("급식 CSV 읽기 실패: %s", exc)
                _csv_cache["months"] = {}
            _csv_cache["mtime"] = mtime
        return _csv_cache["months"].get(f"{year:04d}-{month:02d}", [])


# 한 달 식단 가져오기: 나이스가 되면 그 결과('api'), 안 되면 meals.csv('csv')
def month_meals(year, month):
    """(기록 리스트, 'api' 또는 'csv')"""
    records = fetch_neis_month(year, month)
    if records:
        return records, "api"
    return csv_month(year, month), "csv"


# =========================================================
# /api/meals : 식단 + 공지 + 평점 병합
# =========================================================
# 날짜별 평균 별점과 리뷰 수를 한 번의 조회로 구한다
def review_stats():
    stats = {}
    for row in db_all("SELECT date, AVG(rating) AS avg, COUNT(*) AS cnt FROM reviews GROUP BY date"):
        key = normalize_date(row["date"])
        if key:
            avg = round(float(row["avg"]), 1) if row["avg"] is not None else None
            stats[key] = (avg, int(row["cnt"]))
    return stats


def build_meals(ym, only_date):
    """
    - menu       : 원본 메뉴 (알레르기 괄호 그대로)
    - notice     : 공지가 있는 날짜만 {removed_menus, new_menu, reason}, 없으면 null
    - final_menu : 공지를 반영한 최종 메뉴
    - source     : 'api'(나이스 실시간) 또는 'csv'(저장된 식단)
    """
    records, source = month_meals(*ym)
    by_date = {r["date"]: r for r in records if in_period(r["date"], ym, only_date)}
    notices = {d: n for d, n in notices_by_date().items() if in_period(d, ym, only_date)}
    stats = review_stats()

    result = []
    for key in sorted(set(by_date) | set(notices)):
        record = by_date.get(key) or {"menu": [], "kcal": "", "meal": LUNCH}
        notice = notices.get(key)
        menu = list(record["menu"])
        final_menu = apply_notice(menu, notice) if notice else list(menu)
        if not menu and not final_menu:
            continue
        avg, cnt = stats.get(key, (None, 0))
        result.append({
            "date": key,
            "menu": menu,
            "kcal": record["kcal"],
            "meal": record["meal"],
            "notice": {
                "removed_menus": notice["removed_menus"],
                "new_menu": notice["new_menu"],
                "reason": notice["reason"],
            } if notice else None,
            "final_menu": final_menu,
            "changed": notice is not None,
            "avg_rating": avg,
            "review_count": cnt,
            "source": source,
        })
    return result, source


# 달력이 부르는 주소: 한 달(또는 하루)의 식단을 JSON 배열로 보낸다
@app.route("/api/meals", methods=["GET"])
def api_meals():
    period, error = period_from_args(request.args)
    if error:
        return fail(error)
    meals, source = build_meals(*period)
    response = jsonify(meals)
    response.headers["X-Meal-Source"] = source  # 급식이 하루도 없는 달에도 출처를 알 수 있게
    return response


# =========================================================
# 관리자: 데이터 내보내기 (users.csv / reviews.csv / notices.csv 를 zip 하나로)
# =========================================================
def _csv_safe(value):
    """엑셀에서 수식으로 실행되지 않도록 = + - @ 로 시작하는 글자 앞에 ' 를 붙인다."""
    text = "" if value is None else str(value)
    return "'" + text if text[:1] in ("=", "+", "-", "@") else text


# dict 목록을 CSV 글자로 바꾼다 (columns 순서대로)
def _to_csv(columns, rows):
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(columns)
    for row in rows:
        writer.writerow([_csv_safe(row.get(col)) for col in columns])
    return "﻿" + buf.getvalue()  # BOM: 엑셀에서 한글이 깨지지 않게


# 데이터 내보내기 (관리자만): 세 테이블을 각각 CSV 로 만들어 zip 하나에 담아 내려준다
@app.route("/api/export", methods=["GET"])
@admin_required
def export_data():
    tables = {
        "users.csv": (["id", "username", "role"],                      # 비밀번호는 내보내지 않음
                      db_all("SELECT id, username, role FROM users ORDER BY id")),
        "reviews.csv": (["id", "date", "username", "rating", "comment"],
                        db_all("SELECT id, date, username, rating, comment FROM reviews ORDER BY id")),
        "notices.csv": (["id", "date", "removed_menus", "new_menu", "reason"],
                        [{**n, "removed_menus": ", ".join(n["removed_menus"])}
                         for n in (notice_payload(r) for r in db_all(
                             "SELECT id, date, original_menu, new_menu, reason FROM notices ORDER BY id"))]),
    }
    archive = io.BytesIO()
    with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as zf:
        for name, (columns, rows) in tables.items():
            zf.writestr(name, _to_csv(columns, rows).encode("utf-8"))
    filename = f"school_meal_export_{today_kst():%Y%m%d}.zip"
    return Response(archive.getvalue(), mimetype="application/zip", headers={
        "Content-Disposition": f'attachment; filename="{filename}"',
        "Cache-Control": "no-store",
    })


# =========================================================
# 에러 처리
# =========================================================
# 404 같은 HTTP 오류: /api/ 주소면 JSON 으로, 그 밖에는 Flask 기본 오류 화면으로 답한다
@app.errorhandler(HTTPException)
def handle_http_error(exc):
    if request.path.startswith("/api/"):
        return jsonify({"success": False, "message": exc.description}), exc.code
    return exc


# 예상하지 못한 오류: 자세한 내용은 서버 로그에만 남기고, 사용자에게는 짧은 안내만 보낸다
@app.errorhandler(Exception)
def handle_unexpected_error(exc):
    if isinstance(exc, HTTPException):
        return handle_http_error(exc)
    app.logger.exception("Unhandled error: %s", type(exc).__name__)
    if request.path.startswith("/api/"):
        return jsonify({"success": False, "message": "서버 오류가 발생했습니다."}), 500
    return "서버 오류가 발생했습니다.", 500


# gunicorn 이 app.py 를 불러올 때도 실행되도록 맨 바깥에서 DB 를 준비한다
init_db()

# 'python app.py' 로 직접 실행할 때만 개발용 서버를 켠다 (Render 에서는 gunicorn app:app 이 대신 실행한다)
if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host='0.0.0.0', port=port)
