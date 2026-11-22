"""N13 하교 버스 — 지금 어떻게 움직일까? (Streamlit)

실행(로컬): 프로젝트 폴더에서  python -m streamlit run web/app.py
비밀 값(화면·로그에 출력하지 않음): Secrets → 환경변수 → 프로젝트 폴더 .env 순서로 읽음
  DAEJEON_BUS_KEY   : 공공데이터포털 서비스키 (대전 버스 도착정보·TAGO 도착정보에 같이 씀)
  FEEDBACK_ENDPOINT : 피드백 저장용 Apps Script 웹 앱 주소
예측 방법 (analysis/REPORT.md)
  버스 1대 예상 인원 = 그 시간대 1분당 탑승률(부분 풀링, 9~10월 교통카드) × 같은 노선 앞차 간격(실시간, 없으면 시간표)
  탑승 가능성 = N13(또는 그 정류장)을 떠날 때 인원을 28/40/55명 기준에 넣은 단계
지하철 연계: 역 정류장(현충원역1번출구 41460, 월드컵경기장역 42250) 도착정보에서 같은 차량번호를 찾아 역 도착 시각,
  없으면 N13 도착 + 정거장 수 × 정거장당 평균 분(노선정보 RUN_TM, 추정). 승강장까지 걷기(추정) 후 열차시각표에서 첫 열차
  열차시각표·역간 소요시간은 미리 받은 파일(fetch_metro.py → web/data/metro_*.csv), 실시간 호출 없음
API 아껴 쓰기 (Budget)
  - N13은 서버가 60초마다 1번(09~21시 밖에는 3분마다). 역 정류장은 '지하철 환승'일 때만, 대체 정류장은 N13이 혼잡하거나
    '다른 방법 보기'를 열었을 때만 조회. 같은 정류장 결과는 60초 저장(실패도 저장, 09~21시 밖에는 3배)
  - API별 오늘 호출 수를 세서 80% 넘으면 저장 시간 3배, 95% 넘으면 실시간 호출 멈춤 → 시간표 + 과거 통계로 안내
예시 모드: 주소 뒤에 ?demo=16:40&day=월(&routes=102) → 시간표로 만든 가상 도착(발표·캡처용, 피드백 저장 안 함)
"""
import datetime as dt
import json
import os
import re
import threading
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

import pandas as pd
import streamlit as st
import streamlit.components.v1 as components

HERE = Path(__file__).resolve().parent
KST = dt.timezone(dt.timedelta(hours=9))
DAYS = "월화수목금토일"
SERVICE_HOURS = range(9, 22)                   # 09:00~21:59 (prediction_table 시간대 9~21)
TH = (28, 40, 55)
CONG = {1: "앉을 수 있음", 2: "서서 감", 3: "혼잡", 4: "매우 혼잡"}
BOARD = {1: "높음", 2: "다소 높음", 3: "다소 낮음", 4: "낮음"}
BIDX = {v: k for k, v in BOARD.items()}        # 탑승 가능성 → 1(높음)~4(낮음)
SHORT = {"높음": "앉아서 가요", "다소 높음": "서서 가요", "다소 낮음": "혼잡해요", "낮음": "못 탈 수 있어요"}
CAN = {"높음": "앉아서 갈 수 있어요", "다소 높음": "서서 갈 수 있어요"}
PROB = {"높음": "10% 미만", "다소 높음": "10~20%", "다소 낮음": "20~40%", "낮음": "40% 이상"}  # 화면 표시용 구간(추정)
# 화면에서만 쓰는 이름(11/22 10차: '높음·낮음'이 혼잡도로 헷갈림). 분석·문서의 4단계 이름은 그대로
DISP = {"높음": "탑승 쉬움", "다소 높음": "탑승 보통", "다소 낮음": "탑승 어려움", "낮음": "탑승 매우 어려움"}
# 탑승 가능성 칩: 신호등 초록·노랑·주황·빨강. 글자색 대비 8.6·9.5·6.9·6.5 (docs/ui_check.md)
CHIP = {1: ("#4ade80", "#052e16"), 2: ("#facc15", "#422006"), 3: ("#fb923c", "#431407"), 4: ("#b91c1c", "#ffffff")}
# 결론 카드: 같은 색 계열의 연한 테두리·배경
HERO_C = {1: ("#86efac", "#f0fdf4"), 2: ("#facc15", "#fefce8"), 3: ("#fdba74", "#fff7ed"), 4: ("#f87171", "#fef2f2")}
# 버스 번호 색(사용자 확인): 진한 파랑 102·104·107·113·48 / 진한 초록 11·117·212, 그 밖은 검정
ROUTE_COLOR = {**{r: "#1e3a8a" for r in (102, 104, 107, 113, 48)}, **{r: "#14532d" for r in (11, 117, 212)}}

N13 = "41730"
ALL_ROUTES = [11, 102, 104, 113, 117, 212]
SUBWAY_ROUTES = ALL_ROUTES   # 6개 모두 N13 다음에 지하철역 근처를 지남(analysis/subway_routes_check.csv)
MODES = ["지하철 환승", "특정 노선"]
DIRS = ["반석 방면", "판암 방면"]
DRCT = {"반석 방면": 1, "판암 방면": 0}       # 열차시각표 drctType (fetch_metro.py: 데이터로 확인)
STN_NAME = {101: "판암", 102: "신흥", 103: "대동", 104: "대전역", 105: "중앙로", 106: "중구청", 107: "서대전네거리",
            108: "오룡", 109: "용문", 110: "탄방", 111: "시청", 112: "정부청사", 113: "갈마", 114: "월평", 115: "갑천",
            116: "유성온천", 117: "구암", 118: "현충원", 119: "월드컵경기장", 120: "노은", 121: "지족", 122: "반석"}
BUFFER = 1.5                 # 걷는 시간에 더하는 여유(분)
# 대체 정류장: (이름, ARS, 걷는 분(추정), 노선, N13보다 먼저 오는 분(추정), 설명)
PLACES = [("정문", "41690", 6.8, ALL_ROUTES, 1, "N13보다 덜 찬 상태로 와요"),
          ("수통골삼거리", "41670", 11.1, [11, 102, 104], 2, "정문 전 정류장이라 덜 찬 상태로 와요"),
          ("덕명중·수통골입구", "45770", 10.7, [113, 117, 212], 2, "정문 전 정류장이라 덜 찬 상태로 와요"),
          ("덕명네거리", "41400", 11.5, [48, 107, 300, 340], None, "현충원역 방면 · 대전 48·107번, 공주 300·340번")]
# 시간표 버스의 출발지와 출발지→정류장 이동 시간(분, 추정)
ORIGIN = {11: "수통골", 102: "수통골", 104: "수통골", 113: "학하동", 117: "학하동", 212: "빼울약수터", 107: "동학사",
          300: "공주 산성동", 340: "공주 신원사"}
T_DEP = {11: 4, 102: 4, 104: 4, 113: 12, 117: 12, 212: 66}
T_DUK = {107: 27, 300: 65, 340: 90}   # 덕명네거리까지 (parse_timetable_alt.py, build_gongju_schedule.py)
REALTIME_ONLY = {48}                  # 공식 시간표 없음 → 실시간(TAGO)에 잡힐 때만
# TAGO(국토교통부) 정류소 ID: 덕명네거리 현충원역 방면 (TAGO 정류소정보 getSttnNoList로 찾음, 11/22)
TAGO = [("25", "DJB8002923"),         # 대전광역시/계룡시 → 48번
        ("34020", "GOB186011031")]    # 공주시 → 300·340번
CACHE_SEC = 45            # 화면 자동 갱신 간격
API_TTL = 60              # 같은 정류장 도착정보 저장 시간(초)
LIMIT = {"대전 도착정보": 10000, "TAGO 도착정보": 10000}  # TAGO 하루 한도 10,000건(사용자가 공공데이터포털에서 확인, 11/22)
LIVE_FAIL = "지금은 실시간 정보를 불러올 수 없어서 예정 시각으로 보여드려요"   # 화면에 '시간표'라는 말은 쓰지 않음


# ---------------- 데이터 ----------------
@st.cache_data
def load_tables():
    P = pd.read_csv(HERE / "data" / "prediction_table.csv").set_index(["노선", "요일", "시간대"])
    S = pd.read_csv(HERE / "data" / "schedule_n13_days.csv")
    tp = HERE / "data" / "tashu_near.csv"
    T = pd.read_csv(tp) if tp.exists() else pd.DataFrame()
    R = pd.read_csv(HERE / "data" / "alt_stop_ratio.csv")
    ratio = {}
    for rt, g in R.groupby("노선"):
        med = g["비율"].median()
        for _, x in g.iterrows():
            v = x["비율"] if x["비율"] == x["비율"] else med
            ratio[(int(rt), int(x["시간대"]))] = min(float(v), 1.0)   # 1 넘는 칸(시간대 경계 효과)은 1로
    return P, S, T, ratio


@st.cache_data
def load_alt():
    """덕명네거리 시간표 예정: 107번(parse_timetable_alt.py) + 공주 300·340번(build_gongju_schedule.py). 48번은 시간표 없음"""
    out = []
    for f in ("schedule_alt.csv", "schedule_gongju.csv"):
        p = HERE / "data" / f
        if p.exists():
            out.append(pd.read_csv(p)[["일정", "노선", "정류장", "예정분"]])
    return pd.concat(out) if out else pd.DataFrame(columns=["일정", "노선", "정류장", "예정분"])


@st.cache_data
def load_metro():
    """열차시각표(현충원 118·월드컵경기장 119)·역간 소요시간·역 연결표. 파일이 없으면 None → 역 도착 시각만 보여줌"""
    try:
        M = pd.read_csv(HERE / "data" / "metro_timetable.csv")
        MT = pd.read_csv(HERE / "data" / "metro_time.csv")
        tt = {(int(r.출발역), int(r.도착역)): float(r.소요분) for r in MT.itertuples()}
    except Exception:
        M, tt = None, {}
    try:
        L = pd.read_csv(HERE / "data" / "station_link.csv").set_index("노선")
    except Exception:
        L = None
    return M, tt, L


def _secret(name):
    """비밀 값: 배포 Secrets → 환경변수 → (노트북) 프로젝트 폴더 .env 순서. 화면·로그에 출력하지 않음"""
    try:
        v = st.secrets.get(name, "")
    except Exception:
        v = ""
    v = str(v or os.environ.get(name, "")).strip()
    if not v:
        env = HERE.parent / ".env"
        if env.exists():
            for line in env.read_text(encoding="utf-8-sig").splitlines():
                if line.strip().startswith(name + "="):
                    v = line.split("=", 1)[1].strip().strip('"').strip("'")
    return v


def service_key():
    k = _secret("DAEJEON_BUS_KEY")
    return urllib.parse.unquote(k) if "%" in k else k


def safe_msg(e):
    """예외를 남길 때: 종류 이름만, 혹시 키·주소가 섞이면 가림"""
    s = type(e).__name__ if isinstance(e, BaseException) else str(e)
    k = service_key()
    if k:
        s = s.replace(k, "***").replace(urllib.parse.quote(k, safe=""), "***")
    return re.sub(r"https?://\S+", "[주소 가림]", s)[:80]


def kst_now():
    return dt.datetime.now(KST)


# ---------------- API 호출 + 한도 감시 ----------------
class Budget:
    """모든 접속자가 함께 쓰는 저장소: API별 오늘 호출 수, 정류장별 마지막 결과.
    80% 넘으면 저장 시간 3배, 95% 넘으면 새 호출 없이 '한도' 오류를 돌려줌(화면은 시간표로 바뀜)"""

    def __init__(self):
        self.lock = threading.Lock()
        self.day = ""
        self.count = {k: 0 for k in LIMIT}
        self.cache = {}

    def _reset(self):
        d = kst_now().strftime("%Y-%m-%d")
        if d != self.day:
            self.day, self.count = d, {k: 0 for k in LIMIT}

    def ratio(self, api):
        with self.lock:
            self._reset()
            return self.count[api] / LIMIT[api]

    def get(self, api, key, fn, ttl=API_TTL):
        now = time.time()
        with self.lock:
            self._reset()
            r = self.count[api] / LIMIT[api]
            ttl = ttl * (3 if r >= 0.8 else 1) * (1 if kst_now().hour in SERVICE_HOURS else 3)
            hit = self.cache.get((api, key))
            if hit and now - hit[0] < ttl:
                return hit[1], hit[2]
            if r >= 0.95:
                return [], "한도"
            self.count[api] += 1
        try:
            res, err = fn(), ""
        except Exception as e:
            res, err = [], safe_msg(e)
        with self.lock:
            self.cache[(api, key)] = (time.time(), res, err)
        return res, err


@st.cache_resource
def budget():
    return Budget()


def _call_arrivals(ars):
    """대전 도착정보 1번 호출 → [{노선, 차량, 도착분, 남은정류장, MSG_TP}]. 실패하면 예외(종류 이름만)"""
    key = service_key()
    if not key:
        raise RuntimeError("서비스키 없음")
    q = urllib.parse.urlencode({"serviceKey": key, "arsId": ars})
    try:
        with urllib.request.urlopen(f"https://apis.data.go.kr/6300000/arrive/getArrInfoByUid?{q}", timeout=8) as r:
            root = ET.fromstring(r.read().decode("utf-8", "replace"))
    except Exception as e:
        raise RuntimeError(type(e).__name__) from None
    out = []
    for it in root.findall(".//itemList"):
        g = {c.tag: (c.text or "").strip() for c in it}
        try:
            out.append({"노선": int(g.get("ROUTE_NO", "0")), "차량": g.get("CAR_REG_NO", ""),
                        "도착분": max(int(g.get("EXTIME_MIN", "0") or 0), 0),
                        "남은정류장": g.get("STATUS_POS", ""), "MSG_TP": g.get("MSG_TP", "")})
        except ValueError:
            continue
    return out


def _call_tago(city, node):
    """TAGO 정류소별 도착예정정보 1번 호출 → [{노선, 도착분, 남은정류장}] (arrtime 초 → 분)"""
    key = service_key()
    if not key:
        raise RuntimeError("서비스키 없음")
    q = urllib.parse.urlencode({"serviceKey": key, "cityCode": city, "nodeId": node, "_type": "json", "numOfRows": 50})
    try:
        with urllib.request.urlopen(f"https://apis.data.go.kr/1613000/ArvlInfoInqireService/getSttnAcctoArvlPrearngeInfoList?{q}",
                                    timeout=8) as r:
            body = json.loads(r.read().decode("utf-8", "replace"))["response"]["body"]
    except Exception as e:
        raise RuntimeError(type(e).__name__) from None
    items = body.get("items") or {}
    items = items.get("item", []) if isinstance(items, dict) else []
    items = items if isinstance(items, list) else [items]
    out = []
    for x in items:
        try:
            out.append({"노선": int(str(x.get("routeno", "")).strip()), "차량": "", "도착분": int(x.get("arrtime", 0)) // 60,
                        "남은정류장": str(x.get("arrprevstationcnt", "")), "MSG_TP": ""})
        except ValueError:
            continue
    return out


def arrivals(ars):
    return budget().get("대전 도착정보", ars, lambda: _call_arrivals(ars))


def tago_arrivals():
    """덕명네거리: TAGO 대전(48번)·공주(300·340번). 대전 정류장과 같이 60초 저장(한도 10,000 확인 후 120→60초, 11/22)"""
    rows, errs = [], []
    for city, node in TAGO:
        r, e = budget().get("TAGO 도착정보", node, lambda c=city, n=node: _call_tago(c, n), ttl=API_TTL)
        rows += r
        errs += [e] if e else []
    return rows, ("; ".join(errs) if len(errs) == len(TAGO) else "")


# ---------------- 예측 ----------------
def stage(v):
    return 1 if v <= TH[0] else 2 if v <= TH[1] else 3 if v <= TH[2] else 4


def day_info(now, override=None):
    """(예측표 요일, 시간표 종류, 주말 여부)"""
    d = override or DAYS[now.weekday()]
    if d in "월화수목금":
        return d, "평일", False
    return "금", ("토요일" if d == "토" else "휴일"), True


def sched_headway(S, route, t_arr):
    s = S[S["노선"] == route]
    if s.empty:
        return None
    m = t_arr.hour * 60 + t_arr.minute
    k = (s["N13예정분"] - m).abs().idxmin()
    v = s.loc[k, "같은노선_앞차간격"]
    return float(v) if v == v and v > 0 else None


def crowd_window(P, route, day, t_arr):
    """몰림 주의(규칙): N13 쪽 건물 끝나는 수업 30개 이상 시간대, hh:35~(hh+1):05"""
    for h, ok in [(t_arr.hour, t_arr.minute >= 35), (t_arr.hour - 1, t_arr.minute < 5)]:
        if ok and (route, day, h) in P.index and P.loc[(route, day, h), "몰림주의"] == "Y":
            return P.loc[(route, day, h), "몰림주의_시각"]
    return ""


def predict_bus(P, S, route, eta, now, day, last_pass=None, hw=None):
    t_arr = now + dt.timedelta(minutes=eta)
    res = {"노선": route, "도착분": eta, "도착시각": t_arr.strftime("%H:%M"), "도착dt": t_arr, "예측": False}
    key = (route, day, t_arr.hour)
    if t_arr.hour not in SERVICE_HOURS or key not in P.index:
        return res
    r = P.loc[key]
    sh = sched_headway(S, route, t_arr) or float(r["시간표_평균간격_분"])
    if hw is not None and hw > 0:          # 다음 버스: 이번 버스와의 간격
        src = "이번 버스와 간격"
    else:
        hw, src = sh, "시간표"
        if last_pass is not None:
            live = (t_arr - last_pass).total_seconds() / 60
            if 0 < live <= 3 * sh:
                hw, src = live, "실시간"
    res.update({"예측": True, "앞차간격": hw, "간격출처": src, "몰림주의": crowd_window(P, route, day, t_arr)})
    for k in ["보통", "붐빔"]:
        arr = r[f"{k}_버스탑승률_분"] * hw
        dep = max(arr + r[f"{k}_N13수요율_분"] * hw - r["N13하차_1대당"], 0)
        res[f"{k}_도착"], res[f"{k}_혼잡"], res[f"{k}_탑승"] = arr, stage(arr), BOARD[stage(dep)]
    return res


def sched_etas(S, route, now, offset, horizon=90):
    """시간표: 이 정류장에 오기까지 남은 분 목록 (N13 예정 − offset)"""
    m = now.hour * 60 + now.minute
    v = S.loc[S["노선"] == route, "N13예정분"] - offset - m
    return sorted(int(x) for x in v if 0 <= x <= horizon)


def merge_etas(live, sched, S, route, now):
    """실시간 + 시간표. 실시간 버스가 있으면 그 버스(+여유) 이후 시간표만 → 같은 버스 두 번 안 셈"""
    out = [(e, "실시간") for e in sorted(live)]
    if live:
        hw = sched_headway(S, route, now + dt.timedelta(minutes=max(live))) or 10
        sched = [e for e in sched if e > max(live) + max(3, hw / 2)]
    return out + [(e, "시간표") for e in sched]


# ---------------- 백그라운드: N13 조회 + 버스별 웹 예측 기억 ----------------
class Tracker:
    """N13 도착정보를 60초마다(09~21시 밖 3분마다) 조회 — Budget을 거쳐서 호출 수에 포함
    - 앞차 통과 시각(남은 정류장 1로 보이던 차가 다음 조회에서 사라지면 통과, 기점 대기 MSG_TP 07 제외)
    - 버스(노선·차량)마다 웹 예측과 예측 도착·실제 통과 시각 → 피드백 짝짓기 (차량번호는 메모리에만, 3시간 뒤 지움)"""

    def __init__(self, P, S_all):
        self.P, self.S_all = P, S_all
        self.lock = threading.Lock()
        self.snapshot, self.snap_time, self.err, self.last_pass, self.prev, self.store = None, 0.0, "", {}, {}, {}
        threading.Thread(target=self.loop, daemon=True).start()

    def step(self):
        rows, err = budget().get("대전 도착정보", N13, lambda: _call_arrivals(N13), ttl=50)
        if err:
            with self.lock:
                self.err = err
            return
        now = kst_now().replace(second=0, microsecond=0)
        day, kind, _ = day_info(now)
        S = self.S_all[self.S_all["일정"] == kind]
        cur = {(r["노선"], r["차량"]): r for r in rows if r["MSG_TP"] != "07"}
        with self.lock:
            for key, r in self.prev.items():
                if key not in cur:
                    if r["남은정류장"] == "1":
                        self.last_pass[key[0]] = now
                    e = self.store.get(key)
                    if e and e["통과"] is None and r["도착분"] <= 2:
                        e["통과"] = now
            for key, r in cur.items():
                if r["노선"] not in ALL_ROUTES:
                    continue
                b = predict_bus(self.P, S, r["노선"], r["도착분"], now, day, self.last_pass.get(r["노선"]))
                if b["예측"]:
                    self.store[key] = {"노선": r["노선"], "예측도착": b["도착dt"], "통과": None,
                                       "혼잡도": CONG[b["보통_혼잡"]], "탑승가능성": b["보통_탑승"]}
            old = now - dt.timedelta(hours=3)
            self.store = {k: v for k, v in self.store.items() if v["예측도착"] > old}
            self.prev, self.snapshot, self.snap_time, self.err = cur, rows, time.time(), ""

    def loop(self):
        while True:
            try:
                self.step()
            except Exception:
                pass  # 로그에 아무것도 남기지 않음(키가 섞일 일 없음)
            time.sleep(60 if kst_now().hour in SERVICE_HOURS else 180)

    def entries(self):
        with self.lock:
            return [dict(v) for v in self.store.values()]


@st.cache_resource
def tracker():
    P, S, _, _ = load_tables()
    return Tracker(P, S)


# ---------------- 피드백 ----------------
def feedback_endpoint():
    return _secret("FEEDBACK_ENDPOINT")


def send_feedback(payload):
    """서버에서 Apps Script 웹 앱으로 보냄(주소는 브라우저에 전달되지 않음). 성공하면 True"""
    url = feedback_endpoint()
    if not url.startswith("https://script.google.com/"):
        return False
    try:
        req = urllib.request.Request(url, data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
                                     headers={"Content-Type": "application/json"}, method="POST")
        with urllib.request.urlopen(req, timeout=10) as r:
            res = json.loads(r.read().decode("utf-8", "replace"))
        return bool(res.get("ok"))
    except Exception:
        return False


def match_bus(route, now, demo, P, S, day):
    """누른 시각과 가장 가까운, 이미 도착한 그 노선 버스(40분 전 ~ 지금, 예측 오차 2분 허용) + 그 버스에 대한 웹 예측"""
    if demo:
        m = now.hour * 60 + now.minute
        s = S[(S["노선"] == route) & (S["N13예정분"] >= m - 40) & (S["N13예정분"] <= m + 2)]
        if s.empty:
            return None
        v = int(s.loc[(s["N13예정분"] - m).abs().idxmin(), "N13예정분"])
        b = predict_bus(P, S, route, v - m, now, day)
        if not b["예측"]:
            return None
        return {"도착시각": b["도착시각"], "도착시각구분": "예측", "혼잡도": CONG[b["보통_혼잡"]], "탑승가능성": b["보통_탑승"]}
    best = None
    for e in tracker().entries():
        if e["노선"] != route:
            continue
        ref = e["통과"] or e["예측도착"]
        diff = (now - ref).total_seconds() / 60
        if -2 <= diff <= 40 and (best is None or abs(diff) < best[0]):
            best = (abs(diff), e, ref)
    if not best:
        return None
    _, e, ref = best
    return {"도착시각": ref.strftime("%H:%M"), "도착시각구분": "실측" if e["통과"] else "예측",
            "혼잡도": e["혼잡도"], "탑승가능성": e["탑승가능성"]}


def recent_route(default):
    """방금 N13을 지나간 노선(30분 안, 가장 최근)"""
    try:
        now = kst_now()
        passed = [e for e in tracker().entries() if e["통과"] and (now - e["통과"]).total_seconds() < 1800]
        if passed:
            return max(passed, key=lambda e: e["통과"])["노선"]
    except Exception:
        pass
    return default


def on_answer(bid, bus, route):
    ss = st.session_state
    a1, a2 = ss.get(f"fbq_{bid}_혼잡"), ss.get(f"fbq_{bid}_탑승")
    done = ss.setdefault("fb_done", {})
    if bid in done or a1 not in ("예", "아니요") or a2 not in ("예", "아니요"):
        return
    p = {"노선": int(route), "정류장": "N13", "도착시각": bus["도착시각"], "도착시각구분": bus["도착시각구분"],
         "혼잡도": bus["혼잡도"], "탑승가능성": bus["탑승가능성"], "혼잡했나요": a1, "탈수있었나요": a2}
    if ss.get("demo_mode") or send_feedback(p):
        done[bid] = (a1, a2)
    else:
        ss["fb_broken"] = True


# ---------------- 화면 조각 ----------------
# 글자 3단계: 큰(번호·도착·결론 1.15rem 굵게) / 보통(칩·장소 .95rem) / 작은 회색(.82rem #4b5563)
# 색은 탑승 가능성 칩·버스 번호·몰림 주의 제목에만. 카드는 연한 테두리 상자(모서리 10px), 결론 카드만 연한 색
CSS = """
<style>
.block-container{padding-top:3rem;padding-bottom:2rem;max-width:560px}
[data-testid="stHeaderActionElements"],.stMarkdown h1 a,.stMarkdown h2 a,.stMarkdown h3 a{display:none!important}
.n13-title{text-align:center;font-size:1.4rem;font-weight:700;color:#111827;margin:0;line-height:1.3}
.n13-sub{text-align:center;font-size:.82rem;color:#4b5563;margin:2px 0 12px}
.n13-card{border:1px solid #e3e6ea;border-radius:10px;padding:12px 16px;margin:8px 0;background:#fff;color:#111827}
.n13-hero{border:2px solid #d1d5db;background:#f9fafb;border-radius:10px;padding:14px 16px;margin:6px 0 4px;color:#111827}
.n13-hero .h1{font-size:1.15rem;font-weight:700;line-height:1.45}
.n13-hero .wk{font-size:.95rem;font-weight:600;white-space:nowrap}
.n13-hero .h2{font-size:.95rem;margin-top:4px;line-height:1.6}
.n13-hero .n13-mu{margin-top:4px}
.n13-main{font-size:1.15rem;font-weight:700;line-height:1.45}
.n13-pl2{font-size:.95rem;font-weight:600;line-height:1.6;margin-top:4px}
.n13-no{font-weight:800;margin-right:8px}
.n13-place{font-size:.95rem;font-weight:600;color:#111827}
.n13-mu{font-size:.82rem;color:#4b5563;line-height:1.6}
.n13-sec{font-size:.95rem;font-weight:700;color:#111827;margin:26px 0 2px}
.n13-stamp{font-size:.82rem;color:#4b5563;margin:2px 0 6px}
.n13-note{font-size:.82rem;color:#374151;background:#f4f5f7;border-radius:10px;padding:8px 12px;margin:8px 0 0}
.n13-crowd{color:#b91c1c;font-weight:700}
.n13-chip{display:inline-block;border-radius:6px;padding:1px 8px;font-weight:700;font-size:.85rem;white-space:nowrap;line-height:1.5}
.n13-chip.sm{font-size:.75rem;padding:0 6px}
.n13-ph{font-weight:600;font-size:.95rem;white-space:nowrap;margin-left:6px}
.nw{white-space:nowrap}
.n13-sub2{margin-top:4px}
div[data-testid="stButtonGroup"] button{min-height:44px;min-width:64px}
.st-key-mode div[data-testid="stButtonGroup"] > div,.st-key-dir div[data-testid="stButtonGroup"] > div{width:100%;display:flex}
.st-key-mode div[data-testid="stButtonGroup"] button,.st-key-dir div[data-testid="stButtonGroup"] button{flex:1 1 0;font-size:.95rem}
div[data-testid="stButtonGroup"] button[kind="segmented_controlActive"],
div[data-testid="stButtonGroup"] button[data-testid="stBaseButton-segmented_controlActive"]{background:#eaf2fd!important;border-color:#7aa7e0!important;color:#1e4f9a!important}
div[data-testid="stButtonGroup"] button[kind="segmented_controlActive"] p{color:#1e4f9a!important}
[data-testid="stExpander"] details{border:1px solid #e3e6ea;border-radius:10px}
[data-testid="stExpander"] summary{min-height:44px;box-sizing:border-box;display:flex;align-items:center}
[data-testid="stExpander"] summary p{font-size:.95rem;color:#111827}
</style>
"""


def html(s):
    # 물결표(~)가 두 개 있으면 마크다운이 취소선으로 바꿔서, HTML 문자로 바꿔 넣음
    st.markdown(s.replace("~", "&#126;"), unsafe_allow_html=True)


def card(inner):
    return f"<div class='n13-card'>{inner}</div>"


def rcolor(rt):
    return ROUTE_COLOR.get(rt, "#111827")


def num(rt):
    return f"<span class='n13-no' style='color:{rcolor(rt)}'>{rt}</span>"


def chip(level, small=False):
    """탑승 가능성 칩: 신호등 색을 꽉 채우고 화면용 이름(탑승 쉬움 등)을 함께 씀(색만으로 구분하지 않음)"""
    bg, fg = CHIP[BIDX[level]]
    return f"<span class='n13-chip{' sm' if small else ''}' style='background:{bg};color:{fg}'>{DISP[level]}</span>"


def board(level):
    return f"<span class='nw'>{chip(level)}<span class='n13-ph'>{SHORT[level]}</span></span>"


LEGEND = ("탑승 쉬움 못 탈 확률 10% 미만 · 보통 10~20% · <span class='nw'>어려움 20~40%</span> · "
          "<span class='nw'>매우 어려움 40% 이상 (추정)</span>")


def when(m):
    return "곧 도착" if m <= 1 else f"{m}분 뒤 도착"


def travel_min(rt, offset):
    """출발지 → 그 정류장 이동 시간(분, 추정). offset = N13보다 먼저 오는 분, None이면 덕명네거리"""
    if offset is None:
        return T_DUK.get(rt)
    return T_DEP[rt] - offset if rt in T_DEP else None


def eta_text(rt, e, kind, now, travel, tail="", short=False):
    """실시간 'N분 뒤 도착' / 예정 버스 '약 N분 뒤 도착' / 예정 출발 시각이 지났는데 실시간에 없으면 '약 N분 뒤 도착 (추정)'
    화면에는 '시간표'라는 말을 쓰지 않음(11/22 10차). short=True면 '도착'을 뺌(다음 버스 줄)"""
    end = "" if short else " 도착"
    if kind == "실시간" or travel is None:
        s = ("곧" if e <= 1 else f"{e}분 뒤") + end if kind == "실시간" else f"약 {max(e, 1)}분 뒤{end}"
        return f"<span class='nw'>{s}{tail}</span>"
    dep = now + dt.timedelta(minutes=e - travel)
    if dep <= now:
        return f"<span class='nw'>약 {max(e, 1)}분 뒤{end} (추정){tail}</span>"
    return f"<span class='nw'>약 {e}분 뒤{end}{tail}</span>"


def next_line(rt, e, kind, lv, now, tr):
    c2 = f" {chip(lv, True)}" if lv else ""
    return f"<div class='n13-mu n13-sub2'>다음 {eta_text(rt, e, kind, now, tr, c2, short=True)}</div>"


def link_short(L):
    """버스 카드용 열차 한 줄: '현충원역 11:42 반석행' / 여유 2분 이하면 '· 아슬아슬'"""
    if L["열차"] is None:
        return f"<span class='nw'>{L['역']} 약 {hm(L['도착'])} 도착</span>" + \
               (" <span class='nw'>· 오늘 남은 열차 없음</span>" if L["없음"] else "")
    return f"<span class='nw'>{L['역']} {hm(L['열차'])} {L['종착']}행{' · 아슬아슬' if L['아슬'] else ''}</span>"


def link_long(L):
    """결론 카드용: '현충원역 11:38 도착 → 11:42 반석행 (승강장까지 약 2분)', 추정이면 '약 11:38'"""
    s = f"<span class='nw'>{L['역']} {'약 ' if L['추정'] else ''}{hm(L['도착'])} 도착</span>"
    if L["열차"] is None:
        return s + (" <span class='nw'>· 오늘 남은 열차 없음</span>" if L["없음"] else "")
    s += f" <span class='nw'>→ {hm(L['열차'])} {L['종착']}행</span> <span class='nw'>(승강장까지 약 {L['걷기']}분)</span>"
    if L["아슬"]:
        s += " <span class='nw'>· 아슬아슬해요" + (f", 놓치면 다음 {hm(L['다음'])}" if L["다음"] else "") + "</span>"
    return s


def route_card(rt, cur, nxt, now, status="", link=None):
    """N13 노선 카드(3~4줄): 번호+도착 / 칩+짧은 말 / (지하철) 열차 / 다음 버스"""
    tr = travel_min(rt, 0)
    if cur is None:
        html(card(f"<span class='n13-main'>{num(rt)}</span><span class='n13-mu'>{status}</span>"))
        return
    body = f"<div class='n13-main'>{num(rt)}{eta_text(rt, cur['도착분'], cur['종류'], now, tr)}</div>"
    if cur["예측"]:
        body += f"<div class='n13-sub2'>{board(cur['보통_탑승'])}</div>"
    else:
        body += "<div class='n13-mu'>지원 시간(09~21시) 밖이라 예측하지 않아요</div>"
    if link:
        body += f"<div class='n13-mu n13-sub2'>{link_short(link)}</div>"
    if nxt is not None:
        body += next_line(rt, nxt["도착분"], nxt["종류"], nxt["보통_탑승"] if nxt["예측"] else None, now, tr)
    html(card(body))


def demo_arrivals(S, now, routes, offset=0):
    """예시 모드: 시간표로 만든 가상 도착 (노선마다 가장 가까운 1대, 실제 API처럼)"""
    out = []
    for rt in routes:
        e = sched_etas(S, rt, now, offset, 60)
        if e:
            out.append({"노선": rt, "차량": f"예시{rt}-{e[0]}", "도착분": e[0], "남은정류장": "", "MSG_TP": ""})
    return out


def tashu_info(T):
    if T.empty or "N13" not in set(T["쪽"]):
        return None
    a = T[T["쪽"] == "N13"].sort_values("걷는거리_m").iloc[0]
    return {"이름": a["대여소명"].split(" ", 1)[-1], "걷기": round(a["걷는시간_분"]), "자전거": round(a["자전거_대여소간_분"])}


def crowd_note(P, day, now):
    """몰림 주의(규칙: N13 쪽 건물 끝나는 수업 30개 이상 시간대 hh:35~(hh+1):05)를 지금 시각에 맞춰
    30분 전부터 'N분 뒤 몰림 예상', 그 안에는 '지금 몰림 시간대', 지나면 숨김"""
    for h in SERVICE_HOURS:
        rows = [P.loc[(rt, day, h)] for rt in ALL_ROUTES if (rt, day, h) in P.index]
        hit = [r for r in rows if r["몰림주의"] == "Y"]
        if not hit:
            continue
        s = now.replace(hour=h, minute=35)
        e = s + dt.timedelta(minutes=30)
        left = (s - now).total_seconds() / 60
        label = hit[0]["몰림주의_시각"]
        if 0 < left <= 30:
            return f"{label} · {int(left)}분 뒤 몰림 예상"
        if s <= now < e:
            return f"{label} · 지금 몰림 시간대"
    return ""


# ---------------- 지하철 연계 ----------------
def station_info(rt, cur, now, demo):
    """N13에 오는 버스(cur)가 역 정류장에 도착하는 분과 추정 여부.
    실시간: 역 정류장 도착정보에서 같은 차량번호. 없으면 N13 도착 + 정거장 수 × 정거장당 평균 분(추정)"""
    _, _, L = load_metro()
    if L is None or rt not in L.index:
        return None
    r = L.loc[rt]
    est = cur["도착분"] + round(float(r["추정분"]))
    car = cur.get("차량", "")
    if car and not demo:
        rows, _ = arrivals(str(int(r["정류장ARS"])))
        hit = [x["도착분"] for x in rows if x["차량"] == car and x["노선"] == rt]
        if hit and hit[0] >= cur["도착분"]:
            return {"역": r["역"], "역번호": int(r["역번호"]), "분": hit[0], "추정": False, "걷기": int(r["걷기분"])}
    return {"역": r["역"], "역번호": int(r["역번호"]), "분": est, "추정": True, "걷기": int(r["걷기분"])}


def train_after(stn, minute, drct, daytype):
    """stn 역에서 minute(0시 기준 분) 이후 출발하는 열차 목록 [(출발분, 종착)] 앞의 2개"""
    M, _, _ = load_metro()
    if M is None:
        return []
    t = M[(M["역번호"] == stn) & (M["요일구분"] == daytype) & (M["방향"] == drct) & (M["출발분"] >= minute)]
    out = []
    for r in t.sort_values("출발분").head(2).itertuples():
        end = r.종착 if isinstance(r.종착, str) and r.종착 else ("반석" if drct == 1 else "판암")
        out.append((int(r.출발분), end))
    return out


def hm(m):
    m = int(m) % 1440
    return f"{m // 60:02d}:{m % 60:02d}"


def metro_link(rt, cur, now, demo, direction, weekend):
    """버스 → 역 → 승강장 → 열차. 기다림·아슬아슬은 승강장 도착(역 도착 + 걷기) 기준.
    비교 키 = 그 열차가 두 역 중 뒤쪽 역(반석 방면 119, 판암 방면 118)을 지나는 시각 → 같은 열차면 같은 값"""
    si = station_info(rt, cur, now, demo)
    if si is None:
        return None
    arr = now.hour * 60 + now.minute + si["분"]
    d = {"역": si["역"], "도착": arr, "추정": si["추정"], "걷기": si["걷기"], "열차": None, "종착": "",
         "다음": None, "아슬": False, "없음": False, "키": None}
    M, tt, _ = load_metro()
    if M is None:
        return d
    drct = DRCT[direction]
    plat = arr + si["걷기"]
    trains = train_after(si["역번호"], plat, drct, 1 if weekend else 0)
    if not trains:
        d["없음"] = True
        return d
    dep, end = trains[0]
    later = 119 if drct == 1 else 118
    d.update({"열차": dep, "종착": end, "다음": trains[1][0] if len(trains) > 1 else None, "아슬": dep - plat <= 2,
              "키": dep + (tt.get((si["역번호"], later), 0) if si["역번호"] != later else 0)})
    return d


# ---------------- 대체경로 ----------------
def _alt_board(P, S, rt, e, offset, now, day, last_pass, ratio, name, kind, hw=None):
    """대체 정류장 버스의 탑승 가능성(그 정류장을 떠날 때 인원)"""
    b = predict_bus(P, S, rt, e + offset, now, day, last_pass.get(rt) if kind == "실시간" else None, hw=hw)
    if not b["예측"]:
        return None, None
    f = 1.0 if name == "정문" else ratio.get((rt, b["도착dt"].hour), 1.0)
    return BOARD[stage(b["보통_도착"] * f)], BOARD[stage(b["붐빔_도착"] * f)]


def place_options(routes, demo, S, A, now, day, P, ratio, last_pass, in_service, subway):
    """대체 장소마다: 걸어서(+여유) 도착한 뒤 탈 수 있는 첫 버스(실시간, 없으면 예정)와 탑승 가능성.
    특정 노선이면 그 노선이 지나는 장소만(덕명네거리는 지하철 환승일 때만). 탈 버스가 없으면 이유를 붙임.
    이 함수가 불릴 때만 대체 정류장 API를 부름"""
    m = now.hour * 60 + now.minute
    opts, failed = [], False
    for name, ars, walk, prts, offset, _note in PLACES:
        base = {"장소": name, "걷기": walk, "버스": None, "오프셋": offset}
        if offset is None:
            if not subway:
                continue
            rts = prts
        else:
            rts = [r for r in prts if r in routes]
            if not rts:
                continue
        if demo:
            rows, err = (demo_arrivals(S, now, rts, offset), "") if offset is not None else ([], "")
        else:
            rows, err = arrivals(ars)
            if offset is None:          # 덕명네거리: TAGO(48·300·340번) 결과를 더함
                t_rows, t_err = tago_arrivals()
                rows = rows + [r for r in t_rows if r["노선"] not in {x["노선"] for x in rows}]
                err = err and t_err
        failed |= bool(err)
        best, no_info, later = None, [], []
        for rt in rts:
            live = [r["도착분"] for r in rows if r["노선"] == rt and r["MSG_TP"] != "07"]
            if offset is not None:
                sched = sched_etas(S, rt, now, offset, horizon=24 * 60)
            else:   # 덕명네거리: 107·300·340번 예정, 48번은 실시간만
                sched = sorted(int(v - m) for v in A.loc[A["노선"] == rt, "예정분"] if v - m >= 0)
            cands = merge_etas(live, sched, S, rt, now) if (live or sched) else []
            ok = [(e, k) for e, k in cands if e > walk + BUFFER]
            if not ok:
                no_info.append(rt)
                continue
            e, kind = ok[0]
            tr = travel_min(rt, offset)
            if e > 90:
                later.append((e, f"{rt}번 " + eta_text(rt, e, kind, now, tr)))
                continue
            lv = lvb = None
            if offset is not None and in_service:
                lv, lvb = _alt_board(P, S, rt, e, offset, now, day, last_pass, ratio, name, kind)
            cand = {**base, "버스": rt, "탈분": e, "종류": kind, "탑승": lv, "붐빔탑승": lvb, "이동": tr}
            if best is None or rank_key(cand) < rank_key(best):
                best = cand
        if best:
            opts.append(best)
            continue
        miss_rt = [r for r in no_info if r in REALTIME_ONLY]
        miss_sc = [r for r in no_info if r not in REALTIME_ONLY]
        why = ([f"{'·'.join(map(str, miss_rt))}번은 지금 실시간에 안 잡혀요"] if miss_rt else []) + \
              ([f"{'·'.join(map(str, miss_sc))}번은 오늘 남은 버스 없음"] if miss_sc else [])
        if later:
            later.sort()
            opts.append({**base, "상태": "90분 안에 탈 수 있는 버스 없음 · 다음 " + later[0][1]})
        else:
            opts.append({**base, "상태": " · ".join(why) or "오늘 남은 버스 없음"})
    return opts, failed


TAXI = {"장소": "택시", "걷기": 0, "버스": None, "상태": ""}


def option_card(o, now):
    """'어디서 탈까요?' 장소 카드(2줄): '수통골삼거리 · 걸어서 약 11분' / '102  19분 뒤 도착 [탑승 쉬움]'"""
    if o["장소"] == "택시":
        html(card("<span class='n13-place'>택시 · 최후의 수단</span>"
                  "<div class='n13-mu'>버스가 모두 20분 이상 걸릴 때</div>"))
        return
    if o["장소"] == "N13":
        head = "<span class='n13-place'>N13</span> <span class='n13-mu'>· 지금 있는 곳</span>"
    else:
        head = f"<span class='n13-place'>{o['장소']}</span> <span class='n13-mu'>· 걸어서 약 {round(o['걷기'])}분</span>"
    if o.get("버스") is None:
        body = f"<div class='n13-mu n13-sub2'>{o['상태']}</div>"
    else:
        rt = o["버스"]
        c = f" {chip(o['탑승'], True)}" if o.get("탑승") else ""
        body = f"<div class='n13-pl2'>{num(rt)}{eta_text(rt, o['탈분'], o['종류'], now, o.get('이동'), c)}</div>"
    html(card(head + body))


def get_now(demo, qp):
    now = kst_now().replace(second=0, microsecond=0)
    if demo:
        try:
            hh, mm = map(int, qp.get("demo", "16:40").split(":"))
            now = now.replace(hour=hh, minute=mm)
        except ValueError:
            pass
    return now


def rank_key(o):
    """탈 만한 방법(쉬움·보통, 또는 예측 없음)이 먼저 → 타는 시각이 빠른 순 → 탑승 가능성이 높은 순"""
    b = BIDX.get(o.get("탑승"), 2.5)
    return (b > 2.5, o["탈분"], b)


def all_alternatives(routes, demo, S, A, now, day, P, ratio, last_pass, in_service, T, subway, first):
    """N13(지금 있는 곳) + 대체 장소 + (지하철 환승이면) 타슈. 택시는 따로"""
    places, failed = place_options(routes, demo, S, A, now, day, P, ratio, last_pass, in_service, subway)
    if first is not None:
        places.insert(0, {"장소": "N13", "걷기": 0, "버스": first["노선"], "탈분": first["도착분"], "종류": first["종류"],
                          "탑승": first["보통_탑승"] if first["예측"] else None, "이동": travel_min(first["노선"], 0),
                          "오프셋": 0})
    ranked = sorted([o for o in places if o.get("버스") is not None], key=rank_key)
    rest = [o for o in places if o.get("버스") is None]
    if subway:   # 타슈는 현충원역까지 가는 방법이라 지하철 환승일 때만
        t = tashu_info(T)
        rest.append({"장소": "타슈", "걷기": t["걷기"] if t else 0, "버스": None,
                     "상태": f"{t['이름']} 대여소 → 현충원역 자전거 약 {t['자전거']}분 (추정)" if t else "근처 대여소 정보 없음"})
    slow = not any(o["탈분"] < 20 for o in ranked)
    return ranked, rest, slow, failed


def hero_card(lv, h1, lines):
    """결론 카드: 그 버스 탑승 가능성 색의 연한 테두리·배경. lines = 아래 줄들(이미 HTML)"""
    style = ""
    if lv in BIDX:
        bd, bg = HERO_C[BIDX[lv]]
        style = f" style='border-color:{bd};background:{bg}'"
    html(f"<div class='n13-hero'{style}><div class='h1'>{h1}</div>{''.join(lines)}</div>")


def hero_detail(rt, e, kind, now, tr, lv, lvb, link):
    out = [f"<div class='h2'>{eta_text(rt, e, kind, now, tr)} · {board(lv)}</div>"]
    small = f"못 탈 확률 {PROB[lv]} (추정)"
    if lvb and BIDX[lvb] > BIDX[lv]:
        small += f" · 붐비는 날엔 {chip(lvb, True)}"
    out.append(f"<div class='n13-mu'>{small}</div>")
    if link:
        out.append(f"<div class='n13-mu'>{link_long(link)}</div>")
    return out


@st.fragment(run_every=CACHE_SEC)
def live_section(routes, demo, dq, direction):
    """자동 갱신 부분. 이 안의 오류도 화면에는 일반 안내만 보이게 감쌈"""
    try:
        _live_section(routes, demo, dq, direction)
    except Exception as e:
        if type(e).__module__.startswith("streamlit"):
            raise
        st.error("일시적인 오류가 생겼어요. 잠시 후 새로고침해 주세요.")


def _live_section(routes, demo, dq, direction):
    P, S_all, T, ratio = load_tables()
    now = get_now(demo, st.query_params)
    day, kind, weekend = day_info(now, dq)
    S = S_all[S_all["일정"] == kind]
    A = load_alt()
    A = A[A["일정"] == kind]
    in_service = now.hour in SERVICE_HOURS
    subway = direction is not None
    stamp = kst_now()
    # 화면 글자는 예시 화면이면 예시 시각, 갱신 지킴이는 data 속성(실제 시각)을 봄
    shown = f"{now:%H:%M} 기준 · 예시 화면" if demo else f"{stamp:%H:%M:%S} 기준"
    html(f"<div class='n13-stamp' data-n13-stamp='{stamp:%H%M%S}'>{shown} · 45초마다 자동 갱신</div>")

    err, last_pass = "", {}
    if demo:
        raw = demo_arrivals(S, now, routes)
    else:
        trk = tracker()
        with trk.lock:
            snap, age, last_pass, terr = trk.snapshot, time.time() - trk.snap_time, dict(trk.last_pass), trk.err
        if snap is not None and age < 200 and not terr:
            raw = snap
        else:
            raw, err = arrivals(N13)
    raw = [r for r in raw if r["노선"] in routes and r["MSG_TP"] != "07"]
    if err:
        html(f"<div class='n13-note'>{LIVE_FAIL}.</div>")

    # 노선별 이번 버스 + 다음 버스 (실시간, 없으면 예정)
    cards, pred = [], []
    for rt in routes:
        live = sorted(r["도착분"] for r in raw if r["노선"] == rt)
        cands = merge_etas(live, sched_etas(S, rt, now, 0, horizon=24 * 60), S, rt, now)
        if not cands:
            cards.append({"키": 10 ** 5, "노선": rt, "c": None, "n": None, "상태": "오늘 남은 버스 없음", "연계": None})
            continue
        e1, k1 = cands[0]
        if e1 > 90:
            cards.append({"키": 10 ** 4 + e1, "노선": rt, "c": None, "n": None, "연계": None,
                          "상태": "90분 안에 버스 없음 · 다음 " + eta_text(rt, e1, k1, now, travel_min(rt, 0))})
            continue
        c = predict_bus(P, S, rt, e1, now, day, last_pass.get(rt) if k1 == "실시간" else None)
        c["종류"] = k1
        car = [r["차량"] for r in raw if r["노선"] == rt and r["도착분"] == e1]
        c["차량"] = car[0] if car and k1 == "실시간" else ""
        n = None
        if len(cands) > 1 and cands[1][0] <= 120:
            e2, k2 = cands[1]
            n = predict_bus(P, S, rt, e2, now, day, hw=e2 - e1)
            n["종류"] = k2
        pred += [x for x in (c, n) if x is not None and x["예측"]]
        link = metro_link(rt, c, now, demo, direction, weekend) if subway else None
        key = link["키"] if link and link["키"] is not None else now.hour * 60 + now.minute + e1 + 1000
        cards.append({"키": key, "노선": rt, "c": c, "n": n, "상태": "", "연계": link})
    # 지하철 환승이면 '몇 시 열차를 타게 되는지'(같은 열차면 버스 먼저 오는 순), 아니면 버스 도착 순
    cards.sort(key=lambda x: (x["키"] if subway else 0, x["c"]["도착분"] if x["c"] else x["키"], x["노선"]))
    pred.sort(key=lambda b: b["도착분"])

    first = next((b for b in pred if b["도착분"] >= 0), None)
    risky = bool(first) and first["보통_탑승"] in ("다소 낮음", "낮음")
    ss = st.session_state
    alts = None
    if in_service and risky:   # N13이 위험할 때만 대체 정류장 조회
        alts = all_alternatives(routes, demo, S, A, now, day, P, ratio, last_pass, in_service, T, subway, first)

    if not in_service:
        hero_card(None, "이 서비스는 09~21시만 예측해요", ["<div class='h2'>지금은 버스 도착 시각만 보여드려요.</div>"])
    elif first is None:
        hero_card(None, "곧 오는 버스가 없어요", ["<div class='h2'>아래에서 다음 버스와 다른 방법을 확인하세요.</div>"])
    elif not risky:
        # 규칙(그대로): N13 다음 버스가 쉬움·보통이면 N13에서 타기. 지하철 환승이면 그중 가장 빠른 열차를 타는 버스
        pick, reason = first, "가장 먼저 오고 " + CAN[first["보통_탑승"]]
        if subway:
            okc = [x for x in cards if x["c"] and x["c"]["예측"] and x["c"]["보통_탑승"] in CAN
                   and x["연계"] and x["연계"]["키"] is not None]
            if okc:
                bx = min(okc, key=lambda x: (x["연계"]["키"], x["c"]["도착분"]))
                if bx["c"] is not first:
                    pick, reason = bx["c"], "가장 빠른 열차를 탈 수 있고 " + CAN[bx["c"]["보통_탑승"]]
        rt = pick["노선"]
        link = next((x["연계"] for x in cards if x["c"] is pick), None)
        extra = []
        if link and link["키"] is not None:
            # 현충원역 11:42 열차 = 월드컵경기장역 11:44 열차처럼, 다른 역에서 타는 같은 열차면 밝혀 줌(11/22 10차)
            same = [x["연계"] for x in cards if x["연계"] and x["연계"]["키"] == link["키"] and x["연계"]["역"] != link["역"]]
            if same:
                extra = [f"<div class='n13-mu'><span class='nw'>{same[0]['역']} {hm(same[0]['열차'])}에 출발하는 열차와</span> "
                         f"<span class='nw'>같은 열차예요</span></div>"]
        hero_card(pick["보통_탑승"], f"N13에서 <span style='color:{rcolor(rt)}'>{rt}번</span>을 타세요",
                  [f"<div class='h2'>{reason}</div>"] +
                  hero_detail(rt, pick["도착분"], pick["종류"], now, travel_min(rt, 0), pick["보통_탑승"], pick["붐빔_탑승"], link)
                  + extra)
    elif risky:
        # 대안: N13 뒤 버스 중 탈 만한 것 + 대체 장소 중 탈 만한 것 → 타는 시각이 빠른 순(서서 갈 수 있는 게 먼저 오면 그것)
        ranked, _, slow, _ = alts
        cand = [{"장소": "N13", "버스": b["노선"], "탈분": b["도착분"], "탑승": b["보통_탑승"], "붐빔탑승": b["붐빔_탑승"],
                 "종류": b["종류"], "걷기": 0, "이동": travel_min(b["노선"], 0), "오프셋": 0} for b in pred if b["보통_탑승"] in CAN]
        cand += [o for o in ranked if o.get("탑승") in CAN and o["장소"] != "N13"]
        cand.sort(key=lambda o: (o["탈분"], BIDX[o["탑승"]]))
        tail = ["<div class='n13-mu'>버스가 모두 20분 이상 걸려요. 급하면 택시</div>"] if slow else []
        if cand:
            o = cand[0]
            rt = o["버스"]
            if o["장소"] == "N13":
                reason = f"앞 버스는 혼잡하고, 이 버스는 {CAN[o['탑승']]}"
                h1 = f"N13에서 <span style='color:{rcolor(rt)}'>{rt}번</span>을 타세요"
            else:
                reason = f"N13은 혼잡해요. 여기서 타면 {CAN[o['탑승']]}"
                h1 = (f"{o['장소']}에서 <span style='color:{rcolor(rt)}'>{rt}번</span>을 타세요 "
                      f"<span class='wk'>· 걸어서 약 {round(o['걷기'])}분</span>")
            link = None
            if subway and o.get("오프셋") is not None:
                link = metro_link(rt, {"도착분": o["탈분"] + o["오프셋"], "차량": ""}, now, demo, direction, weekend)
            hero_card(o["탑승"], h1, [f"<div class='h2'>{reason}</div>"] +
                      hero_detail(rt, o["탈분"], o["종류"], now, o.get("이동"), o["탑승"], o.get("붐빔탑승"), link) + tail)
        else:
            hero_card(first["보통_탑승"], "N13 버스가 혼잡해요",
                      ["<div class='h2'>곧 탈 만한 다른 방법이 없어요. 아래 목록을 확인하세요.</div>"] + tail)
    if weekend:
        html("<div class='n13-note'>주말은 평일(금요일) 데이터로 추정한 값이에요.</div>")
    cn = "" if weekend or not in_service else crowd_note(P, day, now)   # 주말엔 수업이 없어 안 보임
    if cn:
        html(f"<div class='n13-note'><span class='n13-crowd'>몰림 주의</span> {cn}</div>")

    # 노선 카드: 위 3개 + 더 보기
    sub = " <span class='n13-mu' style='font-weight:400'>· 열차 빠른 순</span>" if subway else ""
    html(f"<div class='n13-sec'>N13에 오는 버스{sub}</div>")
    for x in cards[:3]:
        route_card(x["노선"], x["c"], x["n"], now, x["상태"], x["연계"])
    if len(cards) > 3:
        with st.expander(f"다른 노선 더 보기 ({len(cards) - 3}개)"):
            for x in cards[3:]:
                route_card(x["노선"], x["c"], x["n"], now, x["상태"], x["연계"])

    # 어디서 탈까요?: N13이 위험하면 위 3개 + 더 보기, 아니면 펼쳤을 때만 조회(API 아끼기)
    html("<div class='n13-sec'>어디서 탈까요? <span class='n13-mu' style='font-weight:400'>· 타는 시각이 빠른 순</span></div>")
    if alts is not None:
        ranked, rest, slow, failed = alts
        if failed:
            html(f"<div class='n13-note'>다른 정류장은 {LIVE_FAIL}.</div>")
        show = ranked[:2] + [TAXI] if slow else ranked[:3]
        more = ranked[(2 if slow else 3):] + rest + ([] if slow else [TAXI])
        for o in show:
            option_card(o, now)
        if more:
            with st.expander(f"다른 장소 더 보기 ({len(more)}개)"):
                for o in more:
                    option_card(o, now)
    else:
        with st.expander("장소별로 보기", key="more_alt", on_change="rerun"):
            if ss.get("more_alt"):
                ranked, rest, slow, failed = all_alternatives(routes, demo, S, A, now, day, P, ratio, last_pass,
                                                              in_service, T, subway, first)
                if failed:
                    html(f"<div class='n13-note'>다른 정류장은 {LIVE_FAIL}.</div>")
                for o in ranked + rest + [TAXI]:
                    option_card(o, now)


def feedback_section(routes, demo, dq):
    P, S_all, _, _ = load_tables()
    now = get_now(demo, st.query_params)
    day, kind, _ = day_info(now, dq)
    S = S_all[S_all["일정"] == kind]
    ss = st.session_state
    ss["demo_mode"] = demo
    html("<div class='n13-sec'>버스를 타셨나요?</div>")
    if not (feedback_endpoint() or demo):
        html("<div class='n13-mu'>피드백 저장은 준비 중이에요.</div>")
        return
    if ss.get("fb_broken"):
        html("<div class='n13-mu'>피드백 저장이 잠시 안 돼요. 나중에 다시 시도해 주세요.</div>")
        return
    if now.hour not in SERVICE_HOURS:
        html("<div class='n13-mu'>피드백은 09~21시에 받아요.</div>")
        return
    if demo:   # 예시: 시간표상 방금(40분 안) N13에 도착한 노선
        m = now.hour * 60 + now.minute
        s = S[S["노선"].isin(routes) & (S["N13예정분"] <= m) & (S["N13예정분"] >= m - 40)]
        default = int(s.loc[s["N13예정분"].idxmax(), "노선"]) if not s.empty else routes[0]
    else:
        default = recent_route(routes[0])
    route = st.selectbox("노선", ALL_ROUTES, format_func=lambda r: f"{r}번",
                         index=ALL_ROUTES.index(default) if default in ALL_ROUTES else 1, key="fb_route")
    bus = match_bus(route, now, demo, P, S, day)
    if not bus:
        st.caption(f"최근 40분 안에 N13에 도착한 {route}번 버스를 찾지 못했어요.")
        return
    lv = bus["탑승가능성"]
    html(f"<div class='n13-mu'><span class='nw'>{route}번 {bus['도착시각']} 도착 버스</span> · "
         f"<span class='nw'>웹 예측 {chip(lv, True) if lv in BIDX else lv}</span></div>")
    # (저장 값의 탑승가능성은 분석용 이름 그대로 — 피드백 시트와 맞추기 위해)
    bid = f"{route}_{bus['도착시각']}"
    done = ss.setdefault("fb_done", {})
    if bid in done:
        a1, a2 = done[bid]
        st.caption(("예시 화면이라 저장하지 않았어요" if demo else "고마워요! 저장됐어요") + f" (혼잡했나요: {a1} · 탈 수 있었나요: {a2})")
        return
    with st.container(horizontal=True, gap="large"):
        st.segmented_control("혼잡했나요?", ["예", "아니요"], key=f"fbq_{bid}_혼잡", on_change=on_answer, args=(bid, bus, route))
        st.segmented_control("탈 수 있었나요?", ["예", "아니요"], key=f"fbq_{bid}_탑승", on_change=on_answer, args=(bid, bus, route))
    st.caption("두 질문에 답하면 바로 저장돼요. 예측이 맞았는지 확인하는 데 쓰여요. 이름·연락처는 받지 않아요.")


def footer():
    html(f"<div class='n13-mu' style='text-align:center;margin-top:24px'>{LEGEND}<br>"
         "예측은 추정값이에요 · 다른 목적지는 길찾기 앱을 이용하세요<br>"
         "출처: 공공데이터포털 대전 버스 도착정보·노선정보, 국토교통부 TAGO 버스도착정보, 대전교통공사 열차시각표·역간 소요시간, "
         "대전교통 빅데이터 플랫폼 교통카드, 대전교통정보센터·공주시 버스 운행 시각, 타슈 위치 현황, OpenStreetMap</div>")


# 자동 갱신 지킴이: 휴대폰 화면을 껐다 켜거나 다른 앱에 다녀오면 연결이 끊겨 갱신이 멈출 수 있음 →
#  (1) 화면이 1분 넘게 가려졌다가 다시 보이면 새로고침 (2) '기준' 시각 글자가 150초 넘게 안 바뀌면 새로고침
#  사용자의 선택(방향·노선 등)은 주소(쿼리)에 저장해 두어 새로고침해도 그대로
KEEPALIVE = """
<script>
(function(){
  const P = window.parent; if (!P || P.__n13keep) return; P.__n13keep = true;
  let hiddenAt = 0, last = '', changed = Date.now();
  function reload(why){
    try { P.sessionStorage.setItem('n13_reload', why + ' ' + new Date().toTimeString().slice(0, 8)); } catch (e) {}
    P.location.reload();
  }
  P.document.addEventListener('visibilitychange', function(){
    if (P.document.hidden) { hiddenAt = Date.now(); }
    else if (hiddenAt && Date.now() - hiddenAt > 60000) { reload('hidden ' + Math.round((Date.now() - hiddenAt) / 1000) + 's'); }
    else { changed = Date.now(); }
  });
  setInterval(function(){
    const el = P.document.querySelector('[data-n13-stamp]');
    if (!el || P.document.hidden) { changed = Date.now(); return; }
    const t = el.getAttribute('data-n13-stamp');
    if (t !== last) { last = t; changed = Date.now(); }
    else if (Date.now() - changed > 150000) { reload('stale'); }
  }, 10000);
})();
</script>
"""


def _qp_set(name, value):
    try:
        if value in (None, "", []):
            if name in st.query_params:
                del st.query_params[name]
        elif st.query_params.get(name) != str(value):
            st.query_params[name] = str(value)
    except Exception:
        pass


def main():
    st.set_page_config(page_title="N13 하교 버스", layout="centered")
    html(CSS)
    components.html(KEEPALIVE, height=0)
    qp = st.query_params
    demo = "demo" in qp
    dq = qp.get("day") if demo and qp.get("day") in list(DAYS) else None
    now = get_now(demo, qp)
    html("<div class='n13-title'>N13 하교 버스</div>"
         f"<div class='n13-sub'>삼성화재연수원 정류장(41730) · {now:%H:%M} {dq or DAYS[now.weekday()]}요일</div>")
    ss = st.session_state
    pre = [int(x) for x in str(qp.get("routes", "")).split(",") if x.strip().isdigit() and int(x) in ALL_ROUTES]
    # 처음 열 때만 주소의 값으로 선택을 채움(새로고침해도 유지)
    if "mode" not in ss:
        ss["mode"] = MODES[1] if (pre or qp.get("mode") == "route") else MODES[0]
    if "dir" not in ss:
        ss["dir"] = DIRS[1] if qp.get("dir") == "pan" else DIRS[0]
    mode = st.segmented_control("어떻게 가요?", MODES, required=True, key="mode", width="stretch")
    direction = None
    if mode != MODES[1]:
        routes = SUBWAY_ROUTES
        direction = st.segmented_control("열차 방향", DIRS, required=True, key="dir", width="stretch")
        _qp_set("mode", None)
        _qp_set("dir", "pan" if direction == DIRS[1] else None)
        _qp_set("dest", None)
        _qp_set("routes", None if not demo else qp.get("routes"))
    else:
        if "routes_sel" not in ss:
            ss["routes_sel"] = pre or [102]
        routes = st.multiselect("노선", ALL_ROUTES, key="routes_sel", format_func=lambda r: f"{r}번",
                                placeholder="노선을 골라 주세요")
        _qp_set("mode", "route")
        _qp_set("routes", ",".join(map(str, routes)))
        _qp_set("dir", None)
        _qp_set("dest", None)
        if not routes:
            html("<div class='n13-mu'>노선을 하나 이상 골라 주세요.</div>")
            footer()
            return
    live_section(routes, demo, dq, direction)
    feedback_section(routes, demo, dq)
    footer()


try:
    main()
except Exception as e:
    if type(e).__module__.startswith("streamlit"):  # Streamlit 내부 제어(다시 실행 등)는 그대로 넘김
        raise
    st.error("일시적인 오류가 생겼어요. 잠시 후 새로고침해 주세요.")  # 자세한 내용은 화면에 보이지 않음
