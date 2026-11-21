"""N13 하교 버스 — 지금 어떻게 움직일까? (Streamlit)

실행(로컬): 프로젝트 폴더에서  python -m streamlit run web/app.py
비밀 값(화면·로그에 출력하지 않음)
  DAEJEON_BUS_KEY   : 배포 비밀 설정(Secrets) → 환경변수 → 상위 폴더 .env 순서로 읽음
  FEEDBACK_ENDPOINT : 피드백 저장용 Apps Script 웹 앱 주소. Secrets 또는 환경변수에서만 읽음(코드에 쓰지 않음)
예측 방법 (analysis/REPORT.md)
  버스 1대 예상 인원 = 그 시간대 1분당 탑승률(부분 풀링, 9~10월 교통카드) × 같은 노선 앞차 간격(실시간, 없으면 시간표)
  혼잡도(4단계) = 버스 안 인원을 28/40/55명 기준에 넣은 단계. 탑승 가능성 = N13 출발 인원(도착 + N13 대기 − 하차) 기준
  대체 정류장(정문·수통골삼거리·덕명중·수통골입구) 인원 = N13 도착 예상 인원 × 그 정류장 비율(alt_stop_load.py, 9~10월 교통카드)
지원 시간: 요일과 상관없이 09:00~21:59. 그 밖에는 예측 없이 실시간 도착만. 주말은 금요일 예측표로 추정
대체경로 추천: 걷는 시간 + 여유 1.5분보다 늦게 오는 첫 버스(실시간, 없으면 시간표)만 탈 수 있다고 보고,
  실제로 타는 시각이 빠른 순 → 같으면 덜 붐비는 순으로 정렬. 상위 3개만 보이고 나머지는 '다른 방법 더 보기'
자동 갱신: 버스·대체경로 부분만 45초마다 다시 그림(st.fragment). API는 서버 저장값을 쓰므로 갱신해도 호출이 늘지 않음
API 호출 줄이기: 같은 정류장 도착정보는 60초 저장(실패도 저장), N13은 백그라운드에서 60초마다 1번만 조회
공주 버스(300·340): 공주시 API로 덕명네거리 정류장을 찾지 못해 실시간 조회 안 함(안내 문구만)
예시 모드: 주소 뒤에 ?demo=16:40&day=월(&routes=102)  → 시간표로 만든 가상 도착(발표·캡처용, '예시' 표시, 피드백 저장 안 함)
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

HERE = Path(__file__).resolve().parent
KST = dt.timezone(dt.timedelta(hours=9))
DAYS = "월화수목금토일"
SERVICE_HOURS = range(9, 22)                   # 09:00~21:59 (prediction_table 시간대 9~21)
TH = (28, 40, 55)
CONG = {1: "앉을 수 있음", 2: "서서 감", 3: "혼잡", 4: "매우 혼잡"}
BOARD = {1: "높음", 2: "다소 높음", 3: "다소 낮음", 4: "낮음"}
BOARD_TEXT = {"높음": "여유 있게 탈 수 있어요", "다소 높음": "서서 갈 수 있어요",
              "다소 낮음": "혼잡해요. 못 탈 수도 있어요", "낮음": "매우 혼잡해요. 못 탈 가능성이 높아요"}
LEADB = {"높음": "여유 있게 탈 수 있어요", "다소 높음": "서서 갈 수 있어요", "다소 낮음": "혼잡해요", "낮음": "매우 혼잡해요"}
WARN = {2: "서서 가야 할", 3: "혼잡할", 4: "매우 혼잡할"}
PROB = {"높음": "10% 미만", "다소 높음": "10~20%", "다소 낮음": "20~40%", "낮음": "40% 이상"}  # 화면 표시용 구간(추정)
# 혼잡도 색: 버스 번호 색(파랑·녹색)과 겹치지 않는 노랑 → 주황 → 빨강. 글자색은 대비 4.5:1 이상(docs/ui_check.md)
CHIP = {1: ("#fef3c7", "#78350f"), 2: ("#fed7aa", "#7c2d12"), 3: ("#fecaca", "#7f1d1d"), 4: ("#991b1b", "#ffffff")}
BAR = {1: "#eab308", 2: "#f97316", 3: "#dc2626", 4: "#7f1d1d"}

# 노선 색 (docs/route_colors.md) — 사용자 확인(매일 타는 사용자가 직접 본 차량 색, 11/21)
BLUE, GREEN, GRAY = "#1d5fd1", "#1a7f3a", "#4b5563"   # 흰 글자 대비 5.8 / 5.1 (docs/ui_check.md)
ROUTE_COLOR = {102: BLUE, 104: BLUE, 107: BLUE, 113: BLUE, 48: BLUE, 11: GREEN, 117: GREEN, 212: GREEN}

N13 = "41730"
ALL_ROUTES = [11, 102, 104, 113, 117, 212]
SUBWAY_ROUTES = ALL_ROUTES   # 노선정보 API 경유 정류장: 6개 모두 N13 다음에 지하철역 근처를 지남(analysis/subway_routes_check.csv)
MODES = ["지하철 환승", "특정 노선 (여러 개 선택)"]
BUFFER = 1.5                 # 걷는 시간에 더하는 여유(분)
# 대체 정류장: (이름, ARS, 걷는 분(추정), 노선, N13보다 먼저 오는 분(추정), 설명)
#   걷는 시간: data/walk_times.csv(정문 6.8분), analysis/alt_nearby_stops.csv(수통골삼거리 11.1, 수통골입구 10.7, 덕명네거리 11.5분)
#   먼저 오는 분: 정문 1분(실측 정문→N13 대부분 1분), 수통골삼거리·수통골입구 2정거장 앞 2분(추정)
PLACES = [("정문", "41690", 6.8, ALL_ROUTES, 1, "N13보다 덜 찬 상태로 와요. 정문에서 타는 사람이 많아요"),
          ("수통골삼거리", "41670", 11.1, [11, 102, 104], 2, "정문 전 정류장이라 덜 찬 상태로 와요"),
          ("덕명중·수통골입구", "45770", 10.7, [113, 117, 212], 2, "정문 전 정류장이라 덜 찬 상태로 와요 (덕명중학교·수통골입구는 거의 같은 곳)"),
          ("덕명네거리", "41400", 11.5, [48, 107, 300, 340], None, "현충원역 방면 · 대전 48·107번, 공주 300·340번")]
CACHE_SEC = 45            # 화면 자동 갱신 간격
API_TTL = 60              # 도착정보 저장 시간: 정류장 5곳 × 하루 1,440번 = 최대 7,200건(한도 10,000)


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
    """덕명네거리 107번 시간표 예정 (parse_timetable_alt.py: 회차지 동학사 출발 + 27분, 추정). 48번은 대전 시간표에 없음"""
    p = HERE / "data" / "schedule_alt.csv"
    return pd.read_csv(p) if p.exists() else pd.DataFrame(columns=["일정", "노선", "정류장", "예정분", "예정시각"])


def _secret(name):
    try:
        v = st.secrets.get(name, "")
    except Exception:
        v = ""
    return str(v or os.environ.get(name, "")).strip()


def service_key():
    k = _secret("DAEJEON_BUS_KEY")
    if not k:
        env = HERE.parent / ".env"
        if env.exists():
            for line in env.read_text(encoding="utf-8-sig").splitlines():
                if line.strip().startswith("DAEJEON_BUS_KEY="):
                    k = line.split("=", 1)[1].strip().strip('"').strip("'")
    return urllib.parse.unquote(k) if "%" in k else k


def safe_msg(e):
    """예외를 남길 때: 종류 이름만, 혹시 키·주소가 섞이면 가림"""
    s = type(e).__name__ if isinstance(e, BaseException) else str(e)
    k = service_key()
    if k:
        s = s.replace(k, "***").replace(urllib.parse.quote(k, safe=""), "***")
    return re.sub(r"https?://\S+", "[주소 가림]", s)[:80]


def _call_arrivals(ars):
    """도착정보 API 1번 호출 → [{노선, 차량, 도착분, 남은정류장, MSG_TP}]. 실패하면 예외(종류 이름만, 주소·키 없음)"""
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


@st.cache_data(ttl=API_TTL, show_spinner=False)
def arrivals(ars):
    """60초 저장. 실패도 저장해서, API가 멈췄을 때 접속자마다 다시 부르지 않음"""
    try:
        return _call_arrivals(ars), ""
    except Exception as e:
        return [], safe_msg(e)


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


def predict_bus(P, S, route, eta, now, day, last_pass=None):
    t_arr = now + dt.timedelta(minutes=eta)
    res = {"노선": route, "도착분": eta, "도착시각": t_arr.strftime("%H:%M"), "도착dt": t_arr, "예측": False}
    key = (route, day, t_arr.hour)
    if t_arr.hour not in SERVICE_HOURS or key not in P.index:
        return res
    r = P.loc[key]
    sh = sched_headway(S, route, t_arr) or float(r["시간표_평균간격_분"])
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
    """N13 도착정보를 60초마다 조회
    - 앞차 통과 시각(track_buses.py 규칙: 남은 정류장 1로 보이던 차가 다음 조회에서 사라지면 통과, 기점 대기 MSG_TP 07 제외)
    - 버스(노선·차량)마다 마지막으로 계산한 웹 예측(혼잡도·탑승 가능성)과 예측 도착·실제 통과 시각 → 피드백 짝짓기에 사용
      (차량번호는 서버 메모리에만 있고 화면·저장에는 쓰지 않음, 3시간 지나면 지움)"""

    def __init__(self, P, S_all):
        self.P, self.S_all = P, S_all
        self.lock = threading.Lock()
        self.snapshot, self.snap_time, self.last_pass, self.prev, self.store = None, 0.0, {}, {}, {}
        threading.Thread(target=self.loop, daemon=True).start()

    def step(self):
        rows = _call_arrivals(N13)
        now = dt.datetime.now(KST).replace(second=0, microsecond=0)
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
            self.prev, self.snapshot, self.snap_time = cur, rows, time.time()

    def loop(self):
        while True:
            try:
                self.step()
            except Exception:
                pass  # 로그에 아무것도 남기지 않음(키가 섞일 일 없음)
            time.sleep(60)

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
        with urllib.request.urlopen(req, timeout=10) as r:   # Apps Script는 302로 결과 페이지를 돌려줌(자동 따라감)
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
        now = dt.datetime.now(KST)
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
CSS = """
<style>
.block-container{padding-top:3.2rem;padding-bottom:2rem;max-width:560px}
[data-testid="stHeaderActionElements"],.stMarkdown h1 a,.stMarkdown h2 a,.stMarkdown h3 a{display:none!important}
.n13-title{text-align:center;font-size:1.45rem;font-weight:700;color:#111827;margin:0;line-height:1.3}
.n13-sub{text-align:center;font-size:.82rem;color:#4b5563;margin:2px 0 10px}
.n13-card{background:#fff;border:1px solid #d1d5db;border-radius:12px;padding:12px 14px;margin:0 0 8px;color:#111827}
.n13-card.plan{border-style:dashed;background:#fafafa}
.n13-card.plan .n13-body{opacity:.85}
.n13-lead{font-size:1.2rem;font-weight:700;line-height:1.45}
.n13-sec{font-size:1rem;font-weight:700;color:#111827;margin:18px 0 8px}
.n13-pill{display:inline-block;color:#fff;border-radius:8px;padding:0 8px;font-weight:700;font-size:.95rem;line-height:1.6;white-space:nowrap}
.n13-tag{display:inline-block;font-size:.75rem;color:#4b5563;border:1px dashed #6b7280;border-radius:999px;padding:0 7px;margin-left:4px;vertical-align:middle}
.n13-tag.live{color:#111827;border:1px solid #111827;font-weight:600}
.n13-chip{display:inline-block;border-radius:8px;padding:2px 10px;font-weight:700;font-size:1.05rem}
.n13-sm{font-size:.88rem;color:#374151;line-height:1.5}
.n13-mu{font-size:.8rem;color:#4b5563;line-height:1.5}
.n13-best{border:2px solid #111827}
.n13-note{font-size:.88rem;color:#374151;background:#f3f4f6;border-radius:12px;padding:8px 12px;margin:0 0 8px}
.n13-warn{font-size:.85rem;color:#7f1d1d;font-weight:600;margin-top:2px}
div[data-testid="stButtonGroup"] button{min-height:44px;min-width:64px}
label[data-testid="stRadioOption"]{min-height:44px;align-items:center;padding-right:8px}
details summary{min-height:44px}
</style>
"""


def pill(rt):
    return f"<span class='n13-pill' style='background:{ROUTE_COLOR.get(rt, GRAY)}'>{rt}번</span>"


def tag(kind):
    return "<span class='n13-tag live'>● 실시간</span>" if kind == "실시간" else "<span class='n13-tag'>○ 시간표 기준</span>"


BIDX = {v: k for k, v in BOARD.items()}   # 탑승 가능성 → 1(높음)~4(낮음)


def chip(level):
    """탑승 가능성 칩 (색 + 글자). 색은 노랑→주황→빨강 계열로 버스 번호 색(파랑·녹색)과 겹치지 않음"""
    bg, fg = CHIP[BIDX[level]]
    return f"<span class='n13-chip' style='background:{bg};color:{fg}'>{level}</span>"


def board_line(level):
    return (f"<div style='margin-top:6px'>{chip(level)} <b>{BOARD_TEXT[level]}</b> "
            f"<span class='n13-sm'>(못 탈 확률 {PROB[level]})</span></div>")


def when(m):
    return "곧 도착" if m <= 1 else f"{m}분 후"


def html(s):
    # 물결표(~)가 두 개 있으면 마크다운이 취소선으로 바꿔서, HTML 문자로 바꿔 넣음
    st.markdown(s.replace("~", "&#126;"), unsafe_allow_html=True)


def bus_card(b, demo):
    plan = b["종류"] != "실시간"
    head = (f"<div>{pill(b['노선'])} <b style='font-size:1.05rem'>{when(b['도착분'])}</b> "
            f"<span class='n13-mu'>{b['도착시각']}</span>{tag(b['종류'])}</div>")
    if not b["예측"]:
        html(f"<div class='n13-card{' plan' if plan else ''}'>{head}<div class='n13-mu'>지원 시간(09~21시) 밖이라 예측하지 않아요</div></div>")
        return
    lv, lv2 = b["보통_탑승"], b["붐빔_탑승"]
    warn = f"<div class='n13-warn'>붐비는 날에는 '{lv2}'까지 낮아질 수 있어요</div>" if BIDX[lv2] > BIDX[lv] else ""
    extra = " · 시간표 기준이라 실제 도착은 달라질 수 있어요" if plan else ""
    html(f"<div class='n13-card{' plan' if plan else ''}' style='border-left:6px solid {BAR[BIDX[lv]]}'>{head}"
         f"<div class='n13-body'>{board_line(lv)}{warn}"
         f"<div class='n13-mu' style='margin-top:2px'>버스 안 {CONG[b['보통_혼잡']]} · 약 {b['보통_도착']:.0f}명 · "
         f"앞차 간격 {b['앞차간격']:.0f}분({b['간격출처']}){extra}{' · 예시' if demo else ''}</div></div></div>")


def demo_arrivals(S, now, routes, offset=0):
    """예시 모드: 시간표로 만든 가상 도착 (노선마다 가장 가까운 1대, 실제 API처럼)"""
    out = []
    for rt in routes:
        e = sched_etas(S, rt, now, offset, 60)
        if e:
            out.append({"노선": rt, "차량": f"예시{rt}-{e[0]}", "도착분": e[0], "남은정류장": "", "MSG_TP": ""})
    return out


def tashu_info(T):
    """타슈: N13 근처 대여소와 걷는 시간만 (data/tashu_near.csv). 실시간 대수 API는 아직 동작 안 함 → '준비 중'"""
    if T.empty or "N13" not in set(T["쪽"]):
        return None
    a = T[T["쪽"] == "N13"].sort_values("걷는거리_m").iloc[0]
    return {"이름": a["대여소명"].split(" ", 1)[-1], "걷기": round(a["걷는시간_분"])}


REALTIME_ONLY = {48, 300, 340}   # 대전 시간표에 없음 → 대전 도착정보(41400)에 잡힐 때만


def place_options(routes, demo, S, A, now, day, P, ratio, last_pass, in_service):
    """대체 장소마다: 걸어서(+여유) 도착한 뒤 탈 수 있는 첫 버스(실시간, 없으면 시간표)와 그 버스의 탑승 가능성.
    탑승 가능성(추정) = 그 정류장을 떠날 때 버스 안 인원을 28/40/55명 기준에 넣은 단계
      정문: 정문을 떠날 때 = N13 도착 인원 / 수통골삼거리·덕명중·수통골입구: N13 도착 인원 × 정류장 비율(alt_stop_ratio.csv)
    혼잡도(보조) = 그 정류장에 올 때 버스 안 인원 (정문은 앞 정류장 비율, 나머지는 위와 같음)
    탈 버스가 없어도 빼지 않고 이유(상태)를 붙여서 돌려줌"""
    m = now.hour * 60 + now.minute
    opts = []
    for name, ars, walk, prts, offset, note in PLACES:
        base = {"장소": name, "걷기": walk, "버스": None, "설명": note}
        rts = [r for r in prts if r in routes] if offset is not None else prts
        if not rts:
            opts.append({**base, "상태": f"고른 노선은 이 정류장을 지나지 않아요 (이 정류장: {'·'.join(map(str, prts))}번)"})
            continue
        if demo:
            rows, err = (demo_arrivals(S, now, rts, offset), "") if offset is not None else ([], "")
        else:
            rows, err = arrivals(ars)
        best, no_info, later = None, [], []
        for rt in rts:
            live = [r["도착분"] for r in rows if r["노선"] == rt and r["MSG_TP"] != "07"]
            if offset is not None:
                sched = sched_etas(S, rt, now, offset, horizon=24 * 60)
            else:   # 덕명네거리: 107번은 시간표(parse_timetable_alt.py), 48·300·340번은 실시간만
                sched = sorted(int(v - m) for v in A.loc[A["노선"] == rt, "예정분"] if v - m >= 0)
            if not live and not sched:
                no_info.append(rt)
                continue
            cands = merge_etas(live, sched, S, rt, now)
            ok = [(e, k) for e, k in cands if e > walk + BUFFER]
            if not ok:
                no_info.append(rt)
                continue
            e, kind = ok[0]
            if e > 90:   # 너무 먼 버스(새벽 등)는 '다음 버스 시각'만 이유로 적음
                later.append(f"{rt}번 {(now + dt.timedelta(minutes=e)).strftime('%H:%M')}")
                continue
            s, ppl, lv = None, None, None
            if offset is not None and in_service:
                b = predict_bus(P, S, rt, e + offset, now, day, last_pass.get(rt) if kind == "실시간" else None)
                if b["예측"]:
                    r = ratio.get((rt, b["도착dt"].hour), 1.0)
                    leave = b["보통_도착"] if name == "정문" else b["보통_도착"] * r
                    ppl = b["보통_도착"] * r
                    s, lv = stage(ppl), BOARD[stage(leave)]
            cand = {**base, "버스": rt, "탈분": e, "종류": kind, "혼잡": s, "인원": ppl, "탑승": lv}
            if best is None or rank_key(cand) < rank_key(best):
                best = cand
        miss_rt = [r for r in no_info if r in REALTIME_ONLY]
        miss_sc = [r for r in no_info if r not in REALTIME_ONLY]
        why_parts = ([f"{'·'.join(map(str, miss_rt))}번은 실시간 정보 없음"] if miss_rt else []) + \
                    ([f"{'·'.join(map(str, miss_sc))}번은 오늘 남은 버스 없음"] if miss_sc else [])
        if best:
            if why_parts:
                best["설명"] = note + " · " + " · ".join(why_parts)
            opts.append(best)
        elif later:
            opts.append({**base, "상태": "90분 안에 탈 수 있는 버스 없음 · 다음 버스(시간표 기준) " + ", ".join(sorted(later, key=lambda x: x[-5:])[:2])
                         + (" · " + " · ".join(why_parts) if miss_rt else "")})
        else:
            opts.append({**base, "상태": ("실시간 정보를 불러오지 못했어요 · " if err else "") + (" · ".join(why_parts) or "오늘 남은 버스 없음")})
    return opts


TAXI = {"장소": "택시", "걷기": 0, "버스": None, "설명": "", "상태": "최후의 수단"}


def option_card(o, best=False, demo=False):
    plan = o.get("종류") == "시간표"
    badge = "<span class='n13-tag live'>추천</span>" if best else ""
    walk = "" if o["장소"] in ("N13에서 기다리기", "택시", "타슈") else f"걸어서 {o['걷기']:g}분 · "
    if o.get("버스") is None:
        body = f"<div class='n13-sm'>{walk}{o['상태']}</div>"
    else:
        main = board_line(o["탑승"]) if o.get("탑승") else ""
        sub = f"<div class='n13-mu'>버스 안 {CONG[o['혼잡']]} · 약 {o['인원']:.0f}명</div>" if o.get("혼잡") else \
              ("<div class='n13-mu'>탑승 가능성 예측 없음</div>" if o.get("탑승") is None else "")
        body = f"<div class='n13-sm'>{walk}{pill(o['버스'])} <b>{o['탈분']}분 뒤 탑승</b>{tag(o['종류'])}</div>{main}{sub}"
    desc = (o["설명"] or "") + (" · 예시" if demo and o["설명"] else "")
    title = "택시 · 최후의 수단" if o["장소"] == "택시" else o["장소"]
    if o["장소"] == "택시":
        body = ""
    html(f"<div class='n13-card{' plan' if plan else ''}{' n13-best' if best else ''}'>"
         f"<div style='font-weight:700'>{title}{badge}</div><div class='n13-body'>{body}"
         + (f"<div class='n13-mu'>{desc}</div>" if desc else "") + "</div></div>")


def get_now(demo, qp):
    now = dt.datetime.now(KST).replace(second=0, microsecond=0)
    if demo:
        try:
            hh, mm = map(int, qp.get("demo", "16:40").split(":"))
            now = now.replace(hour=hh, minute=mm)
        except ValueError:
            pass
    return now


def rank_key(o):
    """탈 만한 방법(탑승 가능성 높음·다소 높음, 또는 예측 없음)이 먼저 → 타는 시각이 빠른 순 → 탑승 가능성이 높은 순"""
    b = BIDX.get(o.get("탑승"), 2.5)
    return (b > 2.5, o["탈분"], b)


@st.fragment(run_every=CACHE_SEC)
def live_section(routes, demo, dq):
    """자동 갱신 부분. 이 안의 오류도 화면에는 일반 안내만 보이게 감쌈"""
    try:
        _live_section(routes, demo, dq)
    except Exception as e:
        if type(e).__module__.startswith("streamlit"):
            raise
        st.error("일시적인 오류가 생겼어요. 잠시 후 새로고침해 주세요.")


def _live_section(routes, demo, dq):
    """결론 → 버스 목록 → 다른 방법. 45초마다 이 부분만 다시 그림(API는 서버 저장값 사용)"""
    P, S_all, T, ratio = load_tables()
    now = get_now(demo, st.query_params)
    day, kind, weekend = day_info(now, dq)
    S = S_all[S_all["일정"] == kind]
    in_service = now.hour in SERVICE_HOURS

    err, last_pass = "", {}
    if demo:
        raw = demo_arrivals(S, now, routes)
    else:
        tr = tracker()
        with tr.lock:
            snap, age, last_pass = tr.snapshot, time.time() - tr.snap_time, dict(tr.last_pass)
        if snap is not None and age < 90:
            raw = snap
        else:
            raw, err = arrivals(N13)
    raw = [r for r in raw if r["노선"] in routes and r["MSG_TP"] != "07"]
    A = load_alt()
    A = A[A["일정"] == kind]
    places = place_options(routes, demo, S, A, now, day, P, ratio, last_pass, in_service)
    tashu = tashu_info(T)
    tashu_opt = ({"장소": "타슈", "걷기": tashu["걷기"], "버스": None, "설명": "공영자전거 · 실시간 대수는 준비 중",
                  "상태": f"근처 대여소({tashu['이름']})까지 걸어서 약 {tashu['걷기']}분"} if tashu else
                 {"장소": "타슈", "걷기": 0, "버스": None, "설명": "공영자전거", "상태": "근처 대여소 정보 없음"})

    if not in_service:
        html("<div class='n13-card'><div class='n13-lead'>이 서비스는 09~21시만 지원해요</div>"
             "<div class='n13-sm'>지금은 예측 없이 실시간 도착만 보여드려요.</div></div>")
        html("<div class='n13-sec'>N13 실시간 도착</div>")
        if err or not raw:
            html(f"<div class='n13-card n13-sm'>{'실시간 정보를 불러오지 못했어요' if err else '지금 실시간으로 잡히는 버스가 없어요'}</div>")
        for r in sorted(raw, key=lambda r: r["도착분"]):
            t = (now + dt.timedelta(minutes=r["도착분"])).strftime("%H:%M")
            html(f"<div class='n13-card'>{pill(r['노선'])} <b>{when(r['도착분'])}</b> <span class='n13-mu'>{t}</span>{tag('실시간')}</div>")
        html("<div class='n13-sec'>다른 방법</div>")
        for o in places + [tashu_opt, TAXI]:
            option_card(o, demo=demo)
        return

    # N13 버스 (실시간 + 시간표 기준)
    buses = []
    for rt in routes:
        live = sorted(r["도착분"] for r in raw if r["노선"] == rt)
        cands = merge_etas(live, sched_etas(S, rt, now, 0, 60), S, rt, now)
        for e, k in cands[: 1 if len(routes) > 2 else 3]:
            b = predict_bus(P, S, rt, e, now, day, last_pass.get(rt) if k == "실시간" else None)
            b["종류"] = k
            buses.append(b)
    buses.sort(key=lambda b: b["도착분"])
    pred = [b for b in buses if b["예측"]]

    # 추천 순위: N13에서 기다리기(탑승 가능성 '높음·다소 높음' 버스만 — '다소 낮음·낮음'은 못 탈 수도 있어서 뺌) + 대체 장소.
    # 타는 시각이 빠른 순 → 같으면 덜 붐비는 순
    opts = []
    n13ok = [b for b in pred if b["보통_탑승"] in ("높음", "다소 높음")]
    if n13ok:
        b = min(n13ok, key=lambda b: (b["도착분"], b["보통_혼잡"]))
        opts.append({"장소": "N13에서 기다리기", "걷기": 0, "버스": b["노선"], "탈분": b["도착분"], "종류": b["종류"],
                     "혼잡": b["보통_혼잡"], "인원": b["보통_도착"], "설명": "지금 있는 곳에서 기다려요", "탑승": b["보통_탑승"]})
    else:   # 빼지 않고 이유를 적어서 '더 보기'에
        opts.append({"장소": "N13에서 기다리기", "걷기": 0, "버스": None, "설명": "지금 있는 곳에서 기다려요",
                     "상태": "1시간 안에 오는 버스가 모두 혼잡해요(탑승 가능성 다소 낮음 이하)" if pred else "1시간 안에 오는 버스 정보 없음"})
    ranked = sorted([o for o in places + opts if o.get("버스") is not None], key=rank_key)
    n13_bad = bool(pred) and pred[0]["보통_탑승"] in ("다소 낮음", "낮음")
    # 정문은 N13 탑승 가능성이 '다소 낮음·낮음'일 때만 추천 후보
    if not n13_bad:
        ranked = [o for o in ranked if o["장소"] != "정문"] + [o for o in ranked if o["장소"] == "정문"]
    others = [o for o in places + opts if o not in ranked]
    top = ranked[0] if ranked else None
    # 택시: 평소엔 '더 보기' 맨 아래, 버스 방법이 모두 20분 이상 걸릴 때만 위로
    all_slow = not any(o["탈분"] < 20 for o in ranked)

    # 1) 결론 한 문장
    if err and not pred:
        lead, sub = "실시간 정보를 불러오지 못했어요", "아래는 시간표와 과거 통계(9~10월)로 만든 예측이에요."
    elif top and top["장소"] == "N13에서 기다리기":
        lead = f"지금은 {'곧' if top['탈분'] <= 1 else str(top['탈분']) + '분 뒤'} {top['버스']}번이 {LEADB[top['탑승']]}"
        before = [b for b in pred if b["도착분"] < top["탈분"]]
        sub = f"그 전에 오는 {before[0]['노선']}번({when(before[0]['도착분'])})은 못 탈 가능성이 높아요." if before else ""
        if top["종류"] != "실시간":
            sub = (sub + " " if sub else "") + "시간표 기준 버스예요."
    elif top:
        lead = f"{top['장소']}까지 걸어가면 {top['탈분']}분 뒤 {top['버스']}번을 탈 수 있어요"
        sub = (f"탑승 가능성 {top['탑승']} · {BOARD_TEXT[top['탑승']]}." if top.get("탑승") else "탑승 가능성 예측은 없어요.") + (" N13 버스는 혼잡해요." if n13_bad else "")
    elif pred:
        lead, sub = "N13에 오는 버스가 매우 혼잡해요", "아래 '다른 방법'도 확인하세요."
    else:
        lead, sub = "지금 N13에 오는 버스 정보가 없어요", "아래 '다른 방법'을 확인하세요."
    if all_slow and not (err and not pred):
        sub = (sub + " " if sub else "") + "버스는 모두 20분 이상 기다려야 해요. 급하면 택시도 있어요."
    html(f"<div class='n13-card'><div class='n13-lead'>{lead}</div>"
         + (f"<div class='n13-sm' style='margin-top:2px'>{sub}</div>" if sub else "") + "</div>")
    if weekend:
        html("<div class='n13-note'>주말은 평일(금요일) 데이터로 추정한 값이에요.</div>")
    crowd = sorted({b["몰림주의"] for b in pred if b["몰림주의"]})
    if crowd:
        html(f"<div class='n13-note'><b style='color:#7f1d1d'>몰림 주의 {crowd[0]}</b> · "
             "N13 쪽 건물에서 수업이 많이 끝나는 시간대라, 표시보다 더 붐빌 수 있어요.</div>")

    # 2) 버스 목록
    html("<div class='n13-sec'>N13에 오는 버스 <span class='n13-mu' style='font-weight:400'>· 45초마다 자동 갱신</span></div>")
    if buses:
        for b in buses:
            bus_card(b, demo)
    else:
        html("<div class='n13-card n13-sm'>지금 실시간으로 잡히는 버스도, 1시간 안 시간표 버스도 없어요.</div>")
        h = now.hour
        for rt in routes:
            if (rt, day, h) in P.index:
                r = P.loc[(rt, day, h)]
                html(f"<div class='n13-card n13-sm'>{pill(rt)} 과거 통계({day}요일 {h}시): 보통 날 {r['보통_혼잡도']} · 붐비는 날 {r['붐빔_혼잡도']}</div>")

    # 3) 다른 방법: 상위 3개 + 더 보기
    html("<div class='n13-sec'>어디서 탈까요? <span class='n13-mu' style='font-weight:400'>· 타는 시각이 빠른 순</span></div>")
    if all_slow:
        show = ranked[:2] + [TAXI]
        rest = ranked[2:] + others + [tashu_opt]
    else:
        show = ranked[:3]
        rest = ranked[3:] + others + [tashu_opt, TAXI]
    for i, o in enumerate(show):
        option_card(o, best=(i == 0 and o.get("버스") is not None), demo=demo)
    with st.expander(f"다른 방법 더 보기 ({len(rest)}개)"):
        for o in rest:
            option_card(o, demo=demo)


def feedback_section(routes, demo, dq):
    P, S_all, _, _ = load_tables()
    now = get_now(demo, st.query_params)
    day, kind, _ = day_info(now, dq)
    S = S_all[S_all["일정"] == kind]
    ss = st.session_state
    ss["demo_mode"] = demo
    html("<div class='n13-sec'>버스를 타셨나요?</div>")
    if not (feedback_endpoint() or demo):
        html("<div class='n13-card n13-sm'>피드백 저장은 준비 중이에요.</div>")
        return
    if ss.get("fb_broken"):
        html("<div class='n13-card n13-sm'>피드백 저장이 잠시 안 돼요. 나중에 다시 시도해 주세요.</div>")
        return
    if now.hour not in SERVICE_HOURS:
        html("<div class='n13-card n13-sm'>피드백은 09~21시에 받아요.</div>")
        return
    if demo:   # 예시: 시간표상 방금(40분 안) N13에 도착한 노선
        m = now.hour * 60 + now.minute
        s = S[S["노선"].isin(routes) & (S["N13예정분"] <= m) & (S["N13예정분"] >= m - 40)]
        default = int(s.loc[s["N13예정분"].idxmax(), "노선"]) if not s.empty else routes[0]
    else:
        default = recent_route(routes[0])
    with st.container(border=True):
        route = st.selectbox("노선", ALL_ROUTES, format_func=lambda r: f"{r}번",
                             index=ALL_ROUTES.index(default) if default in ALL_ROUTES else 1, key="fb_route")
        bus = match_bus(route, now, demo, P, S, day)
        if not bus:
            st.caption(f"최근 40분 안에 N13에 도착한 {route}번 버스를 찾지 못했어요.")
            return
        html(f"<div class='n13-sm'>{pill(route)} {bus['도착시각']} 도착 버스 · 웹 예측: {bus['혼잡도']}, 탑승 가능성 {bus['탑승가능성']}</div>")
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
    html("<div class='n13-mu' style='text-align:center;margin-top:18px'>예측은 추정값이에요 · 45초마다 자동 갱신<br>"
         "다른 목적지는 길찾기 앱을 이용하세요<br>"
         "출처: 공공데이터포털 대전광역시 버스 도착정보·노선정보, 대전교통 빅데이터 플랫폼 교통카드, 대전교통정보센터 시간표, 타슈 위치 현황, OpenStreetMap</div>")


def main():
    st.set_page_config(page_title="N13 하교 버스", layout="centered")
    html(CSS)
    qp = st.query_params
    demo = "demo" in qp
    dq = qp.get("day") if demo and qp.get("day") in list(DAYS) else None
    now = get_now(demo, qp)
    html("<div class='n13-title'>N13 하교 버스</div>"
         f"<div class='n13-sub'>삼성화재연수원 정류장(41730) · {now:%H:%M} {dq or DAYS[now.weekday()]}요일"
         + (" · 예시 화면" if demo else "") + "</div>")
    # 예시 모드에서 ?routes=102,104 를 붙이면 '특정 노선'으로 시작 (발표·캡처용)
    pre = [int(x) for x in str(qp.get("routes", "")).split(",") if x.strip().isdigit() and int(x) in ALL_ROUTES] if demo else []
    mode = st.radio("어떻게 가요?", MODES, horizontal=True, index=1 if pre else 0)
    if mode == MODES[0]:
        routes = SUBWAY_ROUTES
        st.caption("현충원역(11·102·104·113·212번)·월드컵경기장역(117번) 등 지하철역을 지나는 6개 노선")
    else:
        routes = st.multiselect("노선", ALL_ROUTES, default=pre or [102], format_func=lambda r: f"{r}번",
                                placeholder="노선을 골라 주세요")
        if not routes:
            html("<div class='n13-card n13-sm'>노선을 하나 이상 골라 주세요.</div>")
            footer()
            return
    live_section(routes, demo, dq)
    feedback_section(routes, demo, dq)
    footer()


try:
    main()
except Exception as e:
    if type(e).__module__.startswith("streamlit"):  # Streamlit 내부 제어(다시 실행 등)는 그대로 넘김
        raise
    st.error("일시적인 오류가 생겼어요. 잠시 후 새로고침해 주세요.")  # 자세한 내용은 화면에 보이지 않음
