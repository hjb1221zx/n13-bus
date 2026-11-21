"""N13 하교 버스 — 지금 어떻게 움직일까? (Streamlit)

실행(로컬): 프로젝트 폴더에서  python -m streamlit run web/app.py
비밀 값(화면·로그에 출력하지 않음)
  DAEJEON_BUS_KEY   : 배포 비밀 설정(Secrets) → 환경변수 → 상위 폴더 .env 순서로 읽음
  FEEDBACK_ENDPOINT : 피드백 저장용 Apps Script 웹 앱 주소. Secrets 또는 환경변수에서만 읽음(코드에 쓰지 않음)
예측 방법 (analysis/REPORT.md)
  버스 1대 예상 인원 = 그 시간대 1분당 탑승률(부분 풀링, 9~10월 교통카드) × 같은 노선 앞차 간격(실시간, 없으면 시간표)
  시간대·몰림 주의는 '버스가 N13에 도착하는 시각' 기준. 다른 노선 직전 도착(환승 비율)은 웹에서 쓰지 않음
  탑승 가능성 = N13 출발 인원(도착 + N13 대기 − N13 하차)을 28/40/55명 기준에 넣은 4단계
  못 탈 확률 범위 = 화면 표시용으로 정한 구간 (REPORT '웹에서의 계산 결정')
지원 시간: 분석 자료가 평일 09~21시(21시대 포함)라서 그 밖에는 예측 없이 실시간 도착만 보여줌
예정/실시간: 시간표 출발 + 출발점→N13 이동 시간으로 '예정'을 만들고, 실시간에 잡히면 '실시간'으로 바꿈(같은 버스 중복 표시 없음)
API 호출 줄이기: 같은 정류장 도착정보는 45초 동안 저장해 재사용(실패도 45초 저장), N13은 백그라운드에서 60초마다 1번만 조회
예시 모드: 주소 뒤에 ?demo=16:40&day=월  → 시간표로 만든 가상 도착(발표·캡처용, '예시' 표시)
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
CONG = {1: "앉을 수 있음", 2: "서서 감", 3: "혼잡", 4: "매우 혼잡(만차)"}
BOARD = {1: "높음", 2: "다소 높음", 3: "다소 낮음", 4: "낮음"}
BOARD_TEXT = {"높음": "여유 있게 탈 수 있어요", "다소 높음": "서서 갈 수 있어요",
              "다소 낮음": "혼잡해요. 못 탈 수도 있어요", "낮음": "매우 혼잡해요. 못 탈 가능성이 높아요"}
PROB = {"높음": "10% 미만", "다소 높음": "10~20%", "다소 낮음": "20~40%", "낮음": "40% 이상"}  # 화면 표시용 구간(추정)
STAGE_COLOR = {"높음": "#2f6db5", "다소 높음": "#5b8a3a", "다소 낮음": "#d4602a", "낮음": "#8f2410"}

# 노선 색 (docs/route_colors.md)
#  색 규칙: 대전시 보도자료(2008-12-29 '12월 30일부터 시내버스 노선이 확 바뀐다') "급행 빨강, 간선 파랑, 지선과 외곽 녹색"
#  11번  = 외곽: 공식 시간표(2026.11.1) 구분 '외곽', 노선정보 API ROUTE_TP 4 → 녹색
#  117·212번 = 녹색: 사용자 관찰(실제 차량). 공식 자료로 간선/지선 구분은 확인 안 됨(시간표 '도시'/빈칸, API ROUTE_TP 2는 간선·지선 묶음)
#  102·104·107·113·48번 = 공식 자료로 확인 안 됨 → 회색(중립)
GREEN, UNKNOWN = "#2e8b3e", "#6b7280"
ROUTE_COLOR = {11: GREEN, 117: GREEN, 212: GREEN}

N13, GATE, SUTONG, DEOKMYEONG = "41730", "41690", "41670", "41400"
HY_ROUTES = [11, 102, 104, 113, 212]          # 현충원역 방면
ALL_ROUTES = [11, 102, 104, 113, 117, 212]
WALK = {"정문": 6.8, "수통골삼거리": 11.1, "덕명네거리": 11.5}  # data/walk_times.csv, analysis/alt_nearby_stops.csv (추정)
CACHE_SEC = 45
FB_STOPS = {"N13"}


# ---------------- 데이터 ----------------
@st.cache_data
def load_tables():
    P = pd.read_csv(HERE / "data" / "prediction_table.csv").set_index(["노선", "요일", "시간대"])
    S = pd.read_csv(HERE / "data" / "schedule_n13_days.csv")
    tp = HERE / "data" / "tashu_near.csv"
    T = pd.read_csv(tp) if tp.exists() else pd.DataFrame()
    return P, S, T


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
    """예외를 화면에 보일 때: 종류 이름만, 혹시 키·주소가 섞이면 가림"""
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


@st.cache_data(ttl=CACHE_SEC, show_spinner=False)
def arrivals(ars):
    """45초 저장. 실패도 저장해서, API가 멈췄을 때 접속자마다 다시 부르지 않음"""
    try:
        return _call_arrivals(ars), ""
    except Exception as e:
        return [], safe_msg(e)


class Tracker:
    """N13 도착정보를 60초마다 조회해서, 노선별로 '앞차가 N13을 지나간 시각'을 기록 (track_buses.py와 같은 규칙:
    남은 정류장 1로 보이던 차가 다음 조회에서 사라지면 통과, 기점 대기(MSG_TP 07)는 제외)"""

    def __init__(self):
        self.lock = threading.Lock()
        self.snapshot, self.snap_time, self.last_pass, self.prev = None, 0.0, {}, {}
        threading.Thread(target=self.loop, daemon=True).start()

    def loop(self):
        while True:
            try:
                rows = _call_arrivals(N13)
                now = dt.datetime.now(KST)
                cur = {(r["노선"], r["차량"]): r for r in rows if r["MSG_TP"] != "07"}
                with self.lock:
                    for (rt, car), r in self.prev.items():
                        if r["남은정류장"] == "1" and (rt, car) not in cur:
                            self.last_pass[rt] = now
                    self.prev, self.snapshot, self.snap_time = cur, rows, time.time()
            except Exception:
                pass  # 로그에 아무것도 남기지 않음(키가 섞일 일 없음)
            time.sleep(60)


@st.cache_resource
def tracker():
    return Tracker()


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


def fb_payload(b):
    return {"노선": int(b["노선"]), "정류장": "N13", "도착예정시각": b["도착시각"],
            "혼잡도": CONG[b["보통_혼잡"]], "탑승가능성": b["보통_탑승"]}


def on_feedback(bid, q, b):
    ss = st.session_state
    key = f"fb_{bid}_{q}"
    val = ss.get(key)
    done = ss.setdefault("fb_done", set())
    if val not in ("예", "아니요") or (bid, q) in done:
        return
    p = fb_payload(b)
    p["혼잡했나요"] = val if q == "혼잡" else ""
    p["탈수있었나요"] = val if q == "탑승" else ""
    ans = ss.setdefault("fb_ans", {})
    if ss.get("demo_mode"):          # 예시 화면: 저장하지 않고 눌린 것으로만 표시
        done.add((bid, q))
        ans[(bid, q)] = val
    elif send_feedback(p):
        done.add((bid, q))
        ans[(bid, q)] = val
    else:
        ss["fb_broken"] = True
        ss[key] = None


def feedback_box(bid, b):
    ss = st.session_state
    if not (feedback_endpoint() or ss.get("demo_mode")) or ss.get("fb_broken"):
        return
    done = ss.setdefault("fb_done", set())
    with st.container(horizontal=True, gap="large"):   # 휴대폰에서도 두 질문을 한 줄에
        st.segmented_control("이 버스 혼잡했나요?", ["예", "아니요"], key=f"fb_{bid}_혼잡",
                             disabled=(bid, "혼잡") in done, on_change=on_feedback, args=(bid, "혼잡", b))
        st.segmented_control("탈 수 있었나요?", ["예", "아니요"], key=f"fb_{bid}_탑승",
                             disabled=(bid, "탑승") in done, on_change=on_feedback, args=(bid, "탑승", b))
    if (bid, "혼잡") in done or (bid, "탑승") in done:
        ans = ss.get("fb_ans", {})
        got = " · ".join(f"{lab}: {ans[(bid, q)]}" for q, lab in [("혼잡", "혼잡했나요"), ("탑승", "탈 수 있었나요")] if (bid, q) in ans)
        st.caption(("예시 화면이라 저장하지 않았어요" if ss.get("demo_mode") else "고마워요! 저장됐어요") + f" ({got})")


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
    res = {"노선": route, "도착분": eta, "도착시각": t_arr.strftime("%H:%M"), "예측": False}
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


def planned_buses(S, routes, now, live, per_route):
    """시간표 예정: 같은 노선 실시간 버스가 있으면 그 버스(+여유) 이후 예정만 → 같은 버스가 두 번 안 보임"""
    m = now.hour * 60 + now.minute
    out = []
    for rt in routes:
        s = S[(S["노선"] == rt) & (S["N13예정분"] >= m) & (S["N13예정분"] <= m + 60)].sort_values("N13예정분")
        etas = [b["도착분"] for b in live if b["노선"] == rt]
        if etas:
            last = m + max(etas)
            hw = sched_headway(S, rt, now + dt.timedelta(minutes=max(etas))) or 10
            s = s[s["N13예정분"] > last + max(3, hw / 2)]
        for _, x in s.head(per_route).iterrows():
            out.append({"노선": rt, "도착분": int(x["N13예정분"] - m), "예정시각": x["예정시각"]})
    return out


# ---------------- 화면 ----------------
def route_pill(rt):
    return (f"<span style='background:{ROUTE_COLOR.get(rt, UNKNOWN)};color:#fff;border-radius:6px;"
            f"padding:1px 8px;font-weight:700;white-space:nowrap'>{rt}번</span>")


def source_badge(kind):
    if kind == "실시간":
        return "<span style='background:#e7f3ea;color:#1d6b2f;border:1px solid #1d6b2f;border-radius:10px;padding:0 7px;font-size:0.78rem'>● 실시간</span>"
    return "<span style='background:#fff;color:#555;border:1px dashed #888;border-radius:10px;padding:0 7px;font-size:0.78rem'>○ 예정(시간표)</span>"


def card(b, demo=False):
    when = "곧 도착" if b["도착분"] <= 1 else f"{b['도착분']}분 후"
    head = (f"<div style='font-size:1.1rem'>{route_pill(b['노선'])} <b>{when}</b> "
            f"<span style='color:#666;font-size:0.85rem'>({b['도착시각']})</span> {source_badge(b['종류'])}</div>")
    if not b["예측"]:
        body = "<div style='color:#666;font-size:0.9rem'>지원 시간(09~21시) 밖이라 예측하지 않아요</div>"
        c = "#bbb"
    else:
        lv = b["보통_탑승"]
        c = STAGE_COLOR[lv]
        warn = (f"<div style='color:#8f2410;font-size:0.85rem'>⚠ 몰림 주의 {b['몰림주의']} "
                f"(N13 쪽 수업이 많이 끝나는 시간대 규칙)</div>") if b["몰림주의"] else ""
        note = "시간표 기준 예정이라 실제 도착은 달라질 수 있어요 · " if b["종류"] == "예정" else ""
        body = (f"<div style='margin-top:2px'><b style='color:{c}'>{BOARD_TEXT[lv]}</b></div>"
                f"<div style='font-size:0.9rem'>탑승 가능성 <b>{lv}</b> (못 탈 확률 {PROB[lv]}, 추정) · "
                f"{CONG[b['보통_혼잡']]} · 약 {b['보통_도착']:.0f}명</div>"
                f"<div style='color:#555;font-size:0.85rem'>붐비는 날이면: {b['붐빔_탑승']} ({PROB[b['붐빔_탑승']]}) · "
                f"{CONG[b['붐빔_혼잡']]} · 약 {b['붐빔_도착']:.0f}명</div>"
                f"<div style='color:#888;font-size:0.78rem'>{note}앞차 간격 {b['앞차간격']:.0f}분({b['간격출처']})"
                f"{' · 예시' if demo else ''} · 인원은 추정</div>{warn}")
    st.markdown(f"<div style='border-left:6px solid {c};padding:6px 10px;background:#f6f7f9;color:#1f1f1f;"
                f"border-radius:6px'>{head}{body}</div>", unsafe_allow_html=True)


def demo_arrivals(S, now, routes, ars_offset=0):
    """예시 모드: 시간표 N13 도착 예정으로 가상 도착 목록 (정류장별 차이는 ars_offset분)"""
    m = now.hour * 60 + now.minute
    out = []
    for rt in routes:
        s = S[(S["노선"] == rt) & (S["N13예정분"] + ars_offset >= m) & (S["N13예정분"] + ars_offset <= m + 60)].sort_values("N13예정분").head(3)
        for v in s["N13예정분"]:
            out.append({"노선": rt, "차량": f"예시{rt}-{v}", "도착분": int(v + ars_offset - m), "남은정류장": "", "MSG_TP": ""})
    return out


def tashu_line(T):
    """타슈: 근처 대여소가 있을 때만 (data/tashu_near.csv). 실시간 대수 API는 아직 동작 안 함 → '준비 중'"""
    if T.empty or not {"N13", "현충원역"} <= set(T["쪽"]):
        return None
    a = T[T["쪽"] == "N13"].sort_values("걷는거리_m").iloc[0]
    b = T[T["쪽"] == "현충원역"].sort_values("걷는거리_m").iloc[0]
    ride = T["자전거_대여소간_분"].iloc[0] if "자전거_대여소간_분" in T else None
    if ride != ride or ride is None:
        return None
    total = a["걷는시간_분"] + ride
    name_a = a["대여소명"].split(" ", 1)[-1]
    name_b = b["대여소명"].split(" ", 1)[-1]
    return total, (f"- **현충원역까지 타슈** (약 {total:.0f}분): {name_a} 대여소까지 걸어서 약 {a['걷는시간_분']:.0f}분 → "
                   f"자전거 약 {ride:.0f}분 → {name_b} 대여소 (대여·반납 시간 제외, 추정) · 실시간 대수는 준비 중")


def main():
    st.set_page_config(page_title="N13 하교 버스", page_icon="🚌", layout="centered")
    st.markdown("<style>.block-container{padding-top:1.2rem;max-width:640px}</style>", unsafe_allow_html=True)
    P, S_all, T = load_tables()
    qp = st.query_params
    demo = "demo" in qp
    now = dt.datetime.now(KST).replace(second=0, microsecond=0)
    if demo:
        try:
            hh, mm = map(int, qp.get("demo", "16:40").split(":"))
            now = now.replace(hour=hh, minute=mm)
        except ValueError:
            pass
    dq = qp.get("day") if demo and qp.get("day") in list(DAYS) else None
    day, sched_kind, weekend = day_info(now, dq)
    S = S_all[S_all["일정"] == sched_kind]
    in_service = now.hour in SERVICE_HOURS

    st.markdown("### 🚌 N13 하교 버스")
    st.caption("출발: 삼성화재연수원 정류장(41730) · 하교 방향")
    shown_day = dq or DAYS[now.weekday()]
    st.caption(f"기준 시각 {now:%H:%M} ({shown_day}요일)" + (" · **예시 화면: 시간표로 만든 가상 도착**" if demo else ""))
    if weekend and in_service:
        st.warning("**주말은 평일보다 승객이 적어요.** 주말 자료가 없어 금요일 기준으로 예측하니 참고만 하세요.", icon="📅")

    utype = st.radio("어떻게 가요?", ["지하철 환승 (현충원역 방면 아무 버스)", "특정 노선"], horizontal=True)
    special = utype.startswith("특정")
    routes = [st.selectbox("노선", ALL_ROUTES, index=1)] if special else HY_ROUTES

    # 실시간 도착 (N13)
    err, last_pass = "", {}
    if demo:
        raw = list({r["노선"]: r for r in sorted(demo_arrivals(S, now, routes), key=lambda r: -r["도착분"])}.values())  # 실제 API처럼 노선마다 가장 가까운 1대
    else:
        tr = tracker()
        with tr.lock:
            snap, age, last_pass = tr.snapshot, time.time() - tr.snap_time, dict(tr.last_pass)
        if snap is not None and age < 90:
            raw = snap
        else:
            raw, err = arrivals(N13)
    raw = [r for r in raw if r["노선"] in routes and r["MSG_TP"] != "07"]

    if not in_service:
        st.info("**이 서비스는 평일 09~21시만 지원해요.** 지금은 예측 대신 실시간 도착 시간만 참고로 보여드려요.", icon="🕘")
        st.markdown("#### N13 실시간 도착 (참고)")
        if err:
            st.write("실시간 도착정보를 불러오지 못했어요.")
        elif not raw:
            st.write("지금 실시간으로 잡히는 버스가 없어요.")
        for r in sorted(raw, key=lambda r: r["도착분"]):
            t = (now + dt.timedelta(minutes=r["도착분"])).strftime("%H:%M")
            st.markdown(f"{route_pill(r['노선'])} {r['도착분']}분 후 ({t}) {source_badge('실시간')}", unsafe_allow_html=True)
        footer()
        return

    live = []
    for r in raw:
        b = predict_bus(P, S, r["노선"], r["도착분"], now, day, last_pass.get(r["노선"]))
        b.update({"종류": "실시간", "id": f"{r['노선']}_{r['차량'] or r['도착분']}"})
        live.append(b)
    plan = []
    for x in planned_buses(S, routes, now, live, per_route=3 if special else 1):
        b = predict_bus(P, S, x["노선"], x["도착분"], now, day)
        b.update({"종류": "예정", "id": f"{x['노선']}_예정{x['예정시각']}"})
        plan.append(b)
    buses = sorted(live + plan, key=lambda b: b["도착분"])
    pred = [b for b in buses if b["예측"]]

    # 이동 방법 비교
    ok = [b for b in pred if b["보통_탑승"] in ("높음", "다소 높음")]
    best = min(ok, key=lambda b: b["도착분"]) if ok else None
    alt = {}
    for name, ars, walk, rts in [("정문", GATE, WALK["정문"], routes),
                                 ("수통골삼거리", SUTONG, WALK["수통골삼거리"], [x for x in routes if x in (11, 102, 104)]),
                                 ("덕명네거리", DEOKMYEONG, WALK["덕명네거리"], [] if special else [48, 107])]:
        if not rts:
            continue
        if demo:
            off = {"정문": -1, "수통골삼거리": -3}.get(name)
            if off is None:
                alt[name] = "예시"
                continue
            rows, e2 = demo_arrivals(S, now, rts, off), ""
        else:
            rows, e2 = arrivals(ars)
        if e2:
            alt[name] = "오류"
            continue
        cand = sorted([r for r in rows if r["노선"] in rts and r["도착분"] >= walk], key=lambda r: r["도착분"])
        alt[name] = cand[0] if cand else None
    tashu = tashu_line(T) if not special or routes[0] in HY_ROUTES else None

    # 한 문장 추천
    def tag(b):
        return " (시간표 예정)" if b["종류"] == "예정" else ""
    if err and not pred:
        msg = "실시간 도착정보를 불러오지 못했어요. 아래는 과거 통계(9~10월) 기반 예측이에요."
    else:
        walk_opts = []
        if isinstance(alt.get("수통골삼거리"), dict):
            a = alt["수통골삼거리"]
            walk_opts.append((a["도착분"], f"**수통골삼거리까지 약 11분** 걸으면 {a['도착분']}분 뒤 {route_pill(a['노선'])}을 정문 전에 비교적 여유 있게 탈 수 있어요(역주행)."))
        if isinstance(alt.get("덕명네거리"), dict):
            a = alt["덕명네거리"]
            walk_opts.append((a["도착분"], f"**덕명네거리까지 약 12분** 걸으면 {a['도착분']}분 뒤 {route_pill(a['노선'])}(현충원역 방면)을 탈 수 있어요."))
        walk_best = min(walk_opts, key=lambda x: x[0]) if walk_opts else None
        crowded_near = [b for b in pred if b["보통_탑승"] in ("다소 낮음", "낮음") and (not best or b["도착분"] < best["도착분"])]
        if best and (walk_best is None or best["도착분"] <= walk_best[0] + 3):
            how = "여유 있게 탈 수 있는" if best["보통_탑승"] == "높음" else "서서 갈 수 있는"
            msg = f"지금은 **N13에서 {best['도착분']}분** 기다리면 {how} {route_pill(best['노선'])}이 와요{tag(best)}."
            if crowded_near:
                msg += f" (그 전에 오는 {crowded_near[0]['노선']}번은 혼잡할 것 같아요)"
        elif walk_best:
            lead = (f"N13에서 탈 만한 버스는 {best['도착분']}분 뒤({best['노선']}번)라, " if best
                    else "N13에 오는 버스가 혼잡할 것 같아요. ")
            msg = lead + walk_best[1]
        elif pred and tashu:
            msg = f"가까운 버스가 혼잡할 것 같아요. 급하면 **현충원역까지 타슈(약 {tashu[0]:.0f}분)**도 있어요."
        elif pred:
            msg = "가까운 버스가 혼잡할 것 같아요. 아래 다른 방법도 확인해 보세요."
        else:
            msg = "지금 N13에 오는 버스 정보가 없어요. 아래 과거 통계 예측과 대체경로를 참고하세요."
    msg = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", msg)  # HTML 안에서는 ** 대신 <b>
    st.markdown(f"<div style='background:#eaf2fb;color:#1f1f1f;border-radius:8px;padding:10px 12px;margin:6px 0'>{msg}</div>",
                unsafe_allow_html=True)

    # 버스 목록
    if not special and pred:
        fast = min([b for b in pred if b["보통_탑승"] != "낮음"] or pred, key=lambda b: b["도착분"])
        roomy = min([b for b in pred if b["도착분"] <= 30] or pred, key=lambda b: (b["보통_도착"], b["도착분"]))
        st.markdown(f"**가장 빨리 탈 수 있는 버스:** {fast['노선']}번 {fast['도착분']}분 후{tag(fast)} · "
                    f"**가장 여유 있는 버스:** {roomy['노선']}번 {roomy['도착분']}분 후 (약 {roomy['보통_도착']:.0f}명){tag(roomy)}")
    c1, c2 = st.columns([3, 1])
    c1.markdown("#### N13에 오는 버스")
    c2.button("새로고침", use_container_width=True)
    st.caption("● 실시간 = 지금 도착정보에 잡힌 버스 · ○ 예정 = 시간표 출발 + 이동 시간으로 계산(아직 출발 전)")

    st.session_state["demo_mode"] = demo
    fb_on = bool(feedback_endpoint()) or demo
    if fb_on and st.session_state.get("fb_broken"):
        st.caption("피드백 저장이 잠시 안 돼요. 나중에 다시 시도해 주세요.")
    elif fb_on:
        st.caption("버스마다 아래 버튼으로 알려주시면 예측이 맞았는지 확인하는 데 쓰여요.")
    else:
        st.caption("피드백 저장은 준비 중이에요.")
    seen = st.session_state.setdefault("seen", {})
    if buses:
        for b in buses:
            with st.container(border=True):
                card(b, demo)
                if fb_on and b["예측"]:
                    feedback_box(b["id"], b)
            if b["예측"]:
                seen[b["id"]] = {**b, "본시각": time.time()}
    else:
        st.write("지금 실시간으로 잡히는 버스도, 1시간 안 시간표 예정도 없어요." if not err else "실시간 정보 없음")

    # 방금 지나간 버스(목록에서 사라진 버스)에도 답할 수 있게
    if fb_on and not st.session_state.get("fb_broken"):
        gone = [v for k, v in seen.items() if k not in {b["id"] for b in buses} and time.time() - v["본시각"] < 30 * 60]
        if gone:
            with st.expander(f"방금 지나간 버스 알려주기 ({len(gone)}대)"):
                for v in sorted(gone, key=lambda v: v["도착시각"]):
                    st.markdown(f"{route_pill(v['노선'])} {v['도착시각']} · 탑승 가능성 {v['보통_탑승']}", unsafe_allow_html=True)
                    feedback_box(v["id"], v)

    # 버스가 없을 때: 과거 통계
    if not pred:
        h = now.hour
        rows = [(rt, P.loc[(rt, day, h)]) for rt in routes if (rt, day, h) in P.index]
        if rows:
            st.markdown(f"**과거 통계({day}요일 {h}시, 9~10월 평균)**")
            for rt, r in rows:
                st.write(f"{rt}번: 보통 날 {r['보통_혼잡도']}·탑승 가능성 {r['보통_탑승가능성']} / 붐비는 날 {r['붐빔_혼잡도']}·{r['붐빔_탑승가능성']}")

    # 대체경로
    st.markdown("#### 다른 방법")
    def line(name, walk, a, extra=""):
        if a == "예시":
            return f"- **{name}** (걸어서 약 {walk:.0f}분): 예시 화면에서는 실시간 도착을 보여주지 않아요"
        if a == "오류":
            return f"- **{name}** (걸어서 약 {walk:.0f}분): 실시간 정보를 불러오지 못했어요"
        if a is None:
            return f"- **{name}** (걸어서 약 {walk:.0f}분): 도착해서 탈 수 있는 버스가 아직 안 잡혀요"
        return f"- **{name}** (걸어서 약 {walk:.0f}분): {route_pill(a['노선'])} {a['도착분']}분 후 도착{extra}"
    if "정문" in alt:
        st.markdown(line("정문으로 이동", WALK["정문"], alt["정문"], " · 버스는 덜 찬 채 오지만 정문에서 타려는 사람이 많아요"), unsafe_allow_html=True)
    if "수통골삼거리" in alt:
        st.markdown(line("역주행: 수통골삼거리", WALK["수통골삼거리"], alt["수통골삼거리"], " · 정문 전이라 비교적 여유(16시 102번 약 13명, 추정)"), unsafe_allow_html=True)
    if "덕명네거리" in alt:
        st.markdown(line("덕명네거리 48·107번", WALK["덕명네거리"], alt["덕명네거리"], " · 현충원역 방면, 혼잡 예측 없음"), unsafe_allow_html=True)
    if tashu:
        st.markdown(tashu[1])
    footer()


def footer():
    st.markdown("---")
    st.markdown(
        "<div style='color:#777;font-size:0.75rem;line-height:1.55'>"
        "· 예측은 추정이며, 2026년 9~10월 평일 09~21시 1시간 단위 교통카드 자료(대전교통 빅데이터 플랫폼 tportal)로 만들었어요.<br>"
        "· '앞차 간격이 길면 그만큼 붐빈다'는 원리를 실제 데이터로 검증하지는 못했어요.<br>"
        "· 버스 정원(만차선 55명)은 제조사 사양 기준 추정이에요. 못 탈 확률 구간은 화면 표시용으로 정한 추정값이에요.<br>"
        "· 몰림 주의는 N13 쪽 건물에서 끝나는 수업이 30개 이상인 시간대를 표시한 규칙이에요.<br>"
        "· 노선 번호 색: 녹색은 확인된 노선(11번 외곽, 117·212번), 회색은 공식 자료로 확인 못 한 노선이에요.<br>"
        "· 출처: 공공데이터포털(data.go.kr) 대전광역시 버스 도착정보·노선정보 API(도착정보는 45초마다 갱신), "
        "대전교통정보센터 시내버스 시간표(2026.11.1.), 대전광역시 공영자전거(타슈) 위치 현황, OpenStreetMap 기여자(ODbL).</div>",
        unsafe_allow_html=True)


try:
    main()
except Exception as e:
    if type(e).__module__.startswith("streamlit"):  # Streamlit 내부 제어(다시 실행 등)는 그대로 넘김
        raise
    st.error("일시적인 오류가 생겼어요. 잠시 후 새로고침해 주세요.")  # 자세한 내용은 화면에 보이지 않음
