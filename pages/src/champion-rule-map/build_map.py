#!/usr/bin/env python3
"""Builds the static BB(6) Champion Rule Map page. All tape data comes from frames_out.json,
which frames.js extracted from a step-by-step simulation of the real machine."""
import json, math, html, sys, os

S = os.path.dirname(os.path.abspath(__file__))
FR = json.load(open(os.path.join(S, "frames_out.json")))
def frame(step):
    for r in FR:
        for f in r["out"]:
            if f["step"] == step:
                return f
    raise KeyError(step)

EXPLORER = "champion-explorer.html"
WIKI = "https://wiki.bbchallenge.org/wiki/1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE"
esc = html.escape

# ---------------------------------------------------------------- rule table
RULES = {  # state: [(read0 text, chips), (read1 text, chips)]
    "A": [("1RB", ["fill", "append"]), ("1RA", ["run"])],
    "B": [("1RC", ["fill", "append"]), ("1RZ", ["halt"])],
    "C": [("1LD", ["crawl", "append"]), ("0RF", ["recode"])],
    "D": [("1RA", ["fill"]), ("0LE", ["crawl"])],
    "E": [("0LD", ["fill"]), ("1RC", ["crawl", "recode"])],
    "F": [("1RA", ["recode"]), ("0RE", ["recode"])],
}
NAMES = {"crawl": "Crawl left", "run": "Run right", "recode": "Recode right", "fill": "Fill", "append": "Append", "halt": "Halt", "fixed": "Fixed sequence"}
SHORT = {"crawl": "crawl", "run": "run", "recode": "recode", "fill": "fill", "append": "append", "halt": "halt", "fixed": "fixed"}

def chip(k, label=None):
    return f'<span class="chip {k}"><span class="sw {k}"></span>{esc(label or SHORT[k])}</span>'

def rule_cell(state, sym, txt, chips):
    w, d, n = txt[0], txt[1], txt[2]
    arrow = "→" if d == "R" else "←"
    if n == "Z":
        body = f'write <b>{w}</b>, {arrow}, <b class="haltw">halt</b>'
    else:
        body = f'write <b>{w}</b>, {arrow}, <b>{n}</b>'
    extra = ' <span class="note">hand-off</span>' if (state, sym) == ("F", 0) else ""
    return f'<td><div class="rt"><span class="mono">{body}</span><span class="chips">{"".join(chip(c) for c in chips)}{extra}</span></div></td>'

def rule_table():
    rows = []
    for st, pair in RULES.items():
        cells = "".join(rule_cell(st, y, *pair[y]) for y in (0, 1))
        rows.append(f'<tr><th scope="row">{st}</th>{cells}</tr>')
    return ('<table class="rules"><thead><tr><th scope="col">State</th><th scope="col">Reads 0</th><th scope="col">Reads 1</th></tr></thead>'
            f'<tbody>{"".join(rows)}</tbody></table>')

# ---------------------------------------------------------------- tape cells
def cells_html(cells, head=None, groups=None, labels=None, kind=None, zeros=False):
    groups = groups or [len(cells)]
    out, i = [], 0
    for gi, g in enumerate(groups):
        cs = []
        for j in range(g):
            c = cells[i]
            cls = "c"
            if zeros and c == "0": cls += " z"
            if head is not None and i == head: cls += f" h {kind or 'fixed'}"
            cs.append(f'<span class="{cls}">{c}</span>')
            i += 1
        lab = f'<span class="gl">{esc(labels[gi])}</span>' if labels and labels[gi] else ""
        out.append(f'<span class="g"><span class="gc">{"".join(cs)}</span>{lab}</span>')
    return f'<span class="tape">{"".join(out)}</span>'

def rule_words(rule):
    # "D1 0LE" -> "D reads 1: write 0, move left, go to E"
    k, t = rule.split()
    s, r = k[0], k[1]
    w, d, n = t[0], t[1], t[2]
    mv = "right" if d == "R" else "left"
    if n == "Z":
        return f"{s} reads {r}: halt"
    return f"{s} reads {r}: write {w}, move {mv}, go to {n}"

def frame_rows(spec):
    rows = []
    for item in spec:
        if item[0] == "h":
            _, kind, title, text = item
            rows.append(f'<div class="fh">{chip(kind, title)}<span>{esc(text)}</span></div>')
            continue
        if item[0] == "labels":
            _, groups, labels = item
            n = sum(groups)
            ghost = cells_html("0" * n, None, groups, labels).replace('class="c"', 'class="c ghost"')
            rows.append(f'<div class="fr lr" aria-hidden="true"><span></span><span class="tw">{ghost}</span></div>')
            continue
        step, kind, groups, labels = item
        f = frame(step)
        rows.append(
            f'<div class="fr"><span class="st {kind}">{f["state"]}</span>'
            f'<span class="tw">{cells_html(f["cells"], f["head"], groups, labels, kind)}</span>'
            f'<span class="fw"><span class="mono">step {step:,}</span> <span>{esc(rule_words(f["rule"]))}</span></span></div>')
    return f'<div class="frames">{"".join(rows)}</div>'

# ---------------------------------------------------------------- route diagrams
W = 720
SLOPE = {"crawl": 0.6, "run": 0.2, "recode": 0.2}
FIX_H = 12

BEFORE = [
    ("blank", 16, 40, "", ""),
    ("r", 40, 88, "header", "111011"),
    ("r", 88, 208, "countdown", "3-cell digits"),
    ("r", 208, 262, "marker", "+ phase"),
    ("r", 262, 452, "middle counter", "3-cell digits"),
    ("r", 452, 500, "marker", "0 11100"),
    ("r", 500, 640, "pile", "111 groups"),
    ("blank", 640, 704, "", ""),
]

def band(regions, y, tag):
    parts = [f'<text class="sv-tag" x="16" y="{y - 6}">{tag}</text>']
    for kind, a, b, name, detail in regions:
        if kind == "blank":
            parts.append(f'<rect class="sv-blank" x="{a + 1}" y="{y}" width="{b - a - 2}" height="34" rx="3"/>')
            continue
        parts.append(f'<rect class="sv-reg" x="{a + 1}" y="{y}" width="{b - a - 2}" height="34" rx="3"/>')
        cx = (a + b) / 2
        parts.append(f'<text class="sv-name" x="{cx}" y="{y + 15}" text-anchor="middle">{esc(name)}</text>')
        if detail:
            parts.append(f'<text class="sv-detail" x="{cx}" y="{y + 28}" text-anchor="middle">{esc(detail)}</text>')
    return "".join(parts)

def zigzag(x1, y1, x2, y2, step=7.0, amp=3.2):
    L = math.hypot(x2 - x1, y2 - y1)
    n = max(2, int(L // step))
    ux, uy = (x2 - x1) / L, (y2 - y1) / L
    nx, ny = -uy, ux
    pts = [(x1, y1)]
    for i in range(1, n):
        t = i / n
        o = amp if i % 2 else -amp
        pts.append((x1 + (x2 - x1) * t + nx * o, y1 + (y2 - y1) * t + ny * o))
    pts.append((x2, y2))
    return " ".join(f"{px:.1f},{py:.1f}" for px, py in pts)

def ticks(x1, y1, x2, y2, step=9.0, half=3.2):
    L = math.hypot(x2 - x1, y2 - y1)
    ux, uy = (x2 - x1) / L, (y2 - y1) / L
    nx, ny = -uy, ux
    out = []
    d = step / 2
    while d < L:
        px, py = x1 + ux * d, y1 + uy * d
        out.append(f'<line class="sv-tick" x1="{px + nx * half:.1f}" y1="{py + ny * half:.1f}" x2="{px - nx * half:.1f}" y2="{py - ny * half:.1f}"/>')
        d += step
    return "".join(out)

BADGE_R = 10
COLLIDE = []  # (diagram, badge, clearance) for the build-time geometry check

def badge(x, y, n):
    return (f'<circle class="sv-badge" cx="{x:.1f}" cy="{y:.1f}" r="{BADGE_R}"/>'
            f'<text class="sv-num" x="{x:.1f}" y="{y + 3.9:.1f}" text-anchor="middle">{n}</text>')

def seg_dist(px, py, ax, ay, bx, by):
    vx, vy = bx - ax, by - ay
    L2 = vx * vx + vy * vy or 1e-9
    t = max(0, min(1, ((px - ax) * vx + (py - ay) * vy) / L2))
    return math.hypot(px - (ax + t * vx), py - (ay + t * vy))

def box_dist(px, py, x1, y1, x2, y2):
    dx = max(x1 - px, 0, px - x2)
    dy = max(y1 - py, 0, py - y2)
    return math.hypot(dx, dy)

def route_svg(stages, after, end_label, aria, name):
    """stages: ('start', x) | (kind, xa, xb, n, (dx, dy)) for crawl/run/recode, offsets from the segment midpoint
    | ('fixed', a, b, enter, exit, n, (dx, dy)) offsets from the box centre | ('halt',)"""
    y0 = 96
    body, badges = [], []
    segs, boxes, bpos, labels = [], [], [], []
    x, y = None, y0
    for st in stages:
        k = st[0]
        if k == "start":
            x = st[1]
            body.append(f'<circle class="sv-start" cx="{x}" cy="{y}" r="4.5"/>')
            body.append(f'<text class="sv-lab" x="{x + 10}" y="{y + 4.5}">start</text>')
            labels.append((x + 8, y - 8, x + 46, y + 6))
            continue
        if k in SLOPE:
            _, xa, xb, n, off = st
            dy = abs(xb - xa) * SLOPE[k]
            y2 = y + dy
            if k == "crawl":
                body.append(f'<polyline class="sv-path crawl" points="{zigzag(xa, y, xb, y2)}"/>')
            else:
                body.append(f'<line class="sv-path {k}" x1="{xa}" y1="{y:.1f}" x2="{xb}" y2="{y2:.1f}"/>')
                if k == "recode":
                    body.append(ticks(xa, y, xb, y2))
            segs.append((xa, y, xb, y2, 4.0 if k != "run" else 1.5))
            mx, my = (xa + xb) / 2, (y + y2) / 2
            if isinstance(off[0], str):
                L = math.hypot(xb - xa, dy); ux, uy = (xb - xa) / L, dy / L
                cand = [(uy, -ux), (-uy, ux)]
                nx, ny = min(cand, key=lambda v: v[1]) if off[0] == "u" else max(cand, key=lambda v: v[1])
                off = (nx * off[1], ny * off[1])
            bpos.append((mx + off[0], my + off[1], n))
            x, y = xb, y2
            continue
        if k == "fixed":
            _, a, b, enter, exit_, n, off = st
            body.append(f'<rect class="sv-box {KINDS[name][n - 1]}" x="{a}" y="{y:.1f}" width="{b - a}" height="{FIX_H}" rx="3"/>')
            boxes.append((a, y, b, y + FIX_H))
            bpos.append(((a + b) / 2 + off[0], y + FIX_H / 2 + off[1], n))
            x, y = exit_, y + FIX_H
            continue
        if k == "halt":
            body.append(f'<rect class="sv-halt" x="{x - 5.5}" y="{y:.1f}" width="11" height="11"/>')
            body.append(f'<text class="sv-lab strong" x="{x + 11}" y="{y + 10:.1f}">halt</text>')
            boxes.append((x - 5.5, y, x + 5.5, y + 11))
            labels.append((x + 9, y - 1, x + 40, y + 12))
            y += 11
            continue
    if end_label:
        body.append(f'<circle class="sv-end" cx="{x}" cy="{y:.1f}" r="4.5"/>')
        body.append(f'<text class="sv-lab" x="{x - 10}" y="{y + 4.5:.1f}" text-anchor="end">{esc(end_label)}</text>')
        boxes.append((x - 4.5, y - 4.5, x + 4.5, y + 4.5))
        labels.append((x - 70, y - 8, x - 8, y + 6))
    for bx, by, n in bpos:
        badges.append(badge(bx, by, n))
    # geometry check: clearance between each badge and every other mark
    for i, (bx, by, n) in enumerate(bpos):
        c = 1e9
        for ax, ay, ex, ey, w in segs: c = min(c, seg_dist(bx, by, ax, ay, ex, ey) - w)
        for x1, y1, x2, y2 in boxes + labels: c = min(c, box_dist(bx, by, x1, y1, x2, y2))
        for j, (ox, oy, _) in enumerate(bpos):
            if j != i: c = min(c, math.hypot(bx - ox, by - oy) - BADGE_R)
        COLLIDE.append((name, n, round(c - BADGE_R, 1)))
    path_bottom = y + 18
    H = path_bottom + (64 if after else 8)
    guides = []
    for kind, a, b, *_ in BEFORE[1:]:
        guides.append(f'<line class="sv-guide" x1="{a}" y1="64" x2="{a}" y2="{path_bottom:.1f}"/>')
    guides.append(f'<line class="sv-guide" x1="640" y1="64" x2="640" y2="{path_bottom:.1f}"/>')
    parts = [band(BEFORE, 26, "before"), "".join(guides), "".join(body), "".join(badges)]
    if after:
        parts.append(band(after, path_bottom + 24, "after"))
    return (f'<svg class="route" viewBox="0 0 {W} {H:.0f}" role="img" aria-label="{esc(aria)}">'
            + "".join(parts) + "</svg>")

TICK = [("start", 452), ("crawl", 452, 392, 1, ("u", 19)), ("fixed", 380, 392, 392, 392, 2, (-22, 0)),
        ("recode", 392, 452, 3, (-6, 16)), ("fixed", 452, 500, 452, 500, 4, (0, -20)), ("run", 500, 640, 5, (6, -16)),
        ("fixed", 640, 658, 640, 658, 6, (27, 0)), ("crawl", 658, 452, 7, (22, 14))]
CONVERT = [("start", 452), ("crawl", 452, 262, 1, ("u", 19)), ("fixed", 208, 262, 262, 208, 2, (0, -20)),
           ("crawl", 208, 160, 3, (-20, -8)), ("fixed", 148, 160, 160, 160, 4, (-22, 0)),
           ("recode", 160, 244, 5, (-4, 19)), ("run", 244, 484, 6, (0, -16)), ("fixed", 484, 500, 484, 500, 7, (0, -20)),
           ("recode", 500, 640, 8, ("u", 19)), ("fixed", 616, 664, 640, 664, 9, (40, 0)), ("crawl", 664, 628, 10, (22, 10))]
RESET_HEAD = [("start", 452), ("crawl", 452, 262, 1, ("u", 19)), ("fixed", 208, 262, 262, 208, 2, (0, -20)),
              ("crawl", 208, 30, 3, ("u", 19)), ("fixed", 22, 58, 30, 58, 4, (0, 21)), ("recode", 58, 244, 5, ("u", 19)),
              ("fixed", 232, 244, 244, 244, 6, (-18, 16)), ("recode", 244, 484, 7, ("u", 19))]
RESET = RESET_HEAD + [("fixed", 478, 500, 484, 500, 8, (26, -10)), ("recode", 500, 640, 9, ("u", 19)),
                      ("fixed", 616, 664, 640, 664, 10, (40, 0)), ("crawl", 664, 628, 11, (22, 10))]
HALT = RESET_HEAD + [("fixed", 484, 500, 484, 500, 8, (24, -8)), ("halt",)]


A_TICK = [r if r[0] == "blank" else r for r in BEFORE]
A_TICK = [("blank", 16, 40, "", ""), ("r", 40, 88, "header", ""), ("r", 88, 208, "countdown", "same"),
          ("r", 208, 262, "marker", "same"), ("r", 262, 452, "middle counter", "one less"),
          ("r", 452, 500, "marker", "same"), ("r", 500, 652, "pile", "one group more"), ("blank", 652, 704, "", "")]
A_CONV = [("blank", 16, 40, "", ""), ("r", 40, 88, "header", ""), ("r", 88, 208, "countdown", "one less"),
          ("r", 208, 262, "marker", "phase − 1"), ("r", 262, 628, "middle counter", "old pile = 2ᵇ − 1 at the bottom"),
          ("r", 628, 676, "marker", "new"), ("r", 676, 704, "pile", "")]
A_RESET = [("blank", 4, 22, "", ""), ("r", 22, 70, "header", "shifted"), ("r", 70, 452, "countdown", "refilled: 1s, one 0-digit, 1s"),
           ("r", 452, 500, "marker", "+ phase 2"), ("r", 500, 628, "middle counter", "2ᵇ − 1"),
           ("r", 628, 676, "marker", "new"), ("r", 676, 704, "pile", "")]

def stage_li(kind, text, rules=None):
    r = f' <span class="mono rl">{esc(rules)}</span>' if rules else ""
    return f'<li>{chip(kind)}<span>{text}{r}</span></li>'

KINDS = {
    "tick": ["crawl", "fill", "recode", "fixed", "run", "append", "crawl"],
    "convert": ["crawl", "fixed", "crawl", "fill", "recode", "run", "fixed", "recode", "fixed", "crawl"],
    "reset": ["crawl", "fixed", "crawl", "fixed", "recode", "fill", "recode", "fill", "recode", "fixed", "crawl"],
    "halt": ["crawl", "fixed", "crawl", "fixed", "recode", "fill", "recode", "halt"],
}

SECTIONS = [
    dict(id="tick", name="Tick", when="Middle counter above 0", effect="Counter − 1, pile + 1.",
         cost="About 12 steps for every group in the pile, almost all of them in stages 5 and 7.",
         svg=route_svg(TICK, A_TICK, "next tick", name="tick", aria="Tick route: crawl left to the counter's lowest 1-digit, fill it, recode right, step over the marker, run right, append, crawl back."),
         stages=[
             ("crawl", "Crawl left over the counter's low 0-digits to its lowest 1-digit.", "D1 E1 C0 repeating"),
             ("fill", "Fill: that digit's 100 becomes 111, a 0.", "E0 D0 A0 B0"),
             ("recode", "Recode right: every lower 111 becomes 100, a 1. This is the borrow.", "C1 F1 E1 repeating"),
             ("fixed", "C reaches the right marker's first 0 and steps over the marker. F0 hands off to the run.", "C0 D1 E0 D0 A0 B0 C1 F0"),
             ("run", "Run right to the end of the pile.", "A1 repeating"),
             ("append", "Append one 111 group on the blank tape and turn around.", "A0 B0 C0"),
             ("crawl", "Crawl left over the whole pile and the marker back to the counter. Crossing the marker's 00 rebuilds it.", "D1 E1 C0 repeating; D1 E0 at the marker's 00"),
         ]),
    dict(id="convert", name="Convert", when="Middle counter 0, countdown above 0",
         effect="Countdown − 1 and the phase moves on. The pile's b units become b 1-digits at the bottom of the counter, so it holds 2ᵇ − 1, and the pile starts over.",
         cost="Mostly one recode pass over the pile at one step per cell. In the real run it is less than half as long as the tick before it.",
         svg=route_svg(CONVERT, A_CONV, "next tick", name="convert", aria="Convert route: crawl to the countdown, subtract one there, run right, recode the pile into 1-digits, build a new marker."),
         stages=[
             ("crawl", "Crawl left over the whole counter. Every digit is 111, so nothing stops it.", "D1 E1 C0 repeating"),
             ("fixed", "Cross the phase cells and the left marker. The marker is filled in for now.", "D1 E0 D1 E0 D0 A0 B0 C0"),
             ("crawl", "Crawl left over the countdown's low 0-digits.", "D1 E1 C0 repeating"),
             ("fill", "Fill the countdown's lowest 1-digit: countdown − 1.", "E0 D0 A0 B0"),
             ("recode", "Recode right: the lower countdown digits become 1s, and the same sweep writes 100 10 back as the left marker. F0 hands off.", "C1 F1 E1 repeating, then F0"),
             ("run", "Run right over the phase cells, the counter and the right marker's 111.", "A1 repeating"),
             ("fixed", "A reaches the right marker's first 0. A0 B0 fill the 00, so the marker joins the counter.", "A0 B0"),
             ("recode", "Recode right over the pile: each 111 group becomes a 1-digit.", "C1 F1 E1 repeating"),
             ("fixed", "Turn the spare group into a new right marker and write the first group of a new pile.", "C0 D1 E0 D0 A0 B0 C1 F0 A0 B0 C0"),
             ("crawl", "Crawl left to the counter's new right end.", "D1 E1 C0 repeating"),
         ]),
    dict(id="reset", name="Reset", when="Middle counter 0, countdown 0, phase 1",
         effect="The countdown takes over the old marker, phase cells and counter, and refills to nearly all 1-digits. The pile becomes the next counter, 2ᵇ − 1. The phase is 2 again.",
         cost="A crawl over everything left of the counter, then one recode pass to the end of the pile.",
         svg=route_svg(RESET, A_RESET, "next tick", name="reset", aria="Reset route: crawl all the way to the header, rebuild it, recode right through the countdown and the old counter, then recode the pile into the new counter."),
         stages=[
             ("crawl", "Crawl left over the counter.", "D1 E1 C0 repeating"),
             ("fixed", "Cross the left marker, as in a convert.", "D1 E0 D1 E0 D0 A0 B0 C0"),
             ("crawl", "Crawl over the whole countdown, which has no 1-digit, then past the header's 0 to the blank tape.", "D1 E1 C0 repeating; D1 E0 at the header's 0"),
             ("fixed", "Rebuild 111011 two cells further left.", "D1 E0 D0 A0 B0 C1 F1 E0 D0 A0 B0"),
             ("recode", "Recode right over the countdown: every digit becomes a 1.", "C1 F1 E1 repeating"),
             ("fill", "The sweep meets the 0 the crawl left after the old marker. C0 turns back and a fill sets the digit just written back to 0. This is the countdown's single 0-digit.", "C0 D1 E0 D0 A0 B0"),
             ("recode", "Recode right over the old phase cells and the whole counter. All of it becomes 1-digits of the countdown.", "C1 F1 E1 repeating"),
             ("fill", "E reaches the right marker's first 0 and fills the 00. The new left marker and two phase cells form here, where the old right marker was.", "E0 D0 A0 B0"),
             ("recode", "Recode right over the pile: it becomes the new counter.", "C1 F1 E1 repeating"),
             ("fixed", "Build a new right marker and the first group of a new pile, as in a convert.", "C0 D1 E0 D0 A0 B0 C1 F0 A0 B0 C0"),
             ("crawl", "Crawl left to the counter's right end.", "D1 E1 C0 repeating"),
         ]),
    dict(id="halt", name="Halt", when="Middle counter 0, countdown 0, phase 0",
         effect="The machine stops. Stages 1 to 7 are the same as a reset.",
         cost="",
         svg=route_svg(HALT, None, None, name="halt", aria="Halt route: the same as a reset until the recode reaches the right marker, where F, A and B take the halt rule."),
         stages=[
             ("crawl", "Crawl left over the counter.", "D1 E1 C0 repeating"),
             ("fixed", "Cross the left marker.", "D1 E0 D1 E0 D0 A0 B0 C0"),
             ("crawl", "Crawl over the countdown and the header to the blank tape.", "D1 E1 C0 repeating; D1 E0 at the header's 0"),
             ("fixed", "Rebuild the header two cells further left.", "D1 E0 D0 A0 B0 C1 F1 E0 D0 A0 B0"),
             ("recode", "Recode right over the countdown.", "C1 F1 E1 repeating"),
             ("fill", "Bounce and fill at the old marker.", "C0 D1 E0 D0 A0 B0"),
             ("recode", "Recode right over the old phase cells and the counter.", "C1 F1 E1 repeating"),
             ("halt", "F reaches the right marker's first 0. F0 writes 1, A0 writes 1, and B lands on the pile's first 1. B1 is the halt rule.", "F0 A0 B1"),
         ]),
]

def section_html(sec):
    lis = "".join(stage_li(k, esc(t), r) for k, t, r in sec["stages"])
    cost = f'<p class="cost">{esc(sec["cost"])}</p>' if sec["cost"] else ""
    return f'''
    <section class="route-sec" id="{sec["id"]}" aria-labelledby="h-{sec["id"]}">
      <div class="rhead">
        <h3 id="h-{sec["id"]}">{sec["name"]}</h3>
        <span class="when">{esc(sec["when"])}</span>
      </div>
      <div class="rbody">
        <figure class="rfig"><div class="scroll">{sec["svg"]}</div></figure>
        <div class="rtext">
          <p class="effect">{esc(sec["effect"])}</p>
          {cost}
          <ol class="stages">{lis}</ol>
        </div>
      </div>
    </section>'''

# ---------------------------------------------------------------- arrivals
ARR_CELLS = ["1", "1", "1", "0", "0", "1", "1", "1"]
ARR_GROUPS = [5, 3]
ARRIVALS = [
    ("run", "Running right", "convert", ["A", "A", "A", "A"], "A0 B0 fill the 00, then C recodes the pile into 1-digits."),
    ("recode", "Recode, phase 1", "reset", ["E", "C", "F", "E"], "E0 D0 A0 B0 fill the 00, then C recodes the pile into the new counter."),
    ("recode", "Recode from a borrow", "tick", ["C", "F", "E", "C"], "C0 turns back, C0 D1 E0 D0 A0 B0 C1 F0 step over the marker, then the run heads for the end of the pile."),
    ("recode", "Recode, phase 0", "halt", ["F", "E", "C", "F"], "F0 and A0 fill the 00, then B reads the pile's first 1. B1 halts."),
]
def arrivals_html():
    head = "".join(f'<span class="ac{" z" if c == "0" else ""}">{c}</span>' for c in ARR_CELLS)
    rows = [f'<div class="arow ahead"><span class="alab"></span><span class="acells">{head}</span><span class="aout">Right marker 11100, then the pile</span></div>']
    for kind, lab, event, letters, out in ARRIVALS:
        ls = []
        for i in range(len(ARR_CELLS)):
            if i < len(letters):
                cls = "al" + (" hit " + kind if i == 3 else "")
                ls.append(f'<span class="{cls}">{letters[i]}</span>')
            else:
                ls.append('<span class="al empty"></span>')
        rows.append(f'<div class="arow"><span class="alab">{chip(kind, lab)}<span class="ev">{event}</span></span>'
                    f'<span class="acells">{"".join(ls)}</span><span class="aout">{esc(out)}</span></div>')
    return f'<div class="arrivals">{"".join(rows)}</div>'

# ---------------------------------------------------------------- layout strip
def layout_strip():
    f = frame(1013)
    cells = f["cells"][1:]  # drop the leading blank
    head = f["head"] - 1
    parts = [("111011", "header"), ("100100100", "countdown 7"), ("10010", "left marker"), ("11", "phase 2"),
             ("100100100100111111", "middle counter 60"), ("011100", "right marker"), ("111111111111", "pile 3 + spare")]
    assert "".join(p for p, _ in parts) == cells[:sum(len(p) for p, _ in parts)], (cells,)
    out, i = [], 0
    for pat, lab in parts:
        grp = 3 if lab.startswith(("countdown", "middle", "pile")) else len(pat)
        digits = []
        for d0 in range(0, len(pat), grp):
            cs = []
            for c in pat[d0:d0 + grp]:
                cls = "c" + (" z" if c == "0" else "") + (" h" if i == head else "")
                cs.append(f'<span class="{cls}">{c}</span>')
                i += 1
            digits.append(f'<span class="dg">{"".join(cs)}</span>')
        out.append(f'<span class="g"><span class="gc wrapd">{"".join(digits)}</span><span class="gl">{esc(lab)}</span></span>')
    return f'<div class="strip"><span class="tape multi">{"".join(out)}</span></div>'


# ---------------------------------------------------------------- warm-up
WT = json.load(open(os.path.join(S, "warm_tapes.json")))
def snapshot(step, parts):
    d = WT[str(step)]
    cells, head = d["cells"], d["head"]
    assert "".join(p for p, _, _ in parts) == cells, (step, cells)
    out, i = [], 0
    for pat, lab, grp in parts:
        grp = grp or len(pat)
        digits = []
        for d0 in range(0, len(pat), grp):
            cs = []
            for c in pat[d0:d0 + grp]:
                cls = "c" + (" z" if c == "0" else "") + (" h" if i == head else "")
                cs.append(f'<span class="{cls}">{c}</span>')
                i += 1
            digits.append(f'<span class="dg">{"".join(cs)}</span>')
        out.append(f'<span class="g"><span class="gc wrapd">{"".join(digits)}</span><span class="gl">{esc(lab)}</span></span>')
    return f'<span class="tape multi">{"".join(out)}</span>'

WARM = [
    ("0–16", "The header", ["append", "crawl", "fixed"],
     "A, B and C write 111 on the blank tape, as in an append, and C turns left. The crawl back runs off the left end onto blank tape, where E reads a 0. That starts the sequence that rebuilds the header in a reset, and it turns these cells into 111011.",
     [("0–2", "append", "Append", "A0 B0 C0"), ("3–6", "crawl", "Crawl left", "D1 E1 C0 D1"), ("7–16", "fixed", "Header sequence", "E0 D0 A0 B0 C1 F1 E0 D0 A0 B0")],
     17, [("111011", "header", 0), ("1", "one more 1", 0), ("0", "blank", 0)]),
    ("17–74", "The right marker", ["crawl", "fixed", "recode"],
     "C turns back at the blank tape. The crawl again finds nothing to stop at and runs off the left end, and the header sequence rebuilds the header two cells further left. A short recode reaches blank tape, and the sequence that ends every convert and reset builds the first right marker with one pile group after it.",
     "Order: crawl left, header sequence, recode right, end sequence, crawl left.",
     75, [("111011", "header", 0), ("011100", "right marker", 0), ("111", "spare group", 0)]),
    ("75–139", "The left marker", ["crawl", "fixed", "recode", "fill"],
     "Nothing sits between the header and the right marker, so the crawl runs to the left end again. This is a reset. The recode reaches the right marker as E, and as in every reset the old right marker becomes the left marker plus two phase cells. Every part of the layout now exists, with the countdown and the counter both empty.",
     "Order: crawl left, header sequence, recode right, fill at the right marker, recode the pile, end sequence, crawl left.",
     140, [("111011", "header", 0), ("10010", "left marker", 0), ("11", "phase 2", 0), ("011100", "right marker", 0), ("111", "spare group", 0)]),
    ("140–245", "A first number", ["crawl", "fixed", "recode"],
     "Countdown 0, counter 0 and phase 2, the only time the run has that combination. The reset-style sweep turns the left marker and phase cells into digits, and its bounce at the old marker leaves one 0-digit, giving 101, which is 5. In phase 2 the sweep reaches the right marker as C, so the event ends like a tick and adds a pile group.",
     "Order: crawl left, cross the left marker, crawl left, header sequence, recode right, bounce and fill, recode right, step over the right marker, run right, append, crawl left.",
     246, [("111011", "header", 0), ("100111100", "number 101 = 5", 3), ("011100", "right marker", 0), ("111111", "pile 1 + spare", 3)]),
    ("246–701", "Five ticks", ["crawl", "fill", "recode", "run", "append"],
     "The number counts down 5, 4, 3, 2, 1, 0 while the pile grows to 7 groups. There is no left marker yet, so the number works as a middle counter with no countdown beside it.",
     "Order: five ticks, each in the order of the Tick route above.",
     702, [("111011", "header", 0), ("111111111", "number 0", 3), ("011100", "right marker", 0), ("111111111111111111111", "pile 6 + spare", 3)]),
    ("702–820", "The reset that starts the main run", ["crawl", "fixed", "recode", "fill"],
     "No left marker is in the way, so all three digits become 1s with no 0-digit, which gives countdown 7. The right marker becomes the left marker plus phase 2. The 7-group pile becomes the counter: six 1-digits, worth 63 = 2⁶ − 1, and the seventh group becomes the new right marker.",
     "Order: crawl left, header sequence, recode right, fill at the right marker, recode the pile, end sequence, crawl left.",
     821, [("111011", "header", 0), ("100100100", "countdown 7", 3), ("10010", "left marker", 0), ("11", "phase 2", 0),
           ("100100100100100100", "middle counter 63", 3), ("011100", "right marker", 0), ("111", "spare group", 0)]),
]
def warm_html():
    items = []
    for steps, title, chips, text, rules, snap, parts in WARM:
        if isinstance(rules, list):
            rows = "".join(f'<tr><td class="mono">steps {r}</td><td>{chip(k, lab)}</td><td class="mono">{esc(seq)}</td></tr>' for r, k, lab, seq in rules)
            rules_html = f'<div class="scroll"><table class="seq"><caption>Every rule, in order</caption>{rows}</table></div>'
        else:
            rules_html = f'<p class="ord">{esc(rules)}</p>'
        items.append(
            f'<li><div class="wh"><span class="mono">steps {steps}</span><h3>{esc(title)}</h3>'
            f'<span class="chips">{"".join(chip(c) for c in chips)}</span></div>'
            f'<div class="wb"><p>{esc(text)}</p>{rules_html}'
            f'<div class="wsnap"><span class="wcap">Tape after step {snap - 1:,}</span>{snapshot(snap, parts)}</div></div></li>')
    return f'<ol class="warm">{"".join(items)}</ol>'

# ---------------------------------------------------------------- setup map (to scale, from the real run)
WM = json.load(open(os.path.join(S, "warmmap.json")))
def warm_map_svg():
    N, pos, lab, lo, hi = WM["N"], WM["pos"], WM["lab"], WM["lo"], WM["hi"]
    CW, YS, X0, Y0 = 11.0, 0.62, 44.0, 34.0
    X = lambda p: X0 + (p - lo + 0.5) * CW
    Y = lambda i: Y0 + i * YS
    xr = X0 + (hi - lo + 1) * CW          # right edge of the cell area
    W2 = 760
    parts = []
    # tape history: one rect per vertical run of 1s in a cell
    for c, a, b in WM["runs"]:
        parts.append(f'<rect class="sv-tape" x="{X(c) - CW / 2 + 1.5:.1f}" y="{Y(a):.1f}" width="{CW - 3:.1f}" height="{max(YS, (b - a + 1) * YS):.1f}"/>')
    # stage separators, step axis and stage labels
    bounds = [0, 17, 75, 140, 246, 702, 821]
    names = ["The header", "The right marker", "The left marker", "A first number (5)", "Five ticks", "The final reset"]
    for k, st in enumerate(bounds):
        y = Y(st)
        if 0 < st < N:
            parts.append(f'<line class="sv-sep" x1="{X0 - 6}" y1="{y:.1f}" x2="{W2 - 8}" y2="{y:.1f}"/>')
        parts.append(f'<text class="sv-axis" x="{X0 - 10}" y="{y + 3.5:.1f}" text-anchor="end">{st}</text>')
    for k in range(6):
        ym = (Y(bounds[k]) + Y(bounds[k + 1])) / 2
        bx = xr + 22
        parts.append(f'<circle class="sv-badge" cx="{bx:.1f}" cy="{ym:.1f}" r="8.5"/><text class="sv-num" x="{bx:.1f}" y="{ym + 3.7:.1f}" text-anchor="middle">{k + 1}</text>')
        parts.append(f'<text class="sv-lab strong" x="{bx + 14:.1f}" y="{ym + 4.2:.1f}">{esc(names[k])}</text>')
    parts.append(f'<text class="sv-tag" x="{X0 - 10}" y="{Y0 - 14:.1f}" text-anchor="end">step</text>')
    # head path, one piece per run of steps with the same routine
    key = WM["key"]
    lab = list(lab)
    i = 0
    while i < N:  # a recode of one or two steps inside a fixed sequence belongs to that sequence
        j = i
        while j + 1 < N and lab[j + 1] == lab[i]: j += 1
        if lab[i] == "recode" and j - i < 2 and i > 0 and j + 1 < N and lab[i - 1] == "fixed" and lab[j + 1] == "fixed":
            for q in range(i, j + 1): lab[q] = "fixed"
        i = j + 1
    FILLS = {"D1 E0 D0 A0 B0", "E0 D0 A0 B0", "C0 D1 E0 D0 A0 B0"}
    i = 0
    path = []
    while i < N:
        j = i
        while j + 1 < N and lab[j + 1] == lab[i]: j += 1
        k = lab[i]
        box_kind = "fixed"
        if k == "fixed":
            seq = " ".join(key[i:j + 1])
            box_kind = "fill" if seq in FILLS else ("append" if seq == "A0 B0 C0" else "fixed")
        x1, y1, x2, y2 = X(pos[i]), Y(i), X(pos[j + 1]), Y(j + 1)
        if k == "fixed":
            pa, pb = min(pos[i:j + 2]), max(pos[i:j + 2])
            path.append(f'<rect class="sv-box thin {box_kind}" x="{X(pa) - CW / 2 + 1:.1f}" y="{y1:.1f}" width="{(pb - pa + 1) * CW - 2:.1f}" height="{max(2.5, y2 - y1):.1f}" rx="1.5"/>')
        elif k == "crawl":
            if abs(x2 - x1) + abs(y2 - y1) < 4:
                path.append(f'<line class="sv-path crawl" x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}"/>')
            else:
                path.append(f'<polyline class="sv-path crawl" points="{zigzag(x1, y1, x2, y2, 5.0, 2.0)}"/>')
        else:
            path.append(f'<line class="sv-path {k} thin" x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}"/>')
            if k == "recode" and math.hypot(x2 - x1, y2 - y1) > 12:
                path.append(ticks(x1, y1, x2, y2, 8.0, 2.4))
        i = j + 1
    parts.extend(path)
    parts.append(f'<circle class="sv-start" cx="{X(pos[0]):.1f}" cy="{Y(0):.1f}" r="4"/><text class="sv-lab" x="{X(pos[0]) + 9:.1f}" y="{Y(0) - 6:.1f}">blank tape</text>')
    parts.append(f'<circle class="sv-end" cx="{X(pos[N]):.1f}" cy="{Y(N):.1f}" r="4"/>')
    # layout at the end of the setup, at true cell positions
    yb = Y(N) + 26
    names_b = {"count": ("countdown", "7"), "phase": ("", ""), "mid": ("middle counter", "63"), "pile": ("pile", "0")}
    frames = iter([("header", "111011"), ("marker", "100 10"), ("marker", "0 11100")])
    regs = []
    for a, b, n in WM["segs"]:
        nm, det = next(frames) if n == "frame" else names_b[n]
        regs.append(("r", X(a) - CW / 2, X(b) + CW / 2, nm, det))
        if n == "phase":
            parts.append(f'<text class="sv-detail" x="{(X(a) + X(b)) / 2:.1f}" y="{yb + 47:.1f}" text-anchor="middle">phase 2</text>')
    parts.append(band(regs, yb, "tape after step 820"))
    H = yb + 56
    return (f'<svg class="route wmap-svg" viewBox="0 0 {W2} {H:.0f}" role="img" aria-label="The first 821 steps of the real run drawn to scale: the head path coloured by routine over a record of the tape, divided into the six setup stages.">'
            + "".join(parts) + "</svg>")

def warm_map_html():
    return f'''<figure class="wmap">
      <div class="scroll">{warm_map_svg()}</div>
      <figcaption>
        <span>The real run's first 821 steps, to scale: one row per step and one column per cell. Shaded columns are cells holding a 1, so you can watch the header move left each time it is rebuilt and the pile grow to the right. The numbers match the stages listed below.</span>
        <span class="legend" aria-label="Legend">
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><polyline class="sv-path crawl" points="{zigzag(2, 6, 42, 6, 5, 3)}"/></svg>Crawl left</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><line class="sv-path run" x1="2" y1="6" x2="42" y2="6"/></svg>Run right</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><line class="sv-path recode" x1="2" y1="6" x2="42" y2="6"/>{ticks(2, 6, 42, 6, 9, 3.5)}</svg>Recode right</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><rect class="sv-box fill" x="8" y="1" width="28" height="10" rx="3"/></svg>Fill</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><rect class="sv-box append" x="8" y="1" width="28" height="10" rx="3"/></svg>Append</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><rect class="sv-box fixed" x="8" y="1" width="28" height="10" rx="3"/></svg>Other fixed sequence</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><rect class="sv-tape" x="18" y="0" width="8" height="12"/></svg>Cell holding 1</span>
        </span>
      </figcaption>
    </figure>'''

# ---------------------------------------------------------------- page
CSS = open(os.path.join(S, "map.css")).read()

crawl_frames = frame_rows([(845, "crawl", None, None), (846, "crawl", None, None), (847, "crawl", None, None), (848, "crawl", None, None)])
run_frames = frame_rows([(835, "recode", [3, 3, 3], ["marker", "pile", "blank"]), (836, "run", [3, 3, 3], None), (837, "run", [3, 3, 3], None), (838, "run", [3, 3, 3], None), (839, "append", [3, 3, 3], None)])
append_frames = frame_rows([(1064, "append", [3, 3, 5], ["pile", "", "blank"]), (1065, "append", [3, 3, 5], None), (1066, "append", [3, 3, 5], None), (1067, "crawl", [3, 3, 5], None)])
sub_groups = [3, 3, 3, 3, 3, 6]
sub_frames = frame_rows(
    [("labels", sub_groups, ["d4", "d3", "d2", "d1", "d0", "gap + marker"]),
     ("h", "crawl", "Crawl, last step", "D erases the first cell of d1 and moves left onto d2, the lowest 1-digit."),
     (1030, "crawl", sub_groups, None),
     ("h", "fill", "Fill", "E reads the last 0 of d2 and moves left. D writes 1 into the middle cell, A writes 1 into the last cell, and B writes back the cell D erased. d2 is now 111, a 0."),
     (1031, "fill", sub_groups, None), (1032, "fill", sub_groups, None), (1033, "fill", sub_groups, None), (1034, "fill", sub_groups, None),
     ("h", "recode", "Recode", "C and F write 0 into the second and third cells of each digit, and E keeps the 1 that starts the next. d1 and d0 become 100, so both are now 1s. The sweep carries on over the gap and the marker's first three cells. The step over the marker and the crawl back put those right again."),
     (1035, "recode", sub_groups, None), (1036, "recode", sub_groups, None), (1037, "recode", sub_groups, None),
     (1038, "recode", sub_groups, None), (1039, "recode", sub_groups, None), (1040, "recode", sub_groups, None),
     (1041, "recode", sub_groups, None), (1042, "recode", sub_groups, None), (1043, "recode", sub_groups, None),
     ("h", "fixed", "End", "C reads the right marker's first 0, and the tick goes on with the step over the marker: C0 D1 E0 D0 A0 B0 C1 F0."),
     (1044, "fixed", sub_groups, None)])

page = f'''<title>BB(6) Champion Rule Map</title>
<meta name="claude:viewport-fit-sides" content="cover">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Atkinson+Hyperlegible:ital,wght@0,400;0,700;1,400&family=Martian+Mono:wght@400;500;700&display=swap">
<style>
{CSS}
</style>
<div class="wrap">
  <header class="top">
    <p class="eyebrow">Busy Beaver · 6 states, 2 symbols · found by mxdys, June 2025</p>
    <h1>What each rule in the BB(6) champion does</h1>
    <p class="lede">The champion's table has twelve entries: six states, each with one rule for reading 0 and one for reading 1. Sorted by what they do, they form three ways to move along the tape plus a few short fixed sequences. Every part of the calculation uses the same routines in a different order, and the 0s on the tape decide which routine runs next.</p>
    <p class="meta"><code class="machine">1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE</code> <a href="{EXPLORER}" target="_blank" rel="noopener">Watch it run in the BB(6) Champion Explorer</a></p>
    <p class="hint">Hover over or tap any rule name, such as D1, to see what it does. The Rules button in the corner opens the full table.</p>
  </header>

  <section class="block" aria-labelledby="h-table">
    <h2 id="h-table">The rule table, sorted by job</h2>
    <div class="two">
      <div class="card">
        {rule_table()}
        <p class="small">Each entry says what to write, which way to move and the next state. Because that last letter names the state that acts next, rules always chain: C0 is followed by a D rule, E1 by a C rule. Every sequence on this page is written in that order. Four rules belong to two routines.</p>
      </div>
      <dl class="routines">
        <div><dt>{chip("crawl", "Crawl left")}<span class="mono">D1 E1 C0</span></dt><dd>D erases the cell and moves left, E steps back right, and C writes the 1 back and moves left again. The head ends one cell further left every three steps and the tape is unchanged. The crawl ends when E reads a 0.</dd></div>
        <div><dt>{chip("run", "Run right")}<span class="mono">A1</span></dt><dd>A keeps the 1 and moves right, one cell per step. The run ends when A reads a 0.</dd></div>
        <div><dt>{chip("recode", "Recode right")}<span class="mono">C1 F1 E1</span></dt><dd>C writes 0, F writes 0 and E keeps the 1, so every 111 becomes 100, one cell per step. The recode ends when C, E or F reads a 0. When F reads it, F0 hands the head to the run.</dd></div>
        <div><dt>{chip("fill", "Fill")}<span class="mono">E0 D0 A0 B0</span></dt><dd>A crawl that reaches the 00 of a 100 fills both 0s, and B writes back the cell D erased. The 100 becomes 111.</dd></div>
        <div><dt>{chip("append", "Append")}<span class="mono">A0 B0 C0</span></dt><dd>A run that reaches blank tape writes 111, and C turns the head into a crawl.</dd></div>
        <div><dt>{chip("halt", "Halt")}<span class="mono">B1</span></dt><dd>B normally lands on a cell that is 0, often one that D has just erased. Reading a 1 there stops the machine.</dd></div>
      </dl>
    </div>
    <div class="notes">
      <p><b>E1 is where the crawl and the recode meet.</b> E always moves right into C, and C's cell decides which routine carries on. In a crawl that cell is the one D just erased, so C reads 0 and turns left. In a recode it is a fresh 1, so C reads 1 and keeps going right.</p>
      <p><b>The 3-state cycles set the digit size.</b> One turn of C, F and E rewrites exactly three cells, which is why both counters use 3-cell digits: 100 for 1 and 111 for 0.</p>
    </div>
  </section>

  <section class="block" aria-labelledby="h-signs">
    <h2 id="h-signs">The 0s are the signposts</h2>
    <p class="intro">From step 821 on, the tape has this shape between events. This is the real run at step 1,013, with the head on the counter's last cell. Every routine passes over 1s, so the 0s, shown dark, are where things change.</p>
    {layout_strip()}
    <ul class="signs">
      <li><b>The 00 inside each 1-digit.</b> A crawl that reaches it fills it in, which is how both counters subtract.</li>
      <li><b>The left marker 100 10.</b> Only a crawl through an empty counter gets here. It crosses the marker and goes on into the countdown.</li>
      <li><b>The header's 0 and the blank tape beyond it.</b> A crawl only reaches them when the countdown has no 1-digit left, and that starts a reset or the halt.</li>
      <li><b>The right marker 0 11100.</b> Recodes and runs heading right stop at its first 0. The state that gets there picks what happens next.</li>
      <li><b>The blank tape after the pile.</b> The run stops here and appends a group.</li>
    </ul>
    <p class="small">The pile holds one more 111 group than its value. A convert or reset turns that spare group into the next right marker.</p>
  </section>

  <section class="block" aria-labelledby="h-close">
    <h2 id="h-close">The routines up close</h2>
    <p class="intro">Real steps from the run. The outlined cell is under the head, the letter is the head's state, and the text says which rule fires next.</p>
    <div class="cards">
      <div class="card"><h3 class="ch">{chip("crawl", "Crawl left")}</h3>{crawl_frames}<p class="cap">On the pile. D erases a cell and moves left, E steps back onto it, and C writes the 1 back and moves left. D is now one cell further left. Three steps per cell.</p></div>
      <div class="card"><h3 class="ch">{chip("run", "Run right")}</h3>{run_frames}<p class="cap">F0 ends the step over the right marker and hands off to A. A runs over the pile's 1s until it reads the blank tape.</p></div>
      <div class="card"><h3 class="ch">{chip("append", "Append")}</h3>{append_frames}<p class="cap">At the end of the pile A, B and C each write a 1. C moves left, so D starts the crawl back.</p></div>
      <div class="card wide"><h3 class="ch">{chip("fill", "Fill")} {chip("recode", "Recode right")} <span class="chtext">Subtracting one, step by step</span></h3>{sub_frames}<p class="cap">Every step from 1,030 to 1,044. The counter holds 60, written 111100, and the frames show its last five digits, d4 to d0. They go from 1 1 1 0 0 to 1 1 0 1 1, so the counter now reads 111011, or 59.</p></div>
    </div>
  </section>

  <section class="block" aria-labelledby="h-routes">
    <h2 id="h-routes">Each part of the calculation</h2>
    <p class="intro">The head's path through each event, drawn against the tape. Time runs down the page. A crawl takes three steps per cell, so crawl segments are drawn three times steeper than runs and recodes. Region widths are schematic, and the numbers match the list beside each drawing.</p>
    <div class="legend" aria-label="Legend">
      <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><polyline class="sv-path crawl" points="{zigzag(2, 6, 42, 6, 5, 3)}"/></svg>Crawl left</span>
      <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><line class="sv-path run" x1="2" y1="6" x2="42" y2="6"/></svg>Run right</span>
      <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><line class="sv-path recode" x1="2" y1="6" x2="42" y2="6"/>{ticks(2, 6, 42, 6, 9, 3.5)}</svg>Recode right</span>
      <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><rect class="sv-box fill" x="8" y="1" width="28" height="10" rx="3"/></svg>Fill</span>
      <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><rect class="sv-box append" x="8" y="1" width="28" height="10" rx="3"/></svg>Append</span>
      <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><rect class="sv-box fixed" x="8" y="1" width="28" height="10" rx="3"/></svg>Other fixed sequence</span>
    </div>
    {"".join(section_html(s) for s in SECTIONS)}
  </section>

  <section class="block" aria-labelledby="h-phase">
    <h2 id="h-phase">Why the phase decides between reset and halt</h2>
    <div class="prose">
      <p>The countdown and the left marker sit on one 3-cell grid. The middle counter, the right marker and the pile sit on another. The phase is the offset between the two grids, 0, 1 or 2 cells, and the decoder shows it as the 1s between the left marker and the counter.</p>
      <p>Ticks never compare the two grids. A convert makes the stretch between the markers 3b + 5 cells longer. Five cells is one digit plus two, so the offset steps from 2 to 1 to 0 and back to 2.</p>
      <p>In a reset or a halt, the long recode starts on the left grid and runs all the way to the right marker. Its three states repeat every three cells, so the offset decides which state reaches the marker's first 0. A tick's recode starts on the right grid, so it always arrives as C.</p>
    </div>
    <figure class="afig">
      <div class="scroll">{arrivals_html()}</div>
      <figcaption>Which state reads the right marker's first 0 decides what happens next. Each row lists the states that read the marker's cells, left to right, up to that first 0.</figcaption>
    </figure>
    <p class="small">After the warm-up the countdown never runs out in phase 2. mxdys's analysis has it running out twice in phase 1, which gives two resets, and then in phase 0, which gives the halt. It does happen once during the warm-up, at step 140, while both counters are still empty. There the sweep arrives as C and the event ends like a tick.</p>
  </section>

  <section class="block" aria-labelledby="h-warm">
    <h2 id="h-warm">How the tape gets set up</h2>
    <p class="intro">The machine has no separate setup code. From a blank tape it runs the same routines as the rest of the run, and its first six events, working on empty or tiny numbers, build the layout one piece at a time. Each tape below is the real tape at the end of a stage, with the head's cell outlined.</p>
    {warm_map_html()}
    {warm_html()}
    <p class="small">From step 821 the run follows mxdys's rules: 63 ticks empty the counter, and the first convert comes at step 28,297.</p>
  </section>

  <section class="block" aria-labelledby="h-steps">
    <h2 id="h-steps">Where the steps go</h2>
    <div class="prose">
      <p>Almost all the time goes into ticks, and a tick is mostly travel. In the first 20 million steps of the real run, 74.9% are crawl steps and 24.9% are run steps. Fills, appends, recodes and the other fixed sequences share the last 0.2%.</p>
      <p>The 3-to-1 split comes from the costs: each tick crawls back over every pile cell at three steps per cell and runs out over the same cells at one step per cell. That is about 12 steps per pile group, and the pile grows by one group every tick.</p>
    </div>
  </section>

  <footer>Tape layout and rules follow mxdys's analysis on the <a href="{WIKI}" target="_blank" rel="noopener">BusyBeaverWiki page for this machine</a>. Every frame, rule sequence and step count on this page was checked against a step-by-step simulation of the machine.</footer>
</div>
'''
# ---------------------------------------------------------------- rule look-up: hover/tap tokens + floating reference
import re as _re
def rule_def(r):
    st, sym = r[0], int(r[1])
    txt, chips = RULES[st][sym]
    w, d, n = txt[0], txt[1], txt[2]
    if n == "Z":
        return f"{st} reads {sym}: write {w}, move {'right' if d == 'R' else 'left'}, halt", chips
    return f"{st} reads {sym}: write {w}, move {'right' if d == 'R' else 'left'}, go to {n}", chips

DEFS = {f"{s}{y}": dict(zip(("text", "chips"), rule_def(f"{s}{y}"))) for s in RULES for y in (0, 1)}

TOKEN = _re.compile(r'(?<![A-Za-z0-9])([A-F][01])(?![A-Za-z0-9])')
SKIP = ("style", "script", "svg", "title", "code", "aside")
def wrap_tokens(doc):
    out, skip = [], []
    for part in _re.split(r'(<[^>]+>)', doc):
        if part.startswith("<"):
            m = _re.match(r'<(/?)([a-zA-Z0-9]+)', part)
            if m:
                closing, tag = m.group(1) == "/", m.group(2).lower()
                if tag in SKIP and not part.endswith("/>"):
                    if closing and skip and skip[-1] == tag: skip.pop()
                    elif not closing: skip.append(tag)
            out.append(part)
        elif skip:
            out.append(part)
        else:
            out.append(TOKEN.sub(lambda m: f'<span class="rk" data-r="{m.group(1)}">{m.group(1)}</span>', part))
    return "".join(out)

def panel_cell(r):
    st, sym = r[0], int(r[1])
    txt, chips = RULES[st][sym]
    w, d, n = txt[0], txt[1], txt[2]
    arrow = "→" if d == "R" else "←"
    nxt = "halt" if n == "Z" else n
    sws = "".join(f'<span class="sw {c}" title="{NAMES[c]}"></span>' for c in chips)
    return f'<td data-r="{r}"><span class="rpc"><span class="mono"><b>{w}</b> {arrow} <b>{nxt}</b></span><span class="sws">{sws}</span></span></td>'

def overlay_html():
    rows = "".join(f'<tr><th scope="row">{s}</th>{panel_cell(s + "0")}{panel_cell(s + "1")}</tr>' for s in RULES)
    defs_js = json.dumps({k: {"text": v["text"], "chips": [[c, NAMES[c]] for c in v["chips"]]} for k, v in DEFS.items()})
    return f'''
<button type="button" class="rules-fab" id="rules-fab" aria-expanded="false" aria-controls="rules-panel"><span class="fab-grid" aria-hidden="true"></span>Rules</button>
<aside class="rules-panel" id="rules-panel" aria-label="Rule reference" hidden>
  <div class="rp-head"><b>The twelve rules</b><button type="button" class="rp-close" id="rp-close" aria-label="Close the rule reference">×</button></div>
  <table class="rp"><thead><tr><th></th><th scope="col">reads 0</th><th scope="col">reads 1</th></tr></thead><tbody>{rows}</tbody></table>
  <p class="rp-foot">Each cell: what to write, which way to move, and the next state. Squares show the routine.</p>
</aside>
<div class="rk-tip" id="rk-tip" role="tooltip" hidden></div>
<script>
(() => {{
  const DEF = {defs_js};
  const tip = document.getElementById("rk-tip"), fab = document.getElementById("rules-fab");
  const panel = document.getElementById("rules-panel"), closeBtn = document.getElementById("rp-close");
  let pinned = null;
  const cells = r => panel.querySelectorAll('td[data-r="' + r + '"]');
  function mark(r) {{
    panel.querySelectorAll("td.on").forEach(td => td.classList.remove("on"));
    document.querySelectorAll(".rk.on").forEach(el => el.classList.remove("on"));
    if (r) cells(r).forEach(td => td.classList.add("on"));
  }}
  function place(el) {{
    const b = el.getBoundingClientRect(), t = tip.getBoundingClientRect();
    let x = b.left + b.width / 2 - t.width / 2;
    x = Math.max(8, Math.min(x, window.innerWidth - t.width - 8));
    let y = b.top - t.height - 8;
    if (y < 8) y = b.bottom + 8;
    tip.style.left = x + "px"; tip.style.top = y + "px";
  }}
  function show(el) {{
    const d = DEF[el.dataset.r]; if (!d) return;
    tip.innerHTML = '<span class="tip-r">' + el.dataset.r + '</span><span class="tip-t">' + d.text + '</span><span class="tip-c">' +
      d.chips.map(c => '<span class="chip ' + c[0] + '"><span class="sw ' + c[0] + '"></span>' + c[1] + '</span>').join("") + '</span>';
    tip.hidden = false; place(el); mark(el.dataset.r); el.classList.add("on");
  }}
  function hide() {{ tip.hidden = true; pinned = null; mark(null); }}
  document.addEventListener("pointerover", e => {{
    if (e.pointerType === "touch" || pinned) return;
    const el = e.target.closest(".rk"); if (el) show(el);
  }});
  document.addEventListener("pointerout", e => {{
    if (e.pointerType === "touch" || pinned) return;
    const el = e.target.closest(".rk"); if (el && !el.contains(e.relatedTarget)) hide();
  }});
  document.addEventListener("click", e => {{
    const el = e.target.closest(".rk");
    if (el) {{ if (pinned === el) {{ hide(); }} else {{ pinned = el; show(el); }} return; }}
    if (pinned && !e.target.closest("#rk-tip")) hide();
  }});
  window.addEventListener("scroll", () => {{ if (!tip.hidden) {{ if (pinned) place(pinned); else hide(); }} }}, {{ passive: true }});
  window.addEventListener("resize", () => {{ if (!tip.hidden) hide(); }});
  function setOpen(open) {{
    panel.hidden = !open; fab.setAttribute("aria-expanded", String(open)); fab.classList.toggle("open", open);
    try {{ localStorage.setItem("rulesPanelOpen", open ? "1" : "0"); }} catch (err) {{}}
  }}
  fab.addEventListener("click", () => setOpen(panel.hidden));
  closeBtn.addEventListener("click", () => {{ setOpen(false); fab.focus(); }});
  document.addEventListener("keydown", e => {{ if (e.key === "Escape") {{ hide(); if (!panel.hidden) setOpen(false); }} }});
  try {{ if (localStorage.getItem("rulesPanelOpen") === "1") setOpen(true); }} catch (err) {{}}
}})();
</script>'''

page = wrap_tokens(page)
k = page.rfind("</div>") + len("</div>")
page = page[:k] + "\n" + overlay_html() + page[k:]

# A complete HTML document: the page body above, inside the same document skeleton the published copy has.
PRE = ('<!doctype html><html><head><meta charset=utf8><meta name=viewport content="width=device-width,initial-scale=1,viewport-fit=cover">'
       '<style>:root{color-scheme:light;box-sizing:border-box;padding-top:env(safe-area-inset-top,0px);padding-bottom:env(safe-area-inset-bottom,0px)}'
       'html{scroll-padding-top:env(safe-area-inset-top,0px)}body{margin:0;padding:0;font:14px -apple-system,BlinkMacSystemFont,sans-serif;background:#fff;color:#000}'
       'img{max-width:100%}[hidden]:not([hidden=until-found i]){display:none!important}</style></head><body>\n')
SUF = "\n</body></html>"
open(os.path.join(S, "..", "..", "champion-rule-map.html"), "w").write(PRE + page + SUF)
print("ok", len(page))
bad=[c for c in COLLIDE if c[2] < 2]
print("badge clearances:", sorted(COLLIDE, key=lambda c:c[2])[:6])
print("TOO CLOSE:", bad)
