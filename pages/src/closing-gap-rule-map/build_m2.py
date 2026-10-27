#!/usr/bin/env python3
"""Builds the Rule Map page for 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE.
Every frame, map and rule sequence comes from data_m2 (a step-by-step simulation)."""
import json, math, html, os, re
from data_m2 import SNAPS, TRACES, frame, content
from m2sim import classify, TR as MTR

S = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(S, "data")
OUT = os.path.join(S, "..", "..", "closing-gap-rule-map.html")
esc = html.escape
MACHINE = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE"
CLEAN = json.load(open(os.path.join(D, "clean3e9.json")))

def fmt(n):
    return f"{n:,}"

# ---------------------------------------------------------------- rule table
RULES = {  # state: [(read0 text, chips), (read1 text, chips)]
    "A": [("1RB", ["recode", "fill", "append"]), ("0RE", ["crawl", "fill"])],
    "B": [("1LC", ["crawl", "append"]), ("0RA", ["recode", "fill", "append"])],
    "C": [("1LA", ["crawl"]), ("1LD", ["fixed", "append"])],
    "D": [("1LA", ["fixed", "append"]), ("---", ["halt"])],
    "E": [("0RF", ["run", "append"]), ("0LB", ["crawl", "append"])],
    "F": [("0LD", ["append"]), ("1RE", ["run"])],
}
for st, pair in RULES.items():          # the table above must match the machine
    for y in (0, 1):
        r = MTR[(st, y)]
        assert (r[3] if r else "---") == pair[y][0], (st, y)

NAMES = {"crawl": "Carry left", "run": "Pass right", "recode": "Shift right", "fill": "Gap step",
         "append": "Turn", "fixed": "Fixed sequence", "halt": "Halt"}
SHORT = {"crawl": "carry", "run": "pass", "recode": "shift", "fill": "gap step", "append": "turn", "fixed": "fixed", "halt": "halt"}

def chip(k, label=None):
    return f'<span class="chip {k}"><span class="sw {k}"></span>{esc(label or SHORT[k])}</span>'

def rule_cell(state, sym, txt, chips):
    if txt == "---":
        body = '<b class="haltw">halt</b> (no rule)'
    else:
        w, d, n = txt[0], txt[1], txt[2]
        body = f'write <b>{w}</b>, {"→" if d == "R" else "←"}, <b>{n}</b>'
    return f'<td><div class="rt"><span class="mono">{body}</span><span class="chips">{"".join(chip(c) for c in chips)}</span></div></td>'

def rule_table():
    rows = []
    for st, pair in RULES.items():
        rows.append(f'<tr><th scope="row">{st}</th>{"".join(rule_cell(st, y, *pair[y]) for y in (0, 1))}</tr>')
    return ('<table class="rules"><thead><tr><th scope="col">State</th><th scope="col">Reads 0</th><th scope="col">Reads 1</th></tr></thead>'
            f'<tbody>{"".join(rows)}</tbody></table>')

# ---------------------------------------------------------------- tape cells and frames
def cells_html(cells, head=None, groups=None, labels=None, kind=None, zeros=True):
    groups = groups or [len(cells)]
    out, i = [], 0
    for gi, g in enumerate(groups):
        cs = []
        for _ in range(g):
            c = cells[i]
            cls = "c"
            if zeros and c == "0": cls += " z"
            if head is not None and i == head: cls += f" h {kind or 'fixed'}"
            cs.append(f'<span class="{cls}">{c}</span>')
            i += 1
        lab = f'<span class="gl">{esc(labels[gi])}</span>' if labels and labels[gi] else ""
        out.append(f'<span class="g"><span class="gc">{"".join(cs)}</span>{lab}</span>')
    return f'<span class="tape">{"".join(out)}</span>'

def rule_words(key, rule):
    s, r = key[0], key[1]
    if rule == "---":
        return f"{s} reads {r}: no rule, the machine halts"
    w, d, n = rule[0], rule[1], rule[2]
    return f"{s} reads {r}: write {w}, move {'right' if d == 'R' else 'left'}, go to {n}"

STEP_KIND = {}   # step -> routine kind, from the classifier over the traced ranges
for name, (a, b) in {"setup": (0, 46), "example": (4180, 4700)}.items():
    ks, _, _ = classify(TRACES[name]["key"])
    for i, k in enumerate(ks):
        STEP_KIND[a + i] = k
def kind_at(step):
    return STEP_KIND.get(step, "fixed")

def frame_rows(spec, lo, hi, kinds=None):
    rows = []
    for item in spec:
        if isinstance(item, tuple) and item[0] == "h":
            _, kind, title, text = item
            rows.append(f'<div class="fh">{chip(kind, title)}<span>{esc(text)}</span></div>')
            continue
        step = item
        f = frame(step, lo, hi)
        kind = (kinds or {}).get(step) or kind_at(step)
        rows.append(
            f'<div class="fr"><span class="st {kind}">{f["state"]}</span>'
            f'<span class="tw">{cells_html(f["cells"], f["head"], None, None, kind)}</span>'
            f'<span class="fw"><span class="mono">step {fmt(step)}</span> <span>{esc(rule_words(f["key"], f["rule"]))}</span></span></div>')
    return f'<div class="frames">{"".join(rows)}</div>'

# ---------------------------------------------------------------- route diagrams
W = 720
SLOPE = {"crawl": 0.4, "run": 0.2, "recode": 0.2}
FIX_H = 12

def band(regions, y, tag):
    parts = [f'<text class="sv-tag" x="16" y="{y - 6}">{tag}</text>']
    for reg in regions:
        kind, a, b = reg[0], reg[1], reg[2]
        if kind == "blank":
            parts.append(f'<rect class="sv-blank" x="{a + 1}" y="{y}" width="{b - a - 2}" height="34" rx="3"/>')
            if len(reg) > 3 and reg[3]:
                parts.append(f'<text class="sv-detail" x="{(a + b) / 2}" y="{y + 21}" text-anchor="middle">{esc(reg[3])}</text>')
            continue
        name, detail = reg[3], reg[4]
        cls = "sv-reg" + (" mark" if len(reg) > 5 and reg[5] else "")
        parts.append(f'<rect class="{cls}" x="{a + 1}" y="{y}" width="{b - a - 2}" height="34" rx="3"/>')
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
COLLIDE = []

def badge(x, y, n):
    return (f'<circle class="sv-badge" cx="{x:.1f}" cy="{y:.1f}" r="{BADGE_R}"/>'
            f'<text class="sv-num" x="{x:.1f}" y="{y + 3.9:.1f}" text-anchor="middle">{n}</text>')

def seg_dist(px, py, ax, ay, bx, by):
    vx, vy = bx - ax, by - ay
    L2 = vx * vx + vy * vy or 1e-9
    t = max(0, min(1, ((px - ax) * vx + (py - ay) * vy) / L2))
    return math.hypot(px - (ax + t * vx), py - (ay + t * vy))

def box_dist(px, py, x1, y1, x2, y2):
    return math.hypot(max(x1 - px, 0, px - x2), max(y1 - py, 0, py - y2))

def route_svg(name, before, stages, after, end_label, aria):
    """stages: ('start', x) | (kind, xa, xb, n, off) for crawl/run/recode | ('box', kind, a, b, exit, n, off) | ('halt',)
    off is (dx, dy) from the segment midpoint or box centre, or ('u'|'d', dist) along the segment's normal."""
    y0 = 96
    body, segs, boxes, bpos, labels = [], [], [], [], []
    x, y = None, y0
    for st in stages:
        k = st[0]
        if k == "start":
            x = st[1]
            body.append(f'<circle class="sv-start" cx="{x}" cy="{y}" r="4.5"/>')
            if len(st) > 2 and st[2] == "left":
                body.append(f'<text class="sv-lab" x="{x - 10}" y="{y + 4.5}" text-anchor="end">start</text>')
                labels.append((x - 46, y - 8, x - 8, y + 6))
            else:
                body.append(f'<text class="sv-lab" x="{x + 10}" y="{y + 4.5}">start</text>')
                labels.append((x + 8, y - 8, x + 46, y + 6))
        elif k in SLOPE:
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
                L = math.hypot(xb - xa, dy) or 1; ux, uy = (xb - xa) / L, dy / L
                cand = [(uy, -ux), (-uy, ux)]
                nx, ny = min(cand, key=lambda v: v[1]) if off[0] == "u" else max(cand, key=lambda v: v[1])
                off = (nx * off[1], ny * off[1])
            bpos.append((mx + off[0], my + off[1], n))
            x, y = xb, y2
        elif k == "box":
            _, kind, a, b, exit_, n, off = st
            body.append(f'<rect class="sv-box {kind}" x="{a}" y="{y:.1f}" width="{b - a}" height="{FIX_H}" rx="3"/>')
            boxes.append((a, y, b, y + FIX_H))
            bpos.append(((a + b) / 2 + off[0], y + FIX_H / 2 + off[1], n))
            x, y = exit_, y + FIX_H
        elif k == "halt":
            body.append(f'<rect class="sv-halt" x="{x - 5.5}" y="{y:.1f}" width="11" height="11"/>')
            body.append(f'<text class="sv-lab strong" x="{x + 11}" y="{y + 10:.1f}">halt</text>')
            boxes.append((x - 5.5, y, x + 5.5, y + 11))
            labels.append((x + 9, y - 1, x + 40, y + 12))
            y += 11
    if end_label:
        body.append(f'<circle class="sv-end" cx="{x}" cy="{y:.1f}" r="4.5"/>')
        right = x < 360
        tx = x + 10 if right else x - 10
        body.append(f'<text class="sv-lab" x="{tx}" y="{y + 4.5:.1f}" text-anchor="{"start" if right else "end"}">{esc(end_label)}</text>')
        boxes.append((x - 4.5, y - 4.5, x + 4.5, y + 4.5))
        labels.append((x + 8, y - 8, x + 110, y + 6) if right else (x - 110, y - 8, x - 8, y + 6))
    badges = [badge(bx, by, n) for bx, by, n in bpos]
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
    edges = sorted({r[1] for r in before[1:]} | {before[-1][1]})
    for a in edges:
        guides.append(f'<line class="sv-guide" x1="{a}" y1="64" x2="{a}" y2="{path_bottom:.1f}"/>')
    parts = [band(before, 26, "before"), "".join(guides), "".join(body), "".join(badges)]
    if after:
        parts.append(band(after, path_bottom + 24, "after"))
    return (f'<svg class="route" viewBox="0 0 {W} {H:.0f}" role="img" aria-label="{esc(aria)}">' + "".join(parts) + "</svg>")

def stage_li(kind, text, rules=None):
    r = f' <span class="mono rl">{esc(rules)}</span>' if rules else ""
    return f'<li>{chip(kind)}<span>{text}{r}</span></li>'

# regions: ("blank", a, b[, text]) | ("r", a, b, name, detail[, is_mark])
B_MARKER = [("blank", 16, 40), ("r", 40, 112, "left part", ""), ("r", 112, 172, "gap", "000", 1),
            ("r", 172, 480, "stripes", "d cells"), ("r", 480, 560, "marker", "11", 1), ("r", 560, 704, "stripes", "")]
A_MARKER = [("blank", 16, 40), ("r", 40, 120, "left part", "+ 2 cells"), ("r", 120, 180, "gap", "→ 2", 1),
            ("r", 180, 472, "stripes", "d − 4 cells"), ("r", 472, 552, "marker", "← 2", 1), ("r", 552, 704, "stripes", "+ 2 cells")]
MARKER = [("start", 172), ("run", 172, 480, 1, ("u", 16)), ("box", "append", 466, 540, 540, 2, (56, -6)),
          ("crawl", 540, 500, 3, (28, 12)), ("box", "fixed", 470, 500, 470, 4, (-28, -8)),
          ("crawl", 470, 184, 5, ("u", 18)), ("box", "fill", 160, 184, 184, 6, (-24, 0))]

B_WALL = [("blank", 16, 40), ("r", 40, 112, "left part", ""), ("r", 112, 172, "gap", "000", 1),
          ("r", 172, 540, "stripes", "d cells"), ("r", 540, 600, "wall", "00", 1), ("r", 600, 704, "beyond", "")]
A_WALL = [("blank", 16, 40), ("r", 40, 120, "left part", "+ 2 cells"), ("r", 120, 180, "gap", "→ 2", 1),
          ("r", 180, 540, "stripes", "d − 2 cells"), ("r", 540, 600, "wall", "same", 1), ("r", 600, 704, "beyond", "")]
WALL = [("start", 172), ("run", 172, 540, 1, ("u", 16)), ("box", "append", 528, 558, 540, 2, (32, 0)),
        ("crawl", 540, 184, 3, ("u", 18)), ("box", "fill", 160, 184, 184, 4, (-24, 0))]

B_SWAP = [("blank", 16, 40), ("r", 40, 220, "left part", ""), ("r", 220, 280, "gap", "000", 1), ("r", 280, 340, "marker", "11", 1),
          ("r", 340, 704, "stripes", "up to the next mark")]
A_SWAP = [("blank", 16, 40), ("r", 40, 200, "left part", ""), ("r", 200, 260, "marker", "11", 1), ("r", 260, 320, "gap", "000", 1),
          ("r", 320, 704, "stripes", "")]
SWAP = [("start", 280, "left"), ("run", 280, 300, 1, (0, -22)), ("box", "append", 288, 340, 330, 2, (40, 0)),
        ("crawl", 330, 270, 3, (26, 8)), ("box", "fill", 246, 270, 270, 4, (-24, 0)), ("run", 270, 560, 5, ("u", 16))]

B_MERGE = [("blank", 16, 40), ("r", 40, 124, "next gap", "or left end", 1), ("r", 124, 320, "stripes", "and old markers"),
           ("r", 320, 380, "gap", "000", 1), ("r", 380, 440, "stripes", "2 cells"), ("r", 440, 500, "marker", "11", 1), ("r", 500, 704, "stripes", "")]
A_MERGE = [("blank", 16, 40), ("r", 40, 132, "gap", "moved or new", 1), ("r", 132, 380, "stripes", "and old markers"),
           ("r", 380, 440, "wall", "00", 1), ("r", 440, 704, "stripes", "")]
MERGE = [("start", 380, "left"), ("run", 380, 440, 1, (0, -20)), ("box", "append", 428, 494, 494, 2, (52, -6)),
         ("crawl", 494, 454, 3, (28, 12)), ("box", "fixed", 336, 454, 336, 4, (0, 22)),
         ("crawl", 336, 240, 5, ("u", 18)), ("box", "fixed", 222, 240, 222, 6, (-26, -12)),
         ("crawl", 222, 124, 7, ("u", 18)), ("box", "fill", 100, 124, 124, 8, (-24, 0)), ("run", 124, 300, 9, ("u", 16))]

B_MEET = [("blank", 16, 40), ("r", 40, 124, "next gap", "or left end", 1), ("r", 124, 300, "stripes", "and old markers"),
          ("r", 300, 360, "gap", "000", 1), ("r", 360, 420, "stripes", "1 cell"), ("r", 420, 480, "wall", "00", 1), ("r", 480, 616, "stripes", ""), ("blank", 616, 704, "blank")]
A_MEET = [("blank", 16, 40), ("r", 40, 132, "gap", "moved or new", 1), ("r", 132, 300, "stripes", "and old markers"),
          ("r", 300, 620, "stripes", "gap and wall gone"), ("r", 620, 680, "marker", "new end", 1), ("blank", 680, 704)]
MEET = [("start", 360, "left"), ("run", 360, 420, 1, (0, -22)), ("box", "append", 408, 440, 420, 2, (32, 0)),
        ("crawl", 420, 380, 3, (34, 6)), ("box", "fill", 356, 380, 380, 4, (-24, 0)), ("box", "fixed", 376, 420, 400, 5, (-36, 8)),
        ("recode", 400, 616, 6, ("u", 18)), ("box", "fixed", 604, 640, 616, 7, (32, 0)),
        ("crawl", 616, 240, 8, ("u", 18)), ("box", "fixed", 222, 240, 222, 9, (-26, -12)),
        ("crawl", 222, 124, 10, ("u", 18)), ("box", "fill", 100, 124, 124, 11, (-24, 0))]

B_HALT = [("blank", 16, 40), ("r", 40, 160, "stripes", ""), ("r", 160, 220, "block", "111", 1), ("r", 220, 520, "stripes", ""),
          ("r", 520, 580, "packet", "111", 1), ("r", 580, 704, "stripes", "")]
HALT = [("start", 520), ("crawl", 520, 226, 1, ("u", 18)), ("box", "halt", 196, 226, 210, 2, (-28, -2)), ("halt",)]

SECTIONS = [
    dict(id="bounce", name="Closing in on a marker", when="Gap with a marker as the next mark",
         effect="The gap moves two cells right and the marker two cells left, so the stripes between them lose four cells.",
         cost="About three steps per cell between them: one going out, two coming back. This bounce is most of the run.",
         svg=route_svg("bounce", B_MARKER, MARKER, A_MARKER, "next bounce",
                       "One bounce: pass right to the marker, turn, carry a packet back across it and left to the gap, gap step."),
         stages=[("run", "Pass right over the stripes to the marker.", "E0 F1 repeating"),
                 ("append", "Marker turn. The marker is rebuilt two cells further left, with a packet 111 just right of it.", "E1 B1 A0 B0 C1 D0 A0 B1"),
                 ("crawl", "One carry cycle brings the packet up to the marker.", "A1 E1 B0 C0"),
                 ("fixed", "Marker pass: the packet crosses the marker, which stays where it is.", "A1 E1 B0 C1 D0"),
                 ("crawl", "Carry the packet left over the stripes to the gap.", "A1 E1 B0 C0 repeating"),
                 ("fill", "Gap step. The packet fills the gap and a new 000 opens two cells to the right. A1 hands off to the pass.", "A0 B1 A1")]),
    dict(id="wallbounce", name="Closing in on a wall or the end", when="Gap with a wall or blank tape as the next mark",
         effect="The gap moves two cells right and the wall stays put, so the stripes between them lose two cells.",
         cost="The same three steps per cell as a marker bounce, but the distance shrinks half as fast.",
         svg=route_svg("wallbounce", B_WALL, WALL, A_WALL, "next bounce",
                       "One bounce off a wall: pass right, wall turn, carry back to the gap, gap step."),
         stages=[("run", "Pass right to the wall.", "E0 F1 repeating"),
                 ("append", "Wall turn. E and F read the 00, and D writes a 1 that starts a packet. Nothing on the tape moves.", "E0 F0 D0"),
                 ("crawl", "Carry the packet left to the gap.", "A1 E1 B0 C0 repeating"),
                 ("fill", "Gap step.", "A0 B1 A1")]),
    dict(id="swap", name="Swap", when="Gap meets a marker with 4k stripe cells between them at the start",
         effect="The marker ends up just left of the gap, and the gap goes on to the next mark.",
         cost="Ends a run of marker bounces. The last bounce has no stripes left to cross.",
         svg=route_svg("swap", B_SWAP, SWAP, A_SWAP, "next mark",
                       "Swap: the marker turn's packet lands straight in the gap, so the marker is left behind."),
         stages=[("run", "With no stripes left between them, the pass crosses just the gap's last 0 and the marker's first 1.", "E0 F1"),
                 ("append", "Marker turn. Two cells left of the marker is the gap itself, so the rebuilt marker overlaps the gap's last cells.", "E1 B1 A0 B0 C1 D0 A0 B1"),
                 ("crawl", "Two carry cycles bring the packet back to what is left of the gap. No marker pass is needed.", "A1 E1 B0 C0 A1 E1 B0 C0"),
                 ("fill", "Gap step. The gap reopens one cell right of where it was, and a marker 11 now sits just left of it.", "A0 B1 A1"),
                 ("run", "Pass right to whatever mark comes next.", "E0 F1 repeating")]),
    dict(id="merge", name="Merge", when="Gap meets a marker with 4k + 2 stripe cells between them at the start",
         effect="The gap and the marker become a wall where they met, and the packet heads on to the next gap to the left.",
         cost="Mostly the long carry back, two steps per cell.",
         svg=route_svg("merge", B_MERGE, MERGE, A_MERGE, "pass right",
                       "Merge: marker turn, carry, marker pass, then the packet crosses the gap, leaving a wall, and carries on left past markers to the next gap."),
         stages=[("run", "Pass right over the last two stripe cells.", "E0 F1"),
                 ("append", "Marker turn.", "E1 B1 A0 B0 C1 D0 A0 B1"),
                 ("crawl", "One carry cycle.", "A1 E1 B0 C0"),
                 ("fixed", "Marker pass. Its D0 lands on the gap's last 0, and A0 B1 fill the gap in. The carry goes on and leaves a wall, 00, where the gap and the marker met.", "A1 E1 B0 C1 D0 A0 B1"),
                 ("crawl", "Carry left. Markers left behind by earlier swaps are in the way.", "A1 E1 B0 C0 repeating"),
                 ("fixed", "Each one is crossed with a marker pass.", "A1 E1 B0 C1 D0"),
                 ("crawl", "Carry on to the next gap.", "A1 E1 B0 C0 repeating"),
                 ("fill", "Gap step at that gap. If there is none, the packet reaches the blank tape at the left end and a new gap starts there.", "A0 B1 A1"),
                 ("run", "Pass right: the woken gap starts closing in on its next mark.", "E0 F1 repeating")]),
    dict(id="meet", name="The gap meets a wall", when="Gap step lands right next to a wall or the blank right end",
         effect="Gap and wall disappear. A shift carries the change to the next mark, here the right end, which gains a marker. The packet heads back left.",
         cost="One step per cell for the shift, two per cell for the carry back.",
         svg=route_svg("meet", B_MEET, MEET, A_MEET, None,
                       "Gap meets wall: the last bounce's gap step lands on the wall, a shift runs to the end, and a packet is carried back to the next gap."),
         stages=[("run", "The last bounce: pass right.", "E0 F1"),
                 ("append", "Wall turn.", "E0 F0 D0"),
                 ("crawl", "One carry cycle.", "A1 E1 B0 C0"),
                 ("fill", "Gap step. The new 000 lands against the wall's 00.", "A0 B1 A1"),
                 ("fixed", "E and F read 0 0 again, and D turns the head into a shift.", "E0 F0 D0"),
                 ("recode", "Shift right: every stripe moves over by one cell. That fills in the gap and the wall.", "A0 B1 repeating"),
                 ("fixed", "At the blank tape A0, B0 and D0 write three 1s. Two of them stay as the end's new marker, and the tape is one cell longer.", "A0 B0 C1 D0"),
                 ("crawl", "Carry a packet back to the left.", "A1 E1 B0 C0 repeating"),
                 ("fixed", "Marker pass at each marker on the way.", "A1 E1 B0 C1 D0"),
                 ("crawl", "Carry on to the next gap.", "A1 E1 B0 C0 repeating"),
                 ("fill", "Gap step, or a new gap at the left end.", "A0 B1 A1")]),
    dict(id="halt", name="Halt", when="A carried packet reaches a block 111",
         effect="The machine stops. This never happened in 3 billion steps.",
         cost="",
         svg=route_svg("halt", B_HALT, HALT, None, None,
                       "Halt: the carry reaches a block, C reads a 1 and so does D. D1 is the halt."),
         stages=[("crawl", "Carry left toward the block.", "A1 E1 B0 C0 repeating"),
                 ("halt", "At the block, C reads one of its 1s and D the next. D has no rule for reading 1.", "A1 E1 B0 C1 D1")]),
]

def section_html(sec):
    lis = "".join(stage_li(k, esc(t), r) for k, t, r in sec["stages"])
    cost = f'<p class="cost">{esc(sec["cost"])}</p>' if sec["cost"] else ""
    return f'''
    <section class="route-sec" id="{sec["id"]}" aria-labelledby="h-{sec["id"]}">
      <div class="rhead"><h3 id="h-{sec["id"]}">{sec["name"]}</h3><span class="when">{esc(sec["when"])}</span></div>
      <div class="rbody">
        <figure class="rfig"><div class="scroll">{sec["svg"]}</div></figure>
        <div class="rtext"><p class="effect">{esc(sec["effect"])}</p>{cost}<ol class="stages">{lis}</ol></div>
      </div>
    </section>'''

# ---------------------------------------------------------------- the marks (layout strip at step 4,264)
def layout_strip():
    lo, hi = content(4264)
    f = frame(4264, lo, hi)
    s = f["cells"]
    cuts = [(0, 1, "end"), (1, 4, "gap"), (4, 16, "stripes"), (16, 19, "packet"), (19, 28, "stripes"),
            (28, 30, "marker"), (30, 42, "stripes"), (42, 44, "wall"), (44, len(s), "stripes")]
    parts = [(s[a:b], lab) for a, b, lab in cuts]
    assert [p for p, _ in parts][1:8:2] == ["000", "111", "11", "00"] and f["head"] == 16, (s, f["head"])
    for p, lab in parts:
        if lab == "stripes": assert "00" not in p and "11" not in p, p
    out, i = [], 0
    for pat, lab in parts:
        cs = []
        for c in pat:
            cls = "c" + (" z" if c == "0" else "") + (" h crawl" if i == f["head"] else "")
            cs.append(f'<span class="{cls}">{c}</span>')
            i += 1
        mark = " mk" if lab in ("gap", "marker", "wall") else (" pk" if lab == "packet" else "")
        out.append(f'<span class="g{mark}"><span class="gc wrapd">{"".join(cs)}</span><span class="gl">{esc(lab)}</span></span>')
    out.append('<span class="g"><span class="gc"><span class="c ghost2">…</span></span><span class="gl">blank</span></span>')
    return f'<div class="strip"><span class="tape multi">{"".join(out)}</span></div>'

# ---------------------------------------------------------------- when marks meet
MEETS = [
    ("crawl", "Carrying a packet left", [
        ("a gap 000", "Gap step: the gap moves two cells right and the head turns right.", "A0 B1 A1"),
        ("a marker 11", "Marker pass: the packet crosses and the marker stays put.", "A1 E1 B0 C1 D0"),
        ("a wall 00", "The wall becomes a marker with a gap just right of it, and the head turns right.", "A0 B1 A1"),
        ("blank tape at the left end", "A new gap starts there, and the tape is two cells longer.", "A0 B1 A1"),
        ("a block 111", "Halt. Never seen in the run.", "A1 E1 B0 C1 D1"),
    ]),
    ("run", "Passing right", [
        ("a marker 11", "Marker turn: the marker moves two cells left and the head comes back with a packet.", "E1 B1 A0 B0 C1 D0 A0 B1"),
        ("a wall 00, or blank tape", "Wall turn: nothing moves, and the head comes back with a packet.", "E0 F0 D0"),
        ("a block 111", "The block becomes a wall, and a shift starts from there.", "E1 B1, then A0 B1 repeating"),
    ]),
    ("fill", "After a gap step", [
        ("a wall right next to the gap", "Gap and wall run together, and a shift starts from there.", "A1 E0 F0 D0, then A0 B1 repeating"),
    ]),
    ("recode", "Shifting right", [
        ("a marker 11", "The marker is used up. A gap opens where it was, and the head passes right from there.", "A1, then E0 F1"),
        ("a wall 00", "The wall becomes a block, and the head comes back with a packet.", "A0 B0 C1 D0"),
        ("blank tape at the right end", "The end gains a marker, and the head comes back with a packet.", "A0 B0 C1 D0, or A1 E0 F0 D0 A0 B1 A0 B0 C1 D0"),
    ]),
    ("append", "Gap and marker closing in", [
        ("each other, 4k stripe cells apart at the start", "Swap: the marker ends up just left of the gap, which goes on.", "marker turn, two carry cycles, gap step"),
        ("each other, 4k + 2 cells apart", "Merge: they become a wall, and the packet goes on to the next gap to the left.", "marker turn, carry cycle, A1 E1 B0 C1 D0 A0 B1"),
    ]),
]
def meets_html():
    rows = []
    for kind, head, items in MEETS:
        for i, (at, what, rules) in enumerate(items):
            first = f'<th scope="rowgroup" rowspan="{len(items)}">{chip(kind, head)}</th>' if i == 0 else ""
            rows.append(f'<tr>{first}<td class="at">{esc(at)}</td><td>{esc(what)}</td><td class="mono">{esc(rules)}</td></tr>')
    return ('<div class="scroll"><table class="meets"><thead><tr><th scope="col">The head is</th><th scope="col">and reaches</th>'
            '<th scope="col">What happens</th><th scope="col">Rules</th></tr></thead><tbody>' + "".join(rows) + '</tbody></table></div>')

# ---------------------------------------------------------------- to-scale maps (every step)
def step_map(name, a, b, cw, ys, x_lo, x_hi, stages, bottom_parts, aria, start_label, labels_right=True, W2=760):
    pos = TRACES[name]["pos"]; keys = TRACES[name]["key"]
    N = b - a
    kind, _, _ = classify(keys)
    X0, Y0 = 44.0, 34.0
    X = lambda p: X0 + (p - x_lo + 0.5) * cw
    Y = lambda i: Y0 + i * ys
    xr = X0 + (x_hi - x_lo + 1) * cw
    parts = []
    for c in range(x_lo, x_hi + 1):           # tape history: vertical runs of 1s
        i = 0
        while i <= N:
            if SNAPS[a + i]["t"].get(c, 0):
                j = i
                while j + 1 <= N and SNAPS[a + j + 1]["t"].get(c, 0): j += 1
                parts.append(f'<rect class="sv-tape" x="{X(c) - cw / 2 + 1:.1f}" y="{Y(i):.1f}" width="{cw - 2:.1f}" height="{max(ys, (j - i + 1) * ys):.1f}"/>')
                i = j + 1
            else:
                i += 1
    for k, (st, label) in enumerate(stages):
        i = st - a
        y = Y(i)
        if 0 < i < N:
            parts.append(f'<line class="sv-sep" x1="{X0 - 6}" y1="{y:.1f}" x2="{W2 - 8}" y2="{y:.1f}"/>')
        parts.append(f'<text class="sv-axis" x="{X0 - 10}" y="{y + 3.5:.1f}" text-anchor="end">{fmt(st)}</text>')
    parts.append(f'<text class="sv-axis" x="{X0 - 10}" y="{Y(N) + 3.5:.1f}" text-anchor="end">{fmt(b)}</text>')
    for k in range(len(stages)):
        y1 = Y(stages[k][0] - a); y2 = Y((stages[k + 1][0] if k + 1 < len(stages) else b) - a)
        ym = (y1 + y2) / 2; bx = xr + 22
        parts.append(f'<circle class="sv-badge" cx="{bx:.1f}" cy="{ym:.1f}" r="8.5"/><text class="sv-num" x="{bx:.1f}" y="{ym + 3.7:.1f}" text-anchor="middle">{k + 1}</text>')
        parts.append(f'<text class="sv-lab strong" x="{bx + 14:.1f}" y="{ym + 4.2:.1f}">{esc(stages[k][1])}</text>')
    parts.append(f'<text class="sv-tag" x="{X0 - 10}" y="{Y0 - 14:.1f}" text-anchor="end">step</text>')
    i = 0
    while i < N:
        j = i
        while j + 1 < N and kind[j + 1] == kind[i]: j += 1
        k = kind[i]
        x1, y1, x2, y2 = X(pos[i]), Y(i), X(pos[j + 1]), Y(j + 1)
        if k in ("fill", "append", "fixed", "halt"):
            pa, pb = min(pos[i:j + 2]), max(pos[i:j + 2])
            parts.append(f'<rect class="sv-box thin {k}" x="{X(pa) - cw / 2 + 1:.1f}" y="{y1:.1f}" width="{(pb - pa + 1) * cw - 2:.1f}" height="{max(2.5, y2 - y1):.1f}" rx="1.5"/>')
        elif k == "crawl":
            if abs(x2 - x1) + abs(y2 - y1) < 5:
                parts.append(f'<line class="sv-path crawl" x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}"/>')
            else:
                parts.append(f'<polyline class="sv-path crawl" points="{zigzag(x1, y1, x2, y2, 5.0, 2.0)}"/>')
        else:
            parts.append(f'<line class="sv-path {k} thin" x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}"/>')
            if k == "recode" and math.hypot(x2 - x1, y2 - y1) > 12:
                parts.append(ticks(x1, y1, x2, y2, 8.0, 2.4))
        i = j + 1
    parts.append(f'<circle class="sv-start" cx="{X(pos[0]):.1f}" cy="{Y(0):.1f}" r="4"/><text class="sv-lab" x="{X(pos[0]) + 9:.1f}" y="{Y(0) - 6:.1f}">{esc(start_label)}</text>')
    parts.append(f'<circle class="sv-end" cx="{X(pos[N]):.1f}" cy="{Y(N):.1f}" r="4"/>')
    yb = Y(N) + 26
    H = yb
    if bottom_parts:
        regs = [(kind_, X(p1) - cw / 2, X(p2) + cw / 2, *rest) for kind_, p1, p2, *rest in bottom_parts]
        parts.append(band(regs, yb, f"tape after step {fmt(b)}"))
        H = yb + 44
    return (f'<svg class="route wmap-svg" viewBox="0 0 {W2} {H:.0f}" role="img" aria-label="{esc(aria)}">' + "".join(parts) + "</svg>")

LEGEND = f'''<span class="legend" aria-label="Legend">
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><polyline class="sv-path crawl" points="{zigzag(2, 6, 42, 6, 5, 3)}"/></svg>Carry left</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><line class="sv-path run" x1="2" y1="6" x2="42" y2="6"/></svg>Pass right</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><line class="sv-path recode" x1="2" y1="6" x2="42" y2="6"/>{ticks(2, 6, 42, 6, 9, 3.5)}</svg>Shift right</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><rect class="sv-box fill" x="8" y="1" width="28" height="10" rx="3"/></svg>Gap step</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><rect class="sv-box append" x="8" y="1" width="28" height="10" rx="3"/></svg>Turn</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><rect class="sv-box fixed" x="8" y="1" width="28" height="10" rx="3"/></svg>Other fixed sequence</span>
        </span>'''

EX_STAGES = [(4180, "Merge"), (4215, "Carry back over a marker"), (4292, "Gap wakes: 6 bounces"),
             (4595, "Merge again"), (4618, "Carry to the end: new gap"), (4657, "Closing in on the wall")]

def example_map():
    lo, hi = -33, 23
    svg = step_map("example", 4180, 4700, 9.0, 0.78, lo, hi, EX_STAGES,
                   [("blank", -33, -33), ("r", -32, -32, "", ""), ("r", -31, -29, "gap", "", 1), ("r", -28, -27, "", ""),
                    ("r", -26, -24, "", "", 1), ("r", -23, -14, "stripes", ""), ("r", -13, -12, "", "", 1),
                    ("r", -11, 11, "stripes", ""), ("r", 12, 13, "", "", 1), ("r", 14, 22, "stripes", "")],
                   "Steps 4,180 to 4,700 drawn to scale, one row per step and one column per cell, with the head path coloured by routine.",
                   "step 4,180")
    return svg

SETUP_STAGES = [(0, "Write 111"), (4, "First stripe"), (6, "Carry"), (14, "First gap"), (17, "Pass and wall turn"),
                (22, "Carry"), (26, "Gap step"), (29, "Gap meets the end"), (32, "Shift"), (34, "End marker"), (38, "Carry")]

# ---------------------------------------------------------------- big picture (coarse, one cycle)
def turning_points(pos, hyst=3):
    pts = [(0, pos[0])]
    d = 0; ext_i = 0
    for i in range(1, len(pos)):
        p = pos[i]
        if d >= 0:
            if p >= pos[ext_i]: ext_i = i; d = 1 if p > pos[pts[-1][0]] else d
            elif pos[ext_i] - p >= hyst and d == 1:
                pts.append((ext_i, pos[ext_i])); d = -1; ext_i = i
            elif d == 0 and pos[pts[-1][0]] - p >= hyst: d = -1; ext_i = i
        if d < 0:
            if p <= pos[ext_i]: ext_i = i
            elif p - pos[ext_i] >= hyst:
                pts.append((ext_i, pos[ext_i])); d = 1; ext_i = i
    pts.append((len(pos) - 1, pos[-1]))
    return pts

def cycle_map():
    a, b = 43385, 79549
    pos = TRACES["cycle"]["pos"]
    keys = TRACES["cycle"]["key"]
    kind, _, _ = classify(keys)
    lo = min(pos) - 1; hi = max(pos) + 1
    W2 = 760; X0, Y0 = 50.0, 30.0
    cw = 600.0 / (hi - lo + 1)
    ys = 700.0 / (b - a)
    X = lambda p: X0 + (p - lo + 0.5) * cw
    Y = lambda i: Y0 + i * ys
    pts = turning_points(pos, 4)
    parts = []
    # faint full head path
    parts.append('<polyline class="cm-path" points="' + " ".join(f"{X(p):.1f},{Y(i):.1f}" for i, p in pts) + '"/>')
    # carries back to the left (much longer than the pass before them) and shifts, drawn solid
    runs = []
    i = 0
    while i < len(kind) - 1:
        j = i
        while j + 1 < len(kind) - 1 and (kind[j + 1] == kind[i] or (kind[i] == "crawl" and kind[j + 1] == "fixed" and j + 6 < len(kind) and kind[j + 6] == "crawl")):
            j += 1
        runs.append((kind[i], i, j + 1))
        i = j + 1
    last_pass = 0
    for kd, i, j in runs:
        if kd == "run": last_pass = pos[j] - pos[i]
        if kd == "crawl" and pos[i] - pos[j] > last_pass + 16:
            parts.append(f'<line class="sv-path crawl cm-long" x1="{X(pos[i]):.1f}" y1="{Y(i):.1f}" x2="{X(pos[j]):.1f}" y2="{Y(j):.1f}"/>')
        if kd == "recode" and pos[j] - pos[i] > 20:
            parts.append(f'<line class="sv-path recode cm-long" x1="{X(pos[i]):.1f}" y1="{Y(i):.1f}" x2="{X(pos[j]):.1f}" y2="{Y(j):.1f}"/>')
    # tracks of left turns (the gap) and right turns (marker, wall or end), broken at jumps
    for side, cls in ((0, "cm-gap"), (1, "cm-right")):
        tps = [(i, p) for k, (i, p) in enumerate(pts[1:-1], 1) if (p < pts[k - 1][1]) == (side == 0) and (p < pts[k + 1][1]) == (side == 0)]
        line = []
        for i, p in tps:
            if line and (abs(p - line[-1][1]) > 6 or i - line[-1][0] > 1200):
                if len(line) > 1:
                    parts.append(f'<polyline class="{cls}" points="' + " ".join(f"{X(q):.1f},{Y(j):.1f}" for j, q in line) + '"/>')
                line = []
            line.append((i, p))
        if len(line) > 1:
            parts.append(f'<polyline class="{cls}" points="' + " ".join(f"{X(q):.1f},{Y(j):.1f}" for j, q in line) + '"/>')
    # sub-cycles start where a new gap is born at the left end (the left edge moves)
    m_lo = 0; starts = [0]; run_lo = pos[0]
    for k in range(1, len(pos)):
        if pos[k] < run_lo:
            if pos[k] < run_lo - 1 or True:
                if k - starts[-1] > 200: starts.append(k)
            run_lo = pos[k]
    starts = [next(q for q in range(k, len(kind)) if kind[q] == "run") for k in starts]
    for n, s in enumerate(starts):
        y = Y(s)
        if n:
            parts.append(f'<line class="sv-sep" x1="{X0 - 6}" y1="{y:.1f}" x2="{W2 - 8}" y2="{y:.1f}"/>')
            parts.append(f'<text class="sv-axis" x="{X0 - 10}" y="{y + 3.5:.1f}" text-anchor="end">{fmt(a + s)}</text>')
        else:
            parts.append(f'<text class="sv-axis" x="{X0 - 10}" y="{Y(0) + 3.5:.1f}" text-anchor="end">{fmt(a)}</text>')
        e = starts[n + 1] if n + 1 < len(starts) else len(pos) - 1
        ym = (Y(s) + Y(e)) / 2
        bx = X(hi) + 26
        parts.append(f'<circle class="sv-badge" cx="{bx:.1f}" cy="{ym:.1f}" r="8.5"/><text class="sv-num" x="{bx:.1f}" y="{ym + 3.7:.1f}" text-anchor="middle">{n + 1}</text>')
    parts.append(f'<text class="sv-axis" x="{X0 - 10}" y="{Y(len(pos) - 1) + 3.5:.1f}" text-anchor="end">{fmt(b)}</text>')
    parts.append(f'<text class="sv-tag" x="{X0 - 10}" y="{Y0 - 12:.1f}" text-anchor="end">step</text>')
    H = Y(len(pos) - 1) + 24
    svg = (f'<svg class="route cmap-svg" viewBox="0 0 {W2} {H:.0f}" role="img" aria-label="One whole cycle, steps 43,385 to 79,549, drawn to scale: the head bounces between the gap and the next mark, and each new gap meets the markers left by the one before at half the distance.">'
           + "".join(parts) + "</svg>")
    return svg, [a + s for s in starts]

CYCLE_SVG, CYCLE_STARTS = cycle_map()

def countdown_chart():
    """The 2^200 hand-built halting run: left countdown size and end distance at each pass start."""
    import json
    ps = json.load(open(os.path.join(D, "mix200r_passes.json")))
    W, H = 640, 300; L0, R0, T0, B0 = 46, 18, 22, 40
    X = lambda m: L0 + (W - L0 - R0) * m / 200.0
    Y = lambda v: T0 + (H - T0 - B0) * (1 - v / 220.0)
    parts = []
    for v in (0, 50, 100, 150, 200):
        parts.append(f'<line class="cd-grid" x1="{L0}" y1="{Y(v):.1f}" x2="{W - R0}" y2="{Y(v):.1f}"/>'
                     f'<text class="cd-tick" x="{L0 - 8}" y="{Y(v) + 4:.1f}" text-anchor="end">{v}</text>')
    for m in (0, 50, 100, 150, 200):
        parts.append(f'<text class="cd-tick" x="{X(m):.1f}" y="{H - B0 + 18}" text-anchor="middle">{m}</text>')
    parts.append(f'<text class="cd-axis" x="{(L0 + W - R0) / 2:.0f}" y="{H - 4}" text-anchor="middle">meetings in the run</text>')
    parts.append(f'<text class="cd-axis" x="12" y="{(T0 + H - B0) / 2:.0f}" text-anchor="middle" transform="rotate(-90 12 {(T0 + H - B0) / 2:.0f})">binary digits (log₂)</text>')
    # detour band
    parts.append(f'<rect class="cd-band" x="{X(96):.1f}" y="{T0}" width="{X(100) - X(96):.1f}" height="{H - T0 - B0}"/>'
                 f'<text class="cd-note" x="{X(98):.1f}" y="{T0 - 6}" text-anchor="middle">detour</text>')
    # projection of the first stretch: size falls 1.5 digits per meeting until it reaches 0
    m_end = 96 + ps[12]["L"] / 1.5 if False else None
    first = [r for r in ps if r["m"] <= 96]; second = [r for r in ps if r["m"] >= 100]
    slope = (first[0]["L"] - first[-1]["L"]) / (first[-1]["m"] - first[0]["m"])
    m0 = first[0]["m"] + first[0]["L"] / slope
    parts.append(f'<line class="cd-proj" x1="{X(first[-1]["m"]):.1f}" y1="{Y(first[-1]["L"]):.1f}" x2="{X(m0):.1f}" y2="{Y(0):.1f}"/>')
    parts.append(f'<circle class="cd-end" cx="{X(m0):.1f}" cy="{Y(0):.1f}" r="4"/>'
                 f'<text class="cd-note" x="{X(m0) + 8:.1f}" y="{Y(0) - 26:.1f}">one stretch could</text>'
                 f'<text class="cd-note" x="{X(m0) + 8:.1f}" y="{Y(0) - 12:.1f}">go no further</text>')
    pts = " ".join(f"{X(r['m']):.1f},{Y(r['L']):.1f}" for r in ps)
    parts.append(f'<polyline class="cd-L" points="{pts}"/>')
    rpts = " ".join(f"{X(r['m']):.1f},{Y(r['R']):.1f}" for r in ps)
    parts.append(f'<polyline class="cd-R" points="{rpts}"/>')
    parts.append(f'<text class="cd-lab" x="{X(8):.1f}" y="{Y(first[0]["L"]) - 8:.1f}">left countdown</text>')
    parts.append(f'<text class="cd-lab" x="{X(150):.1f}" y="{Y(62):.1f}">distance to the end</text>')
    parts.append(f'<line class="cd-cross" id="cd-cross" x1="0" y1="{T0}" x2="0" y2="{H - B0}" visibility="hidden"/>')
    parts.append(f'<rect class="cd-hit" x="{L0}" y="{T0}" width="{W - L0 - R0}" height="{H - T0 - B0}"/>')
    data = json.dumps([[r["m"], r["L"], r["R"]] for r in ps])
    svg = (f'<svg class="cd-svg" id="cd-svg" viewBox="0 0 {W} {H}" role="img" data-x0="{L0}" data-x1="{W - R0}" '
           f'aria-label="Along the 197-meeting run, the distance to the end falls one binary digit per meeting from 197 to 0. '
           f'The left countdown falls six digits per pass from 206 to 62, jumps back to 203 at the detour, and falls again to 59. '
           f'Without the detour its size would reach zero at meeting 137, with the end still 2^60 cells away.">'
           + "".join(parts) + "</svg>")
    rows = "".join(f"<tr><th scope=\"row\">{r['m']}</th><td>{r['L']:.1f}</td><td>{r['R']:.0f}</td></tr>" for r in ps)
    table = (f'<details class="cd-data"><summary>The numbers</summary><table class="clean quick"><thead><tr><th scope="col">Meeting</th>'
             f'<th scope="col">log₂ of the countdown</th><th scope="col">log₂ of the distance</th></tr></thead><tbody>{rows}</tbody></table></details>')
    return svg, data, table

CD_SVG, CD_DATA, CD_TABLE = countdown_chart()

def odds_chart():
    """Share of random GMM states whose closest right-end meeting is at least h halvings from the full width."""
    import json
    od = json.load(open(os.path.join(D, "odds48.json")))
    W, H = 640, 300; L0, R0, T0, B0 = 58, 18, 18, 40
    X = lambda h: L0 + (W - L0 - R0) * (h - 2.5) / 10.0
    Y = lambda v: T0 + (H - T0 - B0) * (-v) / 30.0
    sup = {0: '⁰', 10: '⁻¹⁰', 20: '⁻²⁰', 30: '⁻³⁰'}
    parts = []
    for v in (0, -10, -20, -30):
        parts.append(f'<line class="cd-grid" x1="{L0}" y1="{Y(v):.1f}" x2="{W - R0}" y2="{Y(v):.1f}"/>'
                     f'<text class="cd-tick" x="{L0 - 8}" y="{Y(v) + 4:.1f}" text-anchor="end">2{sup[-v]}</text>')
    for h in range(3, 13):
        parts.append(f'<text class="cd-tick" x="{X(h):.1f}" y="{H - B0 + 18}" text-anchor="middle">{h}</text>')
    parts.append(f'<text class="cd-axis" x="{(L0 + W - R0) / 2:.0f}" y="{H - 4}" text-anchor="middle">halvings from the full width to the closest meeting, at least</text>')
    parts.append(f'<text class="cd-axis" x="12" y="{(T0 + H - B0) / 2:.0f}" text-anchor="middle" transform="rotate(-90 12 {(T0 + H - B0) / 2:.0f})">share of states</text>')
    for key, cls in (("plane", "cd-R"), ("line", "cd-L")):
        pts = " ".join(f"{X(h):.1f},{Y(v):.1f}" for h, c, v in od[key])
        parts.append(f'<polyline class="{cls}" points="{pts}"/>')
        for h, c, v in od[key]:
            parts.append(f'<circle class="od-dot {cls}d" cx="{X(h):.1f}" cy="{Y(v):.1f}" r="4"/>')
    p = od["plane"]; l = od["line"]
    parts.append(f'<text class="cd-lab" x="{X(9.2):.1f}" y="{Y(p[6][2]) - 12:.1f}">all two-marker states</text>')
    parts.append(f'<text class="cd-lab" x="{X(3.0):.1f}" y="{Y(-19.5):.1f}">the machine\'s own</text>')
    parts.append(f'<line class="cd-cross" id="od-cross" x1="0" y1="{T0}" x2="0" y2="{H - B0}" visibility="hidden"/>')
    parts.append(f'<rect class="cd-hit" x="{L0}" y="{T0}" width="{W - L0 - R0}" height="{H - T0 - B0}"/>')
    data = json.dumps({"plane": {str(h): [c, v] for h, c, v in p}, "line": {str(h): [c, v] for h, c, v in l}})
    svg = (f'<svg class="cd-svg" id="od-svg" viewBox="0 0 {W} {H}" role="img" data-x0="{L0}" data-x1="{W - R0}" '
           f'aria-label="Share of random two-marker states whose closest right-end meeting is at least h halvings from the full width, '
           f'for h from 3 to 12. Both curves fall about 2.5 binary digits per halving. For all such states the share is 2 to the minus 8.6 at h = 4 '
           f'and 2 to the minus 28.3 at h = 12; for the states the machine actually reaches it is 2 to the minus 13.5 at h = 4 and 2 to the minus 27.3 at h = 10, '
           f'20 to 30 times smaller at every h.">' + "".join(parts) + "</svg>")
    hs = sorted({h for h, c, v in p} | {h for h, c, v in l})
    pd = {h: (c, v) for h, c, v in p}; ld = {h: (c, v) for h, c, v in l}
    cell = lambda d, h: f"{d[h][0]:,} (2<sup>{d[h][1]:.1f}</sup>)" if h in d else "none"
    rows = "".join(f"<tr><th scope=\"row\">{h}</th><td>{cell(pd, h)}</td><td>{cell(ld, h)}</td></tr>" for h in hs)
    table = (f'<details class="cd-data"><summary>The numbers</summary><table class="clean quick"><thead><tr><th scope="col">h at least</th>'
             f'<th scope="col">All two-marker states, of 10⁹</th><th scope="col">The machine\'s own, of 10⁹</th></tr></thead><tbody>{rows}</tbody></table></details>')
    return svg, data, table

OD_SVG, OD_DATA, OD_TABLE = odds_chart()

def seg_chart():
    """Odds that a segment gets within 2^-4 of the width, given that the cycle reaches that segment."""
    import json, math
    sd = json.load(open(os.path.join(D, "segodds.json")))
    W, H = 640, 300; L0, R0, T0, B0 = 58, 18, 18, 46
    X = lambda r: L0 + (W - L0 - R0) * (r + 0.5) / 9.0
    lo, hi = -24.0, -6.0
    Y = lambda v: T0 + (H - T0 - B0) * (hi - v) / (hi - lo)
    sup = {6: '⁻⁶', 10: '⁻¹⁰', 14: '⁻¹⁴', 18: '⁻¹⁸', 22: '⁻²²'}
    parts = []
    for v in (-6, -10, -14, -18, -22):
        parts.append(f'<line class="cd-grid" x1="{L0}" y1="{Y(v):.1f}" x2="{W - R0}" y2="{Y(v):.1f}"/>'
                     f'<text class="cd-tick" x="{L0 - 8}" y="{Y(v) + 4:.1f}" text-anchor="end">2{sup[-v]}</text>')
    ords = ['1st', '2nd', '3rd', '4th', '5th', '6th', '7th', '8th', '9th']
    for r in range(9):
        parts.append(f'<text class="cd-tick" x="{X(r):.1f}" y="{H - B0 + 18}" text-anchor="middle">{ords[r]}</text>')
    parts.append(f'<text class="cd-axis" x="{(L0 + W - R0) / 2:.0f}" y="{H - 6}" text-anchor="middle">segment of the cycle (between returns to a two-marker state)</text>')
    parts.append(f'<text class="cd-axis" x="12" y="{(T0 + H - B0) / 2:.0f}" text-anchor="middle" transform="rotate(-90 12 {(T0 + H - B0) / 2:.0f})">odds of coming within 2⁻⁴</text>')
    rows = {}
    for key, cls in (("plane", "cd-R"), ("line", "cd-L")):
        pts = [(r, h, n) for r, h, n in sd[key] if h > 0]
        parts.append(f'<polyline class="{cls}" points="' + " ".join(f"{X(r):.1f},{Y(math.log2(h / n)):.1f}" for r, h, n in pts) + '"/>')
        for r, h, n in pts:
            parts.append(f'<circle class="od-dot {cls}d" cx="{X(r):.1f}" cy="{Y(math.log2(h / n)):.1f}" r="4"/>')
        for r, h, n in sd[key]: rows.setdefault(r, {})[key] = (h, n)
    # the machine's first segment: proved never
    yb = H - B0 - 4
    parts.append(f'<circle class="od-dot od-never" cx="{X(0):.1f}" cy="{yb:.1f}" r="4"/>'
                 f'<text class="cd-note" x="{X(0) + 10:.1f}" y="{yb - 4:.1f}">never (proved)</text>')
    parts.append(f'<text class="cd-lab" x="{X(4.6):.1f}" y="{Y(-9.4) - 12:.1f}">a random two-marker state</text>')
    parts.append(f'<text class="cd-lab" x="{X(1.25):.1f}" y="{Y(-20.5):.1f}">the machine\'s own</text>')
    parts.append(f'<line class="cd-cross" id="sg-cross" x1="0" y1="{T0}" x2="0" y2="{H - B0}" visibility="hidden"/>')
    parts.append(f'<rect class="cd-hit" x="{L0}" y="{T0}" width="{W - L0 - R0}" height="{H - T0 - B0}"/>')
    data = json.dumps({str(r): {k: list(v) for k, v in d.items()} for r, d in rows.items()})
    svg = (f'<svg class="cd-svg" id="sg-svg" viewBox="0 0 {W} {H}" role="img" data-x0="{L0}" data-x1="{W - R0}" '
           f'aria-label="For each segment of a cycle, the odds that it comes within 2 to the minus 4 of the width, among cycles that reach it. '
           f'From a random two-marker state the odds stay near 1.5 in 1,000 for every segment. On the machine\'s own tapes the first segment never does, '
           f'the second about 4 in 10 million, the third 2.7 in 10,000, then 6.7, 6.1, 8.1, 10.7, 15 and 21 in 10,000 for the fourth to ninth.">' + "".join(parts) + "</svg>")
    trs = ""
    for r in range(9):
        cells = []
        for key in ("plane", "line"):
            h, n = rows[r][key]
            cells.append(f"{h:,} of {n:,}" + (f" (2<sup>{math.log2(h / n):.1f}</sup>)" if h else (" (proved never)" if key == "line" and r == 0 else "")))
        trs += f"<tr><th scope=\"row\">{ords[r]}</th><td>{cells[0]}</td><td>{cells[1]}</td></tr>"
    table = (f'<details class="cd-data"><summary>The numbers</summary><table class="clean quick"><thead><tr><th scope="col">Segment</th>'
             f'<th scope="col">Random two-marker states</th><th scope="col">The machine\'s own</th></tr></thead><tbody>{trs}</tbody></table></details>')
    return svg, data, table

SG_SVG, SG_DATA, SG_TABLE = seg_chart()

def stair_chart():
    """The machine's tail (share of even n whose cycle comes within 2^-x of the end) as a staircase of lines."""
    import json, math
    sd = json.load(open(os.path.join(D, "lines_stair.json")))
    W, H = 640, 300; L0, R0, T0, B0 = 58, 22, 18, 40
    X = lambda h: L0 + (W - L0 - R0) * (h - 4) / 10.5
    lo, hi = -42.0, -12.0
    Y = lambda v: T0 + (H - T0 - B0) * (hi - v) / (hi - lo)
    sup = {15: '⁻¹⁵', 20: '⁻²⁰', 25: '⁻²⁵', 30: '⁻³⁰', 35: '⁻³⁵', 40: '⁻⁴⁰'}
    parts = []
    for v in (-15, -20, -25, -30, -35, -40):
        parts.append(f'<line class="cd-grid" x1="{L0}" y1="{Y(v):.1f}" x2="{W - R0}" y2="{Y(v):.1f}"/>'
                     f'<text class="cd-tick" x="{L0 - 8}" y="{Y(v) + 4:.1f}" text-anchor="end">2{sup[-v]}</text>')
    for h in range(4, 15):
        parts.append(f'<text class="cd-tick" x="{X(h):.1f}" y="{H - B0 + 18}" text-anchor="middle">{h}</text>')
    parts.append(f'<text class="cd-axis" x="{(L0 + W - R0) / 2:.0f}" y="{H - 4}" text-anchor="middle">halvings from the full width to the closest meeting, at least</text>')
    parts.append(f'<text class="cd-axis" x="12" y="{(T0 + H - B0) / 2:.0f}" text-anchor="middle" transform="rotate(-90 12 {(T0 + H - B0) / 2:.0f})">share of even n</text>')
    g = sd["grid"]
    cls = ["st-a", "st-b", "st-c"]
    names = ["line 1", "line 2", "line 3"]
    for k, ln in enumerate(sd["lines"]):
        pts = [(x, y) for x, y in zip(g, ln["ys"]) if y > 0 and x <= ln["reach"]]
        parts.append(f'<polyline class="{cls[k]}" points="' + " ".join(f"{X(x):.1f},{Y(math.log2(y)):.1f}" for x, y in pts) + '"/>')
        xe, ye = pts[-1]
        parts.append(f'<line class="{cls[k]} st-end" x1="{X(xe):.1f}" y1="{Y(math.log2(ye)) - 7:.1f}" x2="{X(xe):.1f}" y2="{Y(math.log2(ye)) + 7:.1f}"/>')
    pts = [(x, y) for x, y in zip(g, sd["total"]) if y > 0 and x <= 14.25]
    parts.append('<polyline class="cd-L st-tot" points="' + " ".join(f"{X(x):.1f},{Y(math.log2(y)):.1f}" for x, y in pts) + '"/>')
    for x, y in pts:
        if abs(x - round(x)) < 1e-9:
            parts.append(f'<circle class="od-dot cd-Ld" cx="{X(x):.1f}" cy="{Y(math.log2(y)):.1f}" r="4"/>')
    # direct labels at the right edge / at each line's end
    lab = [(sd["lines"][0], "line 1 stops at 10.4"), (sd["lines"][1], "line 2 stops at 12.5"), (sd["lines"][2], "line 3 stops at 14.1")]
    for k, (ln, t) in enumerate(lab):
        pts = [(x, y) for x, y in zip(g, ln["ys"]) if y > 0 and x <= ln["reach"]]
        xe, ye = pts[-1]
        if k == 2: parts.append(f'<text class="cd-note st-lab" x="{X(xe) - 6:.1f}" y="{Y(math.log2(ye)) + 16:.1f}" text-anchor="end">{t}</text>')
        else: parts.append(f'<text class="cd-note st-lab" x="{X(xe) + 8:.1f}" y="{Y(math.log2(ye)) - 6:.1f}">{t}</text>')
    xt, yt = pts[-1] if False else (g[-1], sd["total"][-1])
    parts.append(f'<text class="cd-lab" x="{X(5.0):.1f}" y="{Y(-13.3):.1f}">the machine\'s own, all lines</text>')
    parts.append(f'<line class="cd-cross" id="st-cross" x1="0" y1="{T0}" x2="0" y2="{H - B0}" visibility="hidden"/>')
    parts.append(f'<rect class="cd-hit" x="{L0}" y="{T0}" width="{W - L0 - R0}" height="{H - T0 - B0}"/>')
    ix = {round(x): i for i, x in enumerate(g) if abs(x - round(x)) < 1e-9}
    data = {str(h): [sd["total"][i]] + [ln["ys"][i] if g[i] <= ln["reach"] else 0 for ln in sd["lines"]] for h, i in ix.items() if 4 <= h <= 14}
    svg = (f'<svg class="cd-svg" id="st-svg" viewBox="0 0 {W} {H}" role="img" data-x0="{L0}" data-x1="{W - R0}" '
           f'aria-label="The share of even n whose cycle comes within 2 to the minus x of the end, for x from 4 to 14, falls from 2 to the minus 13.5 to 2 to the minus 38.7. '
           f'Three lines of two-marker states carry most of it in turn: line 1 carries 79% at x = 10 and stops at 10.4 halvings, line 2 about half at x = 11 and 12 and stops at 12.5, '
           f'line 3 40% at x = 14 and stops at 14.1. Each falls about 6 binary digits per 4 halvings until it stops.">' + "".join(parts) + "</svg>")
    rows = ""
    for h in range(4, 15):
        d = data[str(h)]
        cell = lambda v: (f"2<sup>{math.log2(v):.1f}</sup> ({v / d[0]:.0%})" if v > 0 else "none")
        rows += f"<tr><th scope=\"row\">{h}</th><td>2<sup>{math.log2(d[0]):.1f}</sup></td><td>{cell(d[1])}</td><td>{cell(d[2])}</td><td>{cell(d[3])}</td></tr>"
    table = (f'<details class="cd-data"><summary>The numbers</summary><table class="clean quick"><thead><tr><th scope="col">x at least</th>'
             f'<th scope="col">All lines</th><th scope="col">Line 1</th><th scope="col">Line 2</th><th scope="col">Line 3</th></tr></thead><tbody>{rows}</tbody></table></details>')
    return svg, json.dumps(data), table

ST_SVG, ST_DATA, ST_TABLE = stair_chart()


# ---------------------------------------------------------------- setup
def setup_rows():
    keys = TRACES["setup"]["key"]
    kinds, _, _ = classify(keys)
    rows = []
    bounds = [s for s, _ in SETUP_STAGES] + [46]
    for k, (st, label) in enumerate(SETUP_STAGES):
        e = bounds[k + 1] - 1
        if st == 38: e = 45
        kd = "recode" if st in (4, 32) else kinds[st]
        if st == 0 or st == 34 or st == 29: kd = "fixed"
        seq = " ".join(keys[st:e + 1])
        rows.append((f"{st}–{e}" if e > st else f"{st}", kd, label, seq))
    return rows
SETUP_TEXT = {
    0: "Blank tape. A, B and C write 111, the same sequence that ends a shift at the blank end, and D turns the head left.",
    4: "A finds blank tape where a stripe 0 should be. A0 B1 write 1 0 in front of the 111, so the head can start carrying.",
    6: "Two carry cycles take the packet to the left end.",
    14: "The packet reaches the blank tape at the left end. As at every left end, A0 B1 A1 leave 1 000: the first gap.",
    17: "Pass right to the end of the tape. The blank tape there works as a wall: E0 F0 D0 turn the head with a new packet.",
    22: "Carry it back to the gap.",
    26: "Gap step. The gap moves two cells right and is now next to the blank tape.",
    29: "The gap meets that wall: E0 F0 D0 again, this time starting a shift.",
    32: "One shift cycle reaches the blank tape.",
    34: "A0 B0 C1 D0 write three 1s there: the end's marker plus the start of a packet.",
    38: "Carry the packet left. After step 45 the tape holds only stripes and the end marker: 10 1010 11, the first clean tape.",
}
def setup_html():
    rows = "".join(f'<tr><td class="mono">{esc(r)}</td><td>{chip(k, lab)}</td><td class="mono">{esc(seq)}</td><td class="sx">{esc(SETUP_TEXT[int(r.split("–")[0])])}</td></tr>'
                   for r, k, lab, seq in setup_rows())
    return f'<div class="scroll"><table class="seq setup"><caption>Every rule, in order</caption><thead><tr><th>steps</th><th>part</th><th>rules</th><th>what it does</th></tr></thead><tbody>{rows}</tbody></table></div>'

def setup_map():
    return step_map("setup", 0, 45, 30.0, 10.0, -5, 4, SETUP_STAGES,
                    [("blank", -5, -5), ("r", -4, -3, "", "10"), ("r", -2, 1, "stripes", "1010"), ("r", 2, 3, "marker", "11", 1), ("blank", 4, 4)],
                    "The first 45 steps from a blank tape, to scale, with the head path coloured by routine.", "blank tape", W2=600)

# ---------------------------------------------------------------- clean tapes
def clean_html():
    rows = []
    for s, n, _ in CLEAN[:10]:
        rows.append(f'<tr><td>{fmt(s)}</td><td>{n}</td><td>{2 * n + 4}</td></tr>')
    rows.append('<tr class="gapr"><td colspan="3">…</td></tr>')
    for s, n, _ in CLEAN[-2:]:
        rows.append(f'<tr><td>{fmt(s)}</td><td>{fmt(n)}</td><td>{fmt(2 * n + 4)}</td></tr>')
    return ('<table class="clean"><thead><tr><th scope="col">after step</th><th scope="col">n</th><th scope="col">cells</th></tr></thead><tbody>'
            + "".join(rows) + '</tbody></table>')

# ---------------------------------------------------------------- the round recurrence (positions of the marks)
REC_RULES = [
    ("run", "Gap at g moving right", "Next mark", [
        ("a marker p, with d a multiple of 4", "Swap, after d/4 bounces", "marker → g + d/2 − 1, gap → g + d/2 + 1, and the gap goes on"),
        ("a marker p, with d 2 more than a multiple of 4", "Merge, after (d − 2)/4 bounces", "a wall at g + d/2 + 3; a packet heads back"),
        ("a wall q", "Gap and wall vanish, and a shift starts at q", "see the shift rows"),
        ("a block r", "The block becomes a wall, the gap falls asleep, and a shift starts", "a wall at r − 1"),
        ("nothing, only blank tape", "A new end marker forms", "w grows by 3, with the new end marker 2 cells before the new end; a packet heads back"),
    ]),
    ("recode", "Shift moving right", "Next mark", [
        ("a marker p", "The marker becomes the new gap", "a gap at p, which goes on"),
        ("a wall q", "The wall becomes a block", "a block at q; a packet heads back"),
        ("a block r", "The block becomes a wall", "a wall at r + 2; a packet heads back"),
        ("blank tape", "A new end marker forms", "w grows by 2, with the new end marker 2 cells before the new end; a packet heads back"),
    ]),
    ("crawl", "Packet moving left", "First mark that isn't a marker", [
        ("a sleeping gap h", "A gap step wakes it", "gap → h + 2"),
        ("a wall q", "The wall becomes a marker and a gap", "marker at q − 1, gap at q + 1"),
        ("the left end", "A new round starts", "every position + 2, a new gap at 1 (+ 4 if a marker sits at cell 0; it becomes a wall at 5)"),
        ("a block", "The machine halts", "never happens within these rules"),
    ]),
]

def rec_rules_html():
    rows = []
    for kind, head, col, items in REC_RULES:
        rows.append(f'<tr class="grp"><th scope="rowgroup" colspan="3">{chip(kind, head)}<span class="grpcol">{esc(col)}</span></th></tr>')
        for at, what, res in items:
            rows.append(f'<tr><td class="at">{esc(at)}</td><td>{esc(what)}</td><td class="f">{esc(res)}</td></tr>')
    return ('<div class="scroll"><table class="meets rec"><thead><tr><th scope="col">Reaches</th><th scope="col">What happens</th>'
            '<th scope="col">Positions afterwards</th></tr></thead><tbody>' + "".join(rows) + '</tbody></table></div>')

LEDGER = [
    ("Step 921", "w = 34 · G1 M32", "the clean tape n = 14", [
        ("Gap 1 closes in on marker 32", "d = 32 − 1 − 3 = 28 = 4 × 7, so a swap after 7 bounces", "M14, G16"),
        ("Gap 16 has blank tape ahead", "w = 34 + 3 = 37, end marker at 35", "M14, M35"),
        ("The packet crosses M14 and reaches the left end", "every position + 2", "w = 39 · G1 M16 M37"),
    ]),
    ("Step 1,749", "w = 39 · G1 M16 M37", "", [
        ("Gap 1 closes in on marker 16", "d = 16 − 1 − 3 = 12 = 4 × 3, so a swap after 3 bounces", "M6, G8"),
        ("Gap 8 closes in on marker 37", "d = 37 − 8 − 3 = 26 = 4 × 6 + 2, so a merge after 6 bounces, into a wall at 8 + 13 + 3", "M6, W24"),
        ("The packet crosses M6 and reaches the left end", "every position + 2", "w = 41 · G1 M8 W26"),
    ]),
    ("Step 2,367", "w = 41 · G1 M8 W26", "", [
        ("Gap 1 closes in on marker 8", "d = 8 − 1 − 3 = 4, so a swap after 1 bounce", "M2, G4"),
        ("Gap 4 reaches wall 26, and the shift runs to blank tape", "w = 41 + 2 = 43, end marker at 41", "M2, M41"),
        ("The packet crosses M2 and reaches the left end", "every position + 2", "w = 45 · G1 M4 M43, at step 2,915"),
    ]),
]

def ledger_html():
    rows = []
    for step, marks, note, items in LEDGER:
        for i, (what, calc, res) in enumerate(items):
            first = ""
            if i == 0:
                extra = f'<span class="lnote">{esc(note)}</span>' if note else ""
                first = f'<th scope="rowgroup" rowspan="{len(items)}"><span class="lstep">{esc(step)}</span><span class="lmarks">{esc(marks)}</span>{extra}</th>'
            rows.append(f'<tr>{first}<td>{esc(what)}</td><td class="f">{esc(calc)}</td><td class="f res">{esc(res)}</td></tr>')
    return ('<div class="scroll"><table class="meets ledger"><thead><tr><th scope="col">Round starts</th><th scope="col">Event</th>'
            '<th scope="col">Arithmetic</th><th scope="col">Marks afterwards</th></tr></thead><tbody>' + "".join(rows) + '</tbody></table></div>')

QUICK = [
    ("n odd", "n + 3", "2", "35%"),
    ("n a multiple of 4", "n + 6", "3", "14%"),
    ("n = 26 or 38 (mod 48)", "n + 9", "5", "23%"),
    ("n = 2 (mod 96)", "n + 12", "5 or 6", "9%"),
    ("any other n", "round by round", "7 to 43", "19%"),
]

def quick_html():
    rows = "".join(f'<tr><th scope="row">{esc(a)}</th><td>{esc(b)}</td><td>{esc(c)}</td><td>{esc(d)}</td></tr>' for a, b, c, d in QUICK)
    return ('<table class="clean quick"><thead><tr><th scope="col">Clean tape</th><th scope="col">Next clean tape</th>'
            '<th scope="col">Rounds</th><th scope="col">Share</th></tr></thead><tbody>' + rows + '</tbody></table>')

# ---------------------------------------------------------------- frames for the cards
carry_frames = frame_rows([4260, 4261, 4262, 4263, 4264], -18, -6)
pass_frames = frame_rows([4295, 4296, 4297, 4298, 4299], -28, -16)
gap_frames = frame_rows([4291, 4292, 4293, 4294, 4295], -32, -20)
wall_frames = frame_rows([4672, 4673, 4674, 4675, 4676], -22, -10)
shift_kinds = {2808: "fixed", 2809: "fixed", 2810: "fixed", 2811: "recode", 2812: "recode", 2813: "recode"}
shift_frames = frame_rows([2808, 2809, 2810, 2811, 2812, 2813], -1, 11, shift_kinds)
turn_frames = frame_rows(
    [("h", "run", "Pass right, last step", "F1 keeps the marker's first 1 and moves on."), 4318,
     ("h", "append", "Marker turn", "E1 and B1 erase the marker. A0, B0, C1, D0 and A0 fill its two cells and the 0 on each side with 1s, so six 1s stand in a row, and B1 turns the third of them into a 0. The first two are the marker, now two cells further left, and the last three are a packet."),
     4319, 4320, 4321, 4322, 4323, 4324, 4325, 4326,
     ("h", "crawl", "One carry cycle", "The packet moves two cells left, up against the marker."),
     4327, 4328, 4329, 4330,
     ("h", "fixed", "Marker pass", "Where a carry would find a stripe 0, C finds the marker's 1. C1 D0 replace the usual C0, and the packet comes out on the far side. The marker has not moved."),
     4331, 4332, 4333, 4334, 4335,
     ("h", "crawl", "Carry on", "The carry continues toward the gap."), 4336, 4337], -9, 2)

# ---------------------------------------------------------------- page
import established
CSS = open(os.path.join(S, "map.css")).read() + open(os.path.join(S, "m2.css")).read()
first_clean = CLEAN[0]; last_clean = CLEAN[-1]

page = f'''<title>Closing Gap Rule Map</title>
<meta name="claude:viewport-fit-sides" content="cover">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Atkinson+Hyperlegible:ital,wght@0,400;0,700;1,400&family=Martian+Mono:wght@400;500;700&display=swap">
<style>
{CSS}
</style>
<div class="wrap">
  <header class="top">
    <p class="eyebrow">Turing machine · 6 states, 2 symbols · one halt rule, out of reach for at least 4.8 × 10⁴⁸ steps</p>
    <h1>What each rule in 1RB0RE…0LD1RE does</h1>
    <p class="lede">From a blank tape this machine fills the tape with stripes, 1010…, and keeps a few marks in them: a gap of three 0s, markers of two 1s, and walls of two 0s. The head bounces between the gap and the next mark to its right. Each bounce moves the gap two cells right and a marker two cells left, so the two meet halfway. The eleven rules split into three ways of moving along the tape and a handful of short fixed sequences, and the mark the head reaches decides which one runs next.</p>
    <p class="meta"><code class="machine">{MACHINE}</code> <a href="champion-rule-map.html" target="_blank" rel="noopener">Compare the BB(6) Champion Rule Map</a></p>
    <p class="hint">Hover over or tap any rule name, such as D1, to see what it does. The Rules button in the corner opens the full table.</p>
  </header>

  <section class="block" aria-labelledby="h-table">
    <h2 id="h-table">The rule table, sorted by job</h2>
    <div class="two">
      <div class="card">
        {rule_table()}
        <p class="small">Each entry says what to write, which way to move and the next state, so the last letter of one rule names the state of the next. Every sequence on this page is written in that firing order. D1 has no entry: it is the halt.</p>
      </div>
      <dl class="routines">
        <div><dt>{chip("crawl", "Carry left")}<span class="mono">A1 E1 B0 C0</span></dt><dd>The head carries a packet, 111, leftward through the stripes. A and E erase the packet's first two 1s, B writes one back, and C writes a 1 into the stripe 0 ahead. The packet is now two cells further left and the stripes behind it are as before. Four steps per two cells.</dd></div>
        <div><dt>{chip("run", "Pass right")}<span class="mono">E0 F1</span></dt><dd>E keeps each stripe 0 and F each stripe 1. The head walks right one cell per step and changes nothing. It stops when E reads a 1 or F reads a 0.</dd></div>
        <div><dt>{chip("recode", "Shift right")}<span class="mono">A0 B1</span></dt><dd>A writes 1 over each 0 and B writes 0 over each 1, so the stripes ahead move over by one cell. Rare: it runs only when a gap meets a wall or the head reaches a block.</dd></div>
        <div><dt>{chip("fill", "Gap step")}<span class="mono">A0 B1 A1</span></dt><dd>A carry that reaches a gap: the packet fills the gap's first two 0s, a new 000 opens two cells to the right, and A1 starts the pass.</dd></div>
        <div><dt>{chip("append", "Turn")}<span class="mono">E1 B1 A0 B0 C1 D0 A0 B1 · E0 F0 D0</span></dt><dd>A pass that reaches a marker moves it two cells left and turns back with a packet. A pass that reaches a wall or blank tape turns back with a packet and moves nothing.</dd></div>
        <div><dt>{chip("halt", "Halt")}<span class="mono">D1</span></dt><dd>D reads a 1 only if a carry finds 1s in the two cells ahead of its packet. A marker supplies one of them, never both.</dd></div>
      </dl>
    </div>
    <div class="notes">
      <p><b>Every routine works in pairs of cells.</b> The stripes repeat every two cells, and each cycle covers exactly two: a carry cycle moves the packet two cells, a pass cycle crosses one 0 and one 1, and a shift cycle rewrites one of each. Anything that breaks the 1010 rhythm stops the cycle, and that is what makes the marks signposts.</p>
      <p><b>One read in each cycle checks the tape.</b> On the way right, E1 instead of E0 means a marker or a block, and F0 instead of F1 means a wall. On the way left, A0 instead of A1 means a gap, a wall or the blank end, and C1 instead of C0 means a marker, or a block.</p>
    </div>
  </section>

  <section class="block" aria-labelledby="h-signs">
    <h2 id="h-signs">The marks are the signposts</h2>
    <p class="intro">This is the whole tape at step 4,264, with the head on the packet's first cell. Everywhere else it is plain stripes. Each mark is a break in the 1010 rhythm, and the routines stop at them.</p>
    {layout_strip()}
    <ul class="signs">
      <li><b>The gap, 000.</b> The head's home base. A carry that reaches it ends in a gap step, which moves the gap two cells right. Gaps left behind further left are asleep until a packet wakes them.</li>
      <li><b>A marker, 11.</b> A pass that reaches it ends in a marker turn, which moves the marker two cells toward the gap. A carry crosses it without moving it.</li>
      <li><b>A wall, 00.</b> A pass that reaches it turns back without moving it. A carry that reaches it turns it into a marker and a gap.</li>
      <li><b>The packet, 111.</b> Exists only while the head carries it. Each bounce makes one at the right and spends it on the gap at the left.</li>
      <li><b>The ends of the tape.</b> The blank tape on the right works like a wall. On the left it works like a gap: a packet that reaches it starts a new gap there.</li>
      <li><b>A block, 111 at rest.</b> Rare. A pass that reaches it shifts it away. A carry that reached it would halt the machine.</li>
    </ul>
  </section>

  <section class="block" aria-labelledby="h-close">
    <h2 id="h-close">The routines up close</h2>
    <p class="intro">Real steps from the run. The outlined cell is under the head, the letter is the head's state, and the text says which rule fires next. 0s are dark.</p>
    <div class="cards">
      <div class="card"><h3 class="ch">{chip("crawl", "Carry left")}</h3>{carry_frames}<p class="cap">The packet 111 starts under A. A and E erase two 1s, B writes one back, and C fills the stripe 0 ahead. Four steps later the packet sits two cells further left.</p></div>
      <div class="card"><h3 class="ch">{chip("run", "Pass right")}</h3>{pass_frames}<p class="cap">Just after a gap step. E reads the stripe 0s and F the 1s, and nothing on the tape changes.</p></div>
      <div class="card"><h3 class="ch">{chip("fill", "Gap step")}</h3>{gap_frames}<p class="cap">The carry's last C0 writes a 1 into the gap's last 0, and A0 writes one into its middle 0. B1 and A1 then clear the next two cells, so the gap now starts two cells further right. E begins the pass.</p></div>
      <div class="card"><h3 class="ch">{chip("append", "Wall turn")}</h3>{wall_frames}<p class="cap">E and F read the wall's 00, and D writes a 1 into its first cell. A starts a carry on that 1 and the stripe 1 before it. One cycle later they are a packet and the wall is 00 again.</p></div>
      <div class="card"><h3 class="ch">{chip("recode", "Shift right")}</h3>{shift_frames}<p class="cap">A gap has just run into a wall, leaving four 0s in a row. E0 F0 D0 turn the head, and the shift starts: each A0 writes 1 over a 0 and each B1 writes 0 over a 1.</p></div>
      <div class="card wide"><h3 class="ch">{chip("append", "Marker turn")} {chip("fixed", "Marker pass")} <span class="chtext">A marker turn, step by step</span></h3>{turn_frames}<p class="cap">Every step from 4,318 to 4,337. By the end the marker sits two cells further left, the packet has crossed it, and the carry is heading back to the gap.</p></div>
    </div>
  </section>

  <section class="block" aria-labelledby="h-routes">
    <h2 id="h-routes">Each part of the calculation</h2>
    <p class="intro">The head's path through each part, drawn against the tape. Time runs down the page. A carry takes two steps per cell, so carry segments are drawn twice as steep as passes and shifts. Region widths are schematic, and the numbers match the list beside each drawing.</p>
    <div class="legend" aria-label="Legend">{LEGEND}</div>
    {"".join(section_html(s) for s in SECTIONS)}
  </section>

  <section class="block" aria-labelledby="h-meets">
    <h2 id="h-meets">Every meeting, in one table</h2>
    <p class="intro">What happens depends only on how the head is moving and which mark it reaches. In the first 3 billion steps the run uses nothing but the three cycles and the short sequences listed here.</p>
    {meets_html()}
  </section>

  <section class="block" aria-labelledby="h-example">
    <h2 id="h-example">A stretch of the run, to scale</h2>
    <figure class="wmap">
      <div class="scroll">{example_map()}</div>
      <figcaption>
        <span>Steps 4,180 to 4,700, one row per step and one column per cell. Shaded columns are cells holding a 1, so the marks show up as breaks in the stripes. A merge near the right leaves a wall and sends a packet back over a marker to a sleeping gap at the left end. That gap closes in on the marker in six bounces, and they merge too. This packet reaches the left end and starts a new gap, which closes in on the second wall. The band at the bottom marks, left to right, the gap, the packet, and the two walls.</span>
        {LEGEND}
      </figcaption>
    </figure>
  </section>

  <section class="block" aria-labelledby="h-big">
    <h2 id="h-big">The big picture: halving</h2>
    <div class="prose">
      <p>Every so often the tape is clean: nothing but stripes and the end's marker, 1 0 (10)ⁿ 1 1, while the head carries one last packet to the left end. The run below starts from the clean tape with n = 62 at step 43,385 and ends at the next one, n = 77, at step 79,549.</p>
      <p>The packet starts a gap at the left end, and the gap closes in on the end's marker. Gap and marker move at the same speed, so they meet in the middle and swap. The gap goes on to the blank right end, which it can only reach two cells at a time, and the meeting there sends a packet back to start the next gap.</p>
      <p>Each new gap first meets the marker the previous one left behind, at half the distance, and swaps with it. So the markers on the left sit at about 1/2, 1/4, 1/8, 1/16 … of the way along. After the swap the gap goes on to meet whatever lies beyond: a marker (swap or merge), a wall, or the end.</p>
      <p>After about log₂ n rounds the newest marker lands at the left end. The next packet to cross it turns it into a wall and starts a new gap just beyond. The gap meets the wall almost at once, and the shift runs over the whole tape to the right end. That clears the last marks and leaves a clean tape again, a few cells longer.</p>
    </div>
    <figure class="wmap cmap">
      <div class="scroll">{CYCLE_SVG}</div>
      <figcaption>
        <span>One full cycle, to scale: about 160 cells across and 36,164 steps down, so every sweep looks almost flat and the bounces blur into grey wedges. The yellow line traces the gap and the pink line the mark it bounces off. Blue lines are packets carried back past the gap to the left, and green lines are shifts. Each numbered band starts when a new gap begins at the left end.</span>
        <span class="legend" aria-label="Legend">
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><line class="cm-gap" x1="2" y1="6" x2="42" y2="6"/></svg>The gap</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><line class="cm-right" x1="2" y1="6" x2="42" y2="6"/></svg>Marker, wall or end it bounces off</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><line class="sv-path crawl" x1="2" y1="6" x2="42" y2="6"/></svg>Carry back to the left</span>
          <span><svg viewBox="0 0 44 12" class="lg" aria-hidden="true"><line class="sv-path recode" x1="2" y1="6" x2="42" y2="6"/></svg>Shift</span>
        </span>
      </figcaption>
    </figure>
    <ol class="rounds">
      <li><b>From 43,393.</b> The gap meets the end's marker in the middle and swaps (step 49,905). It closes in on the blank end and meets it (53,283). The packet goes back over the middle marker.</li>
      <li><b>From 53,557.</b> Swap with the middle marker at the quarter point (55,269). Merge with the end's marker (59,468) leaves a wall.</li>
      <li><b>From 59,659.</b> Swap at the eighth point (60,123). The gap meets the wall (63,915), and a shift runs 52 cells to the end.</li>
      <li><b>From 64,251.</b> Swap at the sixteenth point (64,379). Swap with the end's marker (71,312). The gap meets the blank end (74,894).</li>
      <li><b>From 75,189.</b> Swap (75,221). Merge with the marker from round 4 (77,260) leaves a wall.</li>
      <li><b>From 77,363.</b> The swap (77,365) puts the marker at the very left end. The gap meets the wall (78,637), and the shift runs to the end.</li>
      <li><b>From 79,067.</b> The packet crossed the marker at the left end, turned it into a wall and started a new gap just beyond it. After one bounce the gap meets that wall (79,078), and a shift crosses the whole tape. The packet comes back, and after step 79,549 the tape is clean with n = 77.</li>
    </ol>
    <div class="two cleanrow">
      <div class="card">
        <h3>Clean tapes</h3>
        {clean_html()}
      </div>
      <div class="prose">
        <p>The tape only grows at its ends: two cells on the left each time a new gap starts there, and a few on the right each time a gap or a shift reaches the right end. By step {fmt(last_clean[0])}, the last clean tape in the first 3 billion steps, n is {fmt(last_clean[1])} and the tape is {fmt(2 * last_clean[1] + 4)} cells long.</p>
        <p>A cycle's step count grows with the square of the tape length, since each round's bouncing covers a stretch comparable to the tape. Meanwhile n goes up by about 9 per cycle on average, from 2 to 2,561 over 283 cycles. Together that makes the total grow like the cube of the tape length: between 0.022 × (cells)³ and 0.024 × (cells)³ at every clean tape once n passes 100.</p>
        <p><b>Every n is 2 more than a multiple of 3.</b> Count the 1s on the tape, and add 1 when the head is in C, D, E or F, or 2 when it is in B. No rule changes this total mod 3. For example, A0 writes a 1 and switches to B, adding 1 + 2, and E1 erases a 1 and switches from E to B, adding −1 + 2 − 1. The blank tape starts at 0. When the last carry of a clean tape reaches the left end, the head is in A on 1 1 (10)ⁿ 1 1, which holds n + 4 ones. So n + 4 is always a multiple of 3, and n can only grow by multiples of 3: by 3 most often, and by as much as 57 in the first 3 billion steps. The next section works out the exact amount.</p>
      </div>
    </div>
  </section>

  <section class="block" aria-labelledby="h-rec">
    <h2 id="h-rec">The marks as arithmetic</h2>
    <div class="prose">
      <p>Everything the head does is decided by where the marks are, so the run can be followed without its steps. Keep a list of the marks and update it with a few rules. Each rule replaces thousands or millions of steps.</p>
      <p>Count cells from the leftmost 1, which is cell 0, and let w be the number of cells up to the right end of the tape. A mark is named by its first cell: <b>G g</b> is a gap at cells g to g + 2, <b>M p</b> a marker at p and p + 1, <b>W q</b> a wall and <b>B r</b> a block. A round starts when a packet reaches the left end and opens a gap at cell 1. Right after the clean tape with n, the marks are G1 and M(2n + 4), and w = 2n + 6.</p>
      <p>For a gap and the marker ahead of it, the number that matters is <b>d = p − g − 3</b>, the count of stripe cells between them. It is always even. Each bounce moves the gap two cells right and the marker two cells left, so d drops by 4 per bounce. What is left over at the end decides the meeting: 0 cells gives a swap and 2 cells a merge.</p>
    </div>
    {rec_rules_html()}
    <p class="small">A gap or shift only ever deals with the nearest mark to its right, and a packet crosses markers until it finds something else. Each rule also has an exact step count. For example, k bounces of a gap toward a marker, ending with m stripe pairs still between them, take 6km + 6k² + 24k steps.</p>

    <h3 class="sub">Three rounds, worked through</h3>
    <p class="intro">The run from the clean tape with n = 14. Every list of marks here matches the tape in the step-by-step run.</p>
    {ledger_html()}

    <h3 class="sub">From one clean tape to the next</h3>
    <div class="two cleanrow">
      <div class="card">
        {quick_html()}
        <p class="small">Share: how often each case comes up among the first 10,000 clean tapes of the run. The rules in the first four rows hold for every n up to 200,000.</p>
      </div>
      <div class="prose">
        <p><b>Odd n takes two rounds.</b> The first gap starts at 1 and the end marker sits at 2n + 4, so d = 2n. For odd n that is 2 more than a multiple of 4, so they merge into a wall at 1 + n + 3 = n + 4. The new round shifts it to n + 6. In the second round the gap meets that wall, and the shift runs off the right end, where it adds an end marker and 2 cells. That leaves only stripes and the end marker, now at 2n + 8: the clean tape with n + 3.</p>
        <p><b>Other n take longer.</b> For even n the first meeting is a swap, and the marker lands in the middle at cell n. The next gap meets it with d = n − 2, so a multiple of 4 merges here and any other even n swaps again. Each further round halves the distance once more, so the outcome depends on more and more of the low binary digits of n, until a merge or a wall breaks the pattern. A multiple of 4 is settled in 3 rounds. n = 14 needs 24 rounds to reach 59, and n = 302 needs 23 to reach 341.</p>
        <p><b>For 29 n in 32, the last five binary digits decide the next clean tape.</b> Running the rules on whole residue classes of n gives the next clean tape exactly: n + 3 for odd n, n + 6 for n a multiple of 4, n + 9 for n that leave 6 or 10 when divided by 16, and n + 12 for n that leave 2 when divided by 32. Only n that leave 14, 18 or 30 when divided by 32 need more digits, and every right-end run of more than two meetings happens there. Each further digit settles about a quarter of what is still open.</p>
      </div>
    </div>

    <div class="notes">
      <p><b>Each rule is proved from the rule table.</b> I ran the machine on each rule's starting pattern with the stripe lengths left as symbols and the tape around it unknown. So each rule holds for every length and whatever surrounds it, with an exact step count. A simulation that uses nothing but these rules, starting from a blank tape, reproduces every round and clean tape of the 3 billion step run.</p>
      <p><b>The rules carry the run much further.</b> That simulation reached step 16,470,069,173,330,669,103, about 1.6 × 10¹⁹, and the clean tape with n = 4,529,102, without meeting an arrangement of marks the rules don't cover. A fast program that applies the same rules to the list of marks then followed the machine's clean tapes to n = 14,874,910,607, roughly 6 × 10²⁹ steps. No two marks ever came closer than they already had by n = 302. The deepest cycles along the way, replayed with the certified simulation, give the same results.</p>
      <p><b>Then by residue class.</b> From there the jump to each next clean tape was looked up from the residue classes of n described in <a href="#h-doeshalt">Does it ever halt?</a>, and only the few n whose class is still open were simulated. Every millionth looked-up step was simulated again as a check, and all 103,032 checks agreed. That carried the clean tapes to n = 10¹², after 110,250,943,952 cycles and roughly 2 × 10³⁵ steps.</p>
      <p><b>The clean tapes follow a fixed track.</b> For almost every n the jump depends only on the last few dozen binary digits of n. So modulo 2ᵏ the clean tapes run around a fixed cycle of residues. Each lap of 3 · 2ᵏ visits a third of them, and consecutive laps share more than 99%. A residue class is either visited once per lap or never. That is why the 10-meeting cascades in the run come exactly 3 · 2²⁸ apart. The track also favours the residues where cascades start: along it, deep cascades are about 2.3 times as common as for n picked at random. That is no special property of the machine's own n: a third of its clean tapes are odd, and the rest land on residues with exactly the frequencies of a Markov chain on residues built from random n, which visits n that leave 2 when divided by 16 about three times as often as a random sequence would.</p>
    </div>
  </section>

  <section class="block" aria-labelledby="h-warm">
    <h2 id="h-warm">How the tape gets set up</h2>
    <p class="intro">There is no separate setup code. From a blank tape the same routines build the first stripes, gap and end marker in 45 steps, and the tape is clean for the first time with n = 2.</p>
    <figure class="wmap setupmap"><div class="scroll">{setup_map()}</div>
      <figcaption><span>Every step to scale, one row per step and one column per cell. The numbers match the table below.</span>{LEGEND}</figcaption></figure>
    {setup_html()}
  </section>

  <section class="block" aria-labelledby="h-fuel">
    <h2 id="h-fuel">What keeps the right-end cascade going</h2>
    <div class="prose">
      <p>Each meeting between a gap and the end marker moves the action near the right end about halfway closer to the end. Call the distance at a meeting d. The next distance follows from the binary digits of d + 2. If they end in 00, the meeting is a merge and d + 2 loses its last digit. If they end in 10, it is a swap: d + 2 loses its last digit and gains 5. On its own this rule would carry on to the end of the tape. What stops it is the supply of feeds from the left.</p>
      <p><b>The feed is a halving clock at the left end.</b> During a long cascade the leftmost mark is usually a marker that halves its cell number every round. Each round it swaps with the gap, the gap goes on to the middle and right of the tape, and roughly every second round that produces a meeting. When the marker merges into a wall near the left end, that run of fuel is over.</p>
      <p><b>New fuel comes from blocks.</b> Suppose a round starts with the gap facing a block at cell r. If r has one trailing zero in binary, the next round starts with a wall at r/2 + 4, which feeds the next round directly. If r has k ≥ 2 trailing zeros, it starts with a marker at r/2 that halves for k − 2 rounds. This held in all 4,471 cases checked. The first halving after a clean tape follows the same rule: the marker starts at 2(n + 2), swaps once for each trailing zero of n + 2, and merges into a wall at (n + 2 without its trailing zeros) + 4.</p>
      <p><b>Each block forms at an average.</b> On the main path, a block at r, with the wall near the right end at R and a tape w cells long, leads two rounds later to a block at (r + R + 11)/2, a right-end wall at (R + w + 11)/2 and a tape w + 6 cells long. The right wall's distance to the end goes from D to (D + 1)/2.</p>
    </div>
    <div class="two cleanrow">
      <div class="card">
        <table class="clean quick"><thead><tr><th scope="col">Class of n</th><th scope="col">Meetings</th><th scope="col">Digits</th></tr></thead><tbody>
          <tr><th scope="row">73,742 mod 2³⁰</th><td>10</td><td>30</td></tr>
          <tr><th scope="row">26,819,166 mod 2³⁵</th><td>11</td><td>35</td></tr>
          <tr><th scope="row">4,321,786,462 mod 2³³</th><td>12</td><td>33</td></tr>
          <tr><th scope="row">363,165,946,702 mod 2⁴¹</th><td>14</td><td>41</td></tr>
        </tbody></table>
        <p class="small">Every large n in each class has exactly this many meetings. Digits: how many binary digits of n the class fixes. The deepest cascades spend 1.5 to 2 trailing zeros of the halving runs' starting cells per meeting.</p>
        <table class="clean quick"><thead><tr><th scope="col">Meetings</th><th scope="col">Share of all n</th></tr></thead><tbody>
          <tr><th scope="row">1</th><td>83.3%</td></tr>
          <tr><th scope="row">2</th><td>14.3%</td></tr>
          <tr><th scope="row">3</th><td>1.26%</td></tr>
          <tr><th scope="row">4</th><td>1.16%</td></tr>
          <tr><th scope="row">5</th><td>9.5 per million</td></tr>
          <tr><th scope="row">6</th><td>0.83 per million</td></tr>
          <tr><th scope="row">8</th><td>44 per billion</td></tr>
          <tr><th scope="row">10</th><td>4.1 per billion</td></tr>
        </tbody></table>
        <p class="small">Exact shares from every residue class of n up to 44 binary digits. They match the counts over 2 billion consecutive n.</p>
      </div>
      <div class="prose">
        <p><b>Each meeting costs two to three binary digits.</b> Running the rules on whole residue classes of n, explained in <a href="#h-doeshalt">Does it ever halt?</a>, settles the cascade length of every n whose cycle depends on at most 44 binary digits. After four meetings the cascades fall off a cliff, and each further meeting is 4 to 10 times rarer. The fewest binary digits of n that fix a cascade grow by about 3 per meeting: 8 digits for 4 meetings, 28 for 8, 33 for 12 and 41 for 14.</p>
        <p><b>The longest cascade in a whole class is 16 meetings.</b> Up to 54 digits no settled class has more than 14, and every large n ≡ 363,165,946,702 (mod 2⁴¹) has exactly 14. Classes with 16 first settle at 56 digits, and the first with 17 at 60. Longer ones belong to single integers that read all their digits: below 2⁵⁹ the longest is 19, first reached by n = 114,928,805,503,523,374 (16 by n = 3,617,714,363,521,582 and n = 30,335,806,016,335,582), and following lucky lines gives 23 at 84 digits and 28 at 94. The family built earlier from its ending, every n ending in the 33 binary digits <span style="word-break:break-all">100000001100110010011101001011110</span>, has exactly 12. The machine's own clean tapes reached 14 meetings at n = 391,305,139,022.</p>
        <p><b>The 13-meeting record from the sweeps is different.</b> n = 6,151,594,450 owes 11 of its 13 meetings to the zeros above its top binary digit; changing any digit above bit 33 leaves 3 to 6. Most n whose cycle runs past their top digit gain nothing from it.</p>
        <p><b>The simplest feed stops within 3 meetings.</b> With only the gap, a wall near the left and a wall near the right on the tape, the right side needs d ≡ 2 (mod 4) to keep merging and the left needs the right wall at a multiple of 4. Each meeting moves that wall by d/2 + 7, so the two conditions clash by the second meeting. Every residue class checked ends within 3 meetings.</p>
      </div>
    </div>
    <div class="prose">
      <p><b>Every long cascade runs the same loop.</b> Every cascade of 9 or more meetings that settles within 33 digits spends at least 4 of them in one 8-round loop, and all 256 with 13 or 14 meetings below 2⁴⁹ spend 7 to 9 there. The loop makes 4 meetings per pass. Its rounds start with three walls; a block and a wall; a halving marker and a block; the marker and two walls; the marker and a block; the marker and two walls; three walls; a block and a wall. Call the walls at the start of a pass a, b and c, and the end E. Another pass needs two things. E − c − 1 must have 4 more trailing zeros in binary: that is the end countdown above. And b must keep a fixed relation to the end, which in the limit is b = 16E/21 + 62/49 read as 2-adic numbers, to about 6 more binary digits. Counted exactly, each pass costs 10 binary digits, 2.5 per meeting.</p>
      <p><b>Nothing cheaper keeps a cascade going.</b> Starting from a block, a wall and an end in general position, I followed every branch of the rules exactly, splitting the possible positions in half at each test. From the sixth meeting on, the chance of reaching each further 4 meetings falls by exactly 1024, the cost of the loop. 20 million random starts give the same chances for the first 8 meetings. The loop itself has no built-in end: solving its conditions for 12 passes gives a block, wall and end that make 50 meetings in a row.</p>
      <p><b>A clean tape can't hold the loop for long.</b> On a clean tape every position depends on the one number n, so the two conditions become two targets for the binary digits of n. The left side, through its halving markers, reads about 1.5 new digits of n per meeting and the end countdown only 1. So the end only ever reads digits that the left side has already fixed. Once the left side is satisfied, whether the right end keeps merging is already decided, and the cascade lasts only as long as the two targets agree. For 100 cascades I fixed the digits that lead to the first meeting and followed every continuation for 40 to 45 more digits. Each has a longest possible cascade, reached by exactly one choice of digits, and no later digits go past it. All 256 cascades of 13 or 14 meetings enter the loop the same way, finish one or two passes, and leave when the end runs out of trailing zeros.</p>
      <p><b>The loop is two countdowns, and one of them always runs out.</b> Put R = E − c − 1 and L = 147b + 280E − 392c − 578. One pass turns R into exactly R/16 and L into exactly L/64, so the loop goes on while R keeps 4 and L keeps 6 trailing zeros per pass. L is always 3 more than a multiple of 7, so it is never 0, and it is at most 280E in size. So any one run of the loop makes at most log₆₄ 280E passes, about a sixth of the tape's binary length. Each pass brings the right end 16 times closer to the end, so the loop alone can cover at most about two thirds of the halvings a halt needs.</p>
      <p><b>The two countdowns are one fixed point seen two ways.</b> R = L = 0 is the fixed point of the pass, b = 16E/21 + 62/49 and c = E − 1. As ordinary numbers each pass pulls the walls toward it, so after a pass or two b sits near 16/21 of the way to the end on every tape. As 2-adic numbers each pass pushes away from it, so staying in the loop needs the walls ever closer to it in binary digits. L is the one integer that measures both, and it can't be 0. The card at the end of this section spells the argument out step by step.</p>
      <p><b>Leaving the loop is short, and it never comes back.</b> Starting from the loop's three-wall state with every position free, I followed every branch of one pass, with no limit on binary digits. The search is finite: 356 ways out. A pass completes with probability exactly 1/1024. Otherwise the run ends within 8 meetings and never returns to the loop. Every comparison it makes comes out the same for any spacing of the walls. So a run that reaches the loop makes 4 meetings per pass and at most 8 more.</p>
      <p><b>There is a rarer second loop with the same lock.</b> With one more wall near the end, the same 8 rounds can repeat. Each pass costs 14 binary digits instead of 10. Its left countdown is −441b + 735c − 2156d + 1652E − 179, again 3 more than a multiple of 7, so it is never 0 either. In fact the loop runs with any number k of extra walls, each costing 4 more binary digits per pass. Its pass map has a simple general form: the right walls are smoothed by 1, 4, 6, 4, 1 sixteenths each pass. For every k up to 2500 the left countdown's variable coefficients are multiples of 7 while its constant is 6·3ᵏ mod 7, never 0. Every loop in the family is locked the same way, though each lock only bounds one unbroken stretch: a run that switches pass types escapes it, as the hand-built tapes in <a href="#h-doeshalt">Does it ever halt?</a> show.</p>
    </div>
    <div class="card explain" id="binary-argument">
      <h3 class="ch"><span class="chtext">The binary-digit argument, step by step</span></h3>
      <p><b>1. Closeness in binary digits.</b> Read a number's binary digits from the right. Two numbers are close in this sense, called 2-adic, when they agree in many of their last digits, that is, when their difference is divisible by a high power of 2. A number is 2-adically small when it has many trailing zeros. This has nothing to do with ordinary size: 2⁶⁰ is huge but 2-adically tiny, while 2⁶⁰ − 1, just as huge, is odd and so not 2-adically small at all.</p>
      <p><b>2. A run at the right end reads binary digits.</b> Each meeting between the gap and the end marker looks at the distance d modulo 4, which decides swap or merge, and then the distance roughly halves. Halving shifts the binary expansion right by one place, so the next meeting's test reads the next digit. A run of k meetings reads about k binary digits of the positions, from the bottom up, and a halt needs a single run that reads about log₂ of the tape width of them without breaking off.</p>
      <p><b>3. Each pass of the loop uses up trailing zeros.</b> In the loop's three-wall state the two countdowns are R = E − c − 1 and L = 147b + 280E − 392c − 578. One pass divides R by exactly 16 and L by exactly 64. Both must stay whole numbers, so p passes need R divisible by 16ᵖ and L by 64ᵖ: each pass spends 4 trailing zeros of R and 6 of L. When either runs out, the run breaks off.</p>
      <p><b>4. L can't be 0.</b> Its coefficients 147, 280 and 392 are multiples of 7, while 578 is 4 more than a multiple of 7. So L is always 3 more than a multiple of 7, on every tape, and never 0. Dividing by 64 keeps that remainder, since 64 is one more than 63 = 7 × 9. The 7 is no accident. L = 0 would mean sitting exactly on the loop's fixed point, and finding that point divides by 1 − 1/64, which brings in 63, so the point has 7s in its denominators (b = 16E/21 + 62/49). A wall sits on a whole cell, so no tape is ever exactly there.</p>
      <p><b>5. Small, yet divisible by a large power of 64: the lock.</b> A nonzero whole number divisible by 64ᵖ is at least 64ᵖ in size. But L is built from positions on the tape, so it is at most 280E. So 64ᵖ ≤ 280E, and one stretch of the loop makes at most log₆₄(280E) passes. At 4 meetings per pass that covers about two thirds of the halvings a halt needs. If L could be 0, nothing but R would stop the loop, and R alone allows all of them. That is why L ≠ 0 is the heart of the matter.</p>
      <p><b>6. The same fact as a fixed point.</b> As ordinary numbers, each pass pulls the walls toward that fixed point. In binary digits it pushes them away: staying in the loop means agreeing with the fixed point in 6 more binary digits per pass. L is the tape's offset from the point. As an ordinary number it shrinks 64-fold per pass, and in binary it must gain 6 trailing zeros per pass, and a whole number can't do both for long.</p>
      <p><b>Seen on a real run.</b> Take the closest approach found below 2⁵⁹, the clean tape n = 114,928,805,503,523,374, whose tape is about 2⁵⁷·⁷ cells wide. At three successive pass starts of its run, R has 12, 8 and 4 trailing zeros and L has 21, 15 and 9: exactly 4 and 6 fewer each pass. As ordinary numbers R goes from 2⁵³ to 2⁴⁹ to 2⁴⁵ and L from 2⁵⁸·⁷ to 2⁵²·⁷ to 2⁴⁶·⁷, 16 and 64 times smaller each pass, and L stays 3 more than a multiple of 7 throughout. Another full pass needs at least 5 trailing zeros of R, so after the third pass start the run leaves the loop, with L still holding 9. On this tape the end countdown ran out first, and the cycle got within 2⁻¹⁹·⁷ of the end, where a halt needs about 2⁻⁵⁷. All nine record runs up to 84 digits end the same way, with R down to 3 or 4 trailing zeros while L still has enough for another pass or runs out at the same time; L never gets near its size limit, so what stops them is the line-up, not the lock.</p>
      <p><b>7. How many numbers you get to choose.</b> On a tape with two free numbers, such as the marker position and the width of a two-marker state, both conditions can be met by choosing digits of both numbers: 10 digits per pass, 2.5 per halving. On the machine's own tapes everything depends on the one number n, and the two conditions become n ≡ a (mod 2⁴ᵖ) and n ≡ b (mod 2⁶ᵖ), with a and b fixed by the way the cycle came into the loop. Both can hold only if a and b already agree in their last 4p binary digits. That line-up is settled by digits of n read before the loop starts, so it can't be chosen as the loop goes. Each way in allows a fixed number of passes. Up to that number, passes are cheap, 6 digits each; beyond it, none.</p>
      <p><b>8. Lucky lines, and why the odds come back to 2.5.</b> The chart <a href="#staircase">"The machine's tail is a staircase of lucky lines"</a>, further down, shows exactly this. A few ways in whose line-up happens to be long carry the machine's near misses at each depth, each at 1.5 digits per halving, and then stop. A line-up of g digits is about as likely as a random number having g trailing zeros, 1 in 2ᵍ, so going deeper costs another digit per halving: 2.5 again on average. That is measured, not assumed: the line-up of a way in can be read straight off its two countdowns by solving congruences, and over 693,518 of the machine's own lines each extra loop meeting a line allows is rarer by 0.85 to 0.99 binary digits, out to 20 meetings. That average gives the odds quoted below, and the closest approaches found stay about a third of the way to a halt.</p>
      <p><b>9. Why this is not yet a proof.</b> Every step above is exact except one: that line-ups keep behaving like the trailing zeros of random numbers. That is measured out to 20 loop meetings, but a halt needs about as many meetings as n has binary digits, and there are infinitely many ways into the loop, each with its own line-up. To rule out that one of them has an enormous run of trailing zeros is a statement about the binary digits of particular whole numbers. Such statements are easy to weigh and, so far, impossible to prove, which is the situation of the Collatz problem.</p>
    </div>
  </section>

  <section class="block" aria-labelledby="h-doeshalt">
    <h2 id="h-doeshalt">Does it ever halt?</h2>
    <div class="card brief">
      <h3 class="ch"><span class="chtext">In brief</span></h3>
      <ul>
        <li><b>No halt below n = 2⁶¹.</b> Every clean tape below 2⁶¹ was checked through its residue class, so the machine runs at least 1.8 × 10⁵² steps without halting.</li>
        <li><b>A halt needs one long run at the right end:</b> about log₂ n meetings in a row. The longest anywhere below 2⁶¹ is 19.</li>
        <li><b>Long runs are one loop, and it is locked.</b> One stretch of it covers at most about two thirds of what a halt needs, and it ends the run. Its ending is now known exactly: the run can reach the end only from at most 176 cells away, with the left countdown in a fixed residue class. So a halt needs the loop to start late, and beyond the checked range later than any run seen by a wide margin.</li>
        <li><b>The usual ways into that loop can never lead to a halt.</b> For every way in found within 62 binary digits, which covers all but about eight in ten billion two-marker states, the exact end of the loop alone rules out a halt on any tape wider than 2⁵⁹·² cells, and the checked range covers the rest. The commonest way can't lead to a halt above 2²²·⁴ cells at all.</li>
        <li><b>The rules alone do allow a halt.</b> Hand-built tapes with three free numbers halt at every width tried up to 2²⁰⁰: a stretch of a rarer loop, a drop into the locked one, then a stretch of it.</li>
        <li><b>The machine's own tapes have too few free numbers.</b> They have one (two for the wider family they sit in), while a halt costs about 2.8 binary conditions per halving. The expected number of halts beyond 2⁵⁵ comes out at 1 in 10²⁴ or less. The machine's own tail looks cheaper for a while, but that stretch is a few lucky lines of states, and lines that line up further are rarer by a binary digit per halving.</li>
        <li><b>And the rarer loop is capped outright for them.</b> Each loop has a number of countdowns, two for the locked loop and three for the rarer one, and a family of tapes can follow a loop without a fixed limit only if it has at least that many free numbers. So for the machine's tapes the rarer loop stops after a fixed number of passes for each way in. For the commonest ways in that number is zero or one; among 190,923 ways in built from all routes to 30 binary digits, 81 allow two passes, 8 allow three and none allows four.</li>
        <li><b>The closest any clean tape is known to come is about a third of the way.</b> The best found reach 19.7 halvings at 57 binary digits and 29.6 at 94, where a halt needs about 57 and 94.</li>
        <li><b>No proof yet.</b> What is left is a statement about binary digits of the same kind as the Collatz problem. The section <a href="#h-known">What is established, and how firmly</a> grades every statement on this page and states the main theorem in full.</li>
      </ul>
    </div>
    <div class="prose">
      <p>D1 is the only missing rule, so the question is whether D ever reads a 1. D runs after F0 or C1. After F0 it always lands on the 0 that E wrote two steps before, as in every wall turn. C runs only after B0, and tracing back from there, D can read a 1 in just one way: a carry cycle starting with A1 E1 when the two cells ahead of its packet both hold 1. In the stripes the first of those is a 0, which gives C0 and the carry goes on. At a marker the first is a 1 and the second a 0, which gives C1 D0, the marker pass. Two 1s in a row ahead of the packet needs a block, 111, or a longer run of 1s.</p>
      <p>Blocks do form: a shift that runs into a wall turns the wall into one. But a shift stops at the first mark it meets, so the stretch just left of a new block is plain stripes. The next time the head arrives there it is passing right from a gap, and the pass shifts the block away. In the first 3 billion steps a pass reached a block 68 times, and no carry ever did.</p>
      <p>The rules in <a href="#h-rec">The marks as arithmetic</a> make this exact. Within them a block always lies to the right of the gap or the packet: a block appears only where a shift stops, the packet then heads left from it, and the next pass or shift to arrive removes it. So within the rules a carry never reaches a block.</p>
      <p>That still isn't a proof that the machine never halts. The rules assume the marks never touch in a few odd ways, and the ones that lead to a halt end the same way: a new marker is made directly against a 1, fuses with it into a block left of the head, and the next carry halts on it. That happens when a carry reaches a wall with a marker directly before it or exactly two stripe cells after it, and also when a long run's last meeting is a swap right at the end, as in the hand-built tapes below.</p>
      <p>The only route to either that I have found needs the activity at the right end to halve its distance to the end about log₂ n times in a row: a wall near the end is turned into a block, passed, and remade closer to the end, once for each meeting between a gap and the end marker. That run of meetings is short, as <a href="#h-fuel">What keeps the right-end cascade going</a> shows. The longest below 2⁶¹ is 19 meetings, reached only by rare single clean tapes, and along the machine's own clean tapes, followed to n = 10¹², the longest is 14.</p>
      <p><b>On a tape built by hand, that route really does halt the machine.</b> I set the loop's two countdowns by hand on a 72-cell tape: gap at 1, walls at 7, 30 and 39, head on the gap in state E, tape <span style="word-break:break-all">100010100101010101010101010101001010101001010101010101010101010101010101</span>. The meetings at the end run 30, 14, 6, 2, 0, and the machine halts after 10,302 steps: state D reads the first 1 of a 111 next to the end. A 16,000-cell version follows the mark rules exactly for 17 rounds and then halts at step 759,437,834. On a 17,652-cell tape the last wall can start 8,192 cells from the end, mid-tape, and the machine halts at step 1,258,643,838. I also ran every three-wall round start of width 40 to 130, 423,775 of them, on the real machine. It halted only when the mark rules' right-end run got within 2 cells of the end, or when marks touched. Every clean tape below 5,000 run directly on the machine reaches the next one. Nothing suggests these tapes can be reached from blank. The lock keeps the plain loop from doing this on big tapes: from about 2¹⁷ cells on, one run of the loop can't start from mid-tape, and the machine's own tapes are now longer than 2⁵⁶ cells. A run that switches loops gets around the lock, though, and the last part of this section builds tapes of any size that halt that way.</p>
    </div>
    <div class="two cleanrow">
      <div class="card">
        <table class="clean quick"><thead><tr><th scope="col">Step</th><th scope="col">Width</th><th scope="col">Marks after the gap at 1</th></tr></thead><tbody>
          <tr><th scope="row">0</th><td>72</td><td>W7 W30 W39</td></tr>
          <tr><th scope="row">124</th><td>74</td><td>B32 W41</td></tr>
          <tr><th scope="row">1,894</th><td>78</td><td>M16 B61</td></tr>
          <tr><th scope="row">3,596</th><td>82</td><td>M8 W38 W73</td></tr>
          <tr><th scope="row">4,750</th><td>84</td><td>M4 B75</td></tr>
          <tr><th scope="row">7,224</th><td>90</td><td>W5 W44 W85</td></tr>
          <tr><th scope="row">7,374</th><td>92</td><td>B46 W87</td></tr>
          <tr><th scope="row">9,332</th><td>96</td><td>W27 W70 W93</td></tr>
          <tr><th scope="row">10,066</th><td>98</td><td>B72 W95</td></tr>
          <tr><th scope="row">10,302</th><td colspan="2">halts: D reads a 111</td></tr>
        </tbody></table>
        <p class="small">The hand-built 72-cell tape, round by round on the real machine. The distance from the last wall to the end halves: 33, 17, 9, 5, 3 cells. The machine halts when the carry reaches the block that then forms next to the end.</p>
      </div>
      <div class="prose">
        <p><b>The two countdowns are visible in the table.</b> The wall nearest the end gains on it each pass, and the halving marker on the left runs M16, M8, M4 before it is spent. Planting both countdowns with enough trailing zeros is all it takes to make the machine halt on a small tape. On the machine's own tapes the left countdown is too short, by the lock, and runs that switch between loops have not been seen.</p>
      </div>
    </div>
    <div class="prose">
      <p><b>No clean tape below 2⁶¹ leads to a halt.</b> For most n the cycle to the next clean tape depends only on the last few binary digits of n. Write n = 2ᵏj + ρ and leave j as a symbol. Then the rules can run on a whole residue class at once, and the class splits only when a step needs another digit. A class is settled when its cycle reaches the next clean tape.</p>
      <p>For a whole class, each comparison of two positions is a linear condition on j. I recorded every one, and in every class that settles within 58 digits, each n with at least one 1-bit above those digits follows the class exactly.</p>
      <p>Each n below 2⁶¹ is then either covered by such a class or is the only member, with that many digits, of a class still open, which I ran directly. That makes 36,929,911,789 classes and 120,940,310,955 direct runs, and none of them halts. Two separate programs did this: one re-runs every open class from the clean tape at each digit, and was taken to 2⁵¹; the other carries each class's state forward as it splits, agrees with the first at every one of those levels, and went on to 2⁶¹, matching its own earlier runs to 2⁵⁵, 2⁵⁷ and 2⁵⁹ at every shared level. In all those cycles no two marks come closer than in cycles the certified simulation has checked.</p>
      <p><b>That rules out a halt for at least 1.8 × 10⁵² steps.</b> The clean tapes below 2⁶¹ are never more than 345 apart. Each cycle from the clean tape with n starts with ⌊n/2⌋ bounces, at least 1.5(n − 1)² steps. So the machine needs at least 1.8 × 10⁵² steps to get past 2⁶¹. At its actual pace it needs about 2 × 10⁵⁴. Certified cycles near n = 10¹² keep the pace of the first clean tapes, about 0.022 × (cells)³ steps in total.</p>
    </div>
    <div class="two cleanrow">
      <div class="card">
        <table class="clean quick"><thead><tr><th scope="col">Digits of n</th><th scope="col">Best halvings</th><th scope="col">Needed to halt</th></tr></thead><tbody>
          <tr><th scope="row">17</th><td>10.3</td><td>16.2</td></tr>
          <tr><th scope="row">30</th><td>12.4</td><td>29.1</td></tr>
          <tr><th scope="row">39</th><td>14.0</td><td>38.5</td></tr>
          <tr><th scope="row">45</th><td>14.7</td><td>44.8</td></tr>
          <tr class="gapr"><td colspan="3">best found</td></tr>
          <tr><th scope="row">52</th><td>16.5</td><td>51.7</td></tr>
          <tr><th scope="row">57</th><td>19.7</td><td>56.7</td></tr>
          <tr><th scope="row">68</th><td>20.8</td><td>67.8</td></tr>
          <tr><th scope="row">75</th><td>22.1</td><td>74.4</td></tr>
          <tr><th scope="row">85</th><td>25.4</td><td>84.5</td></tr>
          <tr><th scope="row">94</th><td>29.6</td><td>93.6</td></tr>
        </tbody></table>
        <p class="small">Up to 45 digits: over every n with that many binary digits, the most halvings of the distance between a gap and the end marker. A halt needs the distance to reach 2. Below the line: the closest found, so lower bounds for the best. The 52-digit one, n = 3,617,714,363,521,582, turned up in the exhaustive check; the others come from following the luckiest lines of two-marker states (for example n = 114,928,805,503,523,374 and n = 14,690,414,442,211,083,106,227,634,386), and the 55-digit one was predicted that way before the exhaustive check reached it. Each was confirmed by a certified run of the real machine.</p>
      </div>
      <div class="prose">
        <p><b>A halt would need an n whose cycle runs past its own top digit.</b> Within a residue class every distance keeps growing with the higher digits of n, so it can never shrink to the 2 cells a halt needs. Only an n whose cycle reads all of its binary digits can do that. Below 2⁴⁵ even the best of them fall further short with every digit, and the best found up to 94 digits get only about a third of the way: the shallowest class that comes within 2⁻ˣ of the end has about 3.3x binary digits, so an n with b digits can be expected to reach only about b/3.3 halvings, against the b a halt needs. Each record run is one lead-in meeting, one stretch of the loop (26 of the 28 meetings at 94 digits) and an exit of at most 3. How long the stretch lasts is set by how far that line lines up, not by the loop's own limit, which at 94 digits would allow about 67 meetings. Every one of them enters the loop through one of the routes excluded below.</p>
        <p><b>The odds of a halt beyond 2⁵⁵ look like 1 in 10²⁴ or less.</b> For the machine's own family the odds can be computed exactly, not sampled: follow every even clean tape's whole cycle on classes of n, splitting a class whenever a step needs another binary digit, to 48 digits (369 million classes, exactly the classes the exhaustive check settled through 49 digits). The share of n whose cycle comes within 2⁻ˣ of the end is about 1 in 12,000 for x = 4, 1 in 11 million for x = 8 and 1 in 2 billion for x = 12. From 4 to 8 halvings that falls 2.5 binary digits per halving, like a single two-marker segment, but from 8 to 12 only about 1.9. The chart below shows why. Every two-marker state that a class of n reaches is a whole line of states, one per member of the class, and on a line the loop costs only 6 digits per pass, 1.5 per halving, for as long as the line's line-up lasts. At each depth a few lucky lines carry almost all of the tail, each until its line-up runs out. Lines that line up further are rarer by about a digit per halving: of the machine's 64,665 lines up to 28 digits deep, 15% come within 2⁻¹⁰ in one segment and 0.02% within 2⁻¹⁹, and against random lines of the same shape they line up no more often. So the 1.9 digits per halving cannot last, and the average price is the plane's 2.5. With it, the expected number of halts over all clean tapes beyond 2⁵⁵ comes out at about 10⁻²⁷ from the machine's own tail and 10⁻²⁵ to 10⁻²⁴ from random two-marker states, before taking out the routes now excluded. And the machine's actual sequence of clean tapes is a typical one: its residues mod 2ᵏ follow exactly the frequencies of a Markov chain built from random n, so it visits any class of n at most about 3 times as often as a random sequence would.</p>
        <p>That extrapolates tails measured out to about 20 halvings, so it is an estimate, not a proof. The rules also assume the marks never touch in the ways described above, which every certified cycle bears out but which is not proved for all n.</p>
      </div>
    </div>
    <figure class="card cd-fig" id="staircase">
      <h3 class="ch"><span class="chtext">The machine's tail is a staircase of lucky lines</span></h3>
      <div class="cd-wrap">{ST_SVG}<div class="cd-tip" id="st-tip" role="tooltip" hidden></div></div>
      <figcaption class="cap"><span class="cd-key"><span class="cd-sw cd-swL"></span>The machine's own: share of even n whose cycle comes within 2⁻ˣ of the end</span> <span class="cd-key"><span class="cd-sw cd-swA"></span>line 1</span> <span class="cd-key"><span class="cd-sw cd-swB"></span>line 2</span> <span class="cd-key"><span class="cd-sw cd-swC"></span>line 3</span><br>Every two-marker state a class of n reaches is a whole line of states, one for each member of the class. Each of the three lines shown carries most of the machine's share at some depth, and each stops at a fixed reach: line 1, (7138t + 72, 8192t + 93), reached at 11 digits, at 10.4 halvings; line 2, (18t + 8, 512t + 229) at 7 digits, at 12.5, the same from 34 to 70 digits of t; line 3, (13922t + 2004, 524288t + 75497) at 17 digits, at 14.1. Up to its reach a line pays about 6 binary digits per 4 halvings, one pass of the loop. Summed over the 5,141 lines reached within 22 digits, followed to 46 digits in all, the total matches the exact tail of all cycles to within 2% at every x.</figcaption>
      {ST_TABLE}
    </figure>
    <script>
(function () {{
  const D = {ST_DATA}, svg = document.getElementById('st-svg'), tip = document.getElementById('st-tip'),
        cross = document.getElementById('st-cross');
  if (!svg) return;
  const x0 = +svg.dataset.x0, x1 = +svg.dataset.x1, vb = svg.viewBox.baseVal;
  const pw = v => '2<sup>' + Math.log2(v).toFixed(1) + '</sup>';
  function show(ev) {{
    const r = svg.getBoundingClientRect(), sx = (ev.clientX - r.left) * vb.width / r.width;
    let h = Math.round(4 + (sx - x0) / (x1 - x0) * 10.5); h = Math.min(14, Math.max(4, h));
    const px = x0 + (x1 - x0) * (h - 4) / 10.5, d = D[h];
    cross.setAttribute('x1', px); cross.setAttribute('x2', px); cross.setAttribute('visibility', 'visible');
    const c = (k, v) => '<br><span class="k ' + k + '"></span>' + (v > 0 ? pw(v) + ' (' + Math.round(100 * v / d[0]) + '%)' : 'past its reach');
    tip.innerHTML = '<b>x at least ' + h + '</b><br><span class="k kL"></span>all lines: ' + pw(d[0]) + c('kA', d[1]) + c('kB', d[2]) + c('kC', d[3]);
    tip.hidden = false;
    const left = px * r.width / vb.width, w = tip.offsetWidth;
    tip.style.left = Math.min(Math.max(left + 12, 0), r.width - w) + 'px';
    tip.style.top = '8px';
    if (left + 12 + w > r.width) tip.style.left = Math.max(left - w - 12, 0) + 'px';
  }}
  function hide() {{ tip.hidden = true; cross.setAttribute('visibility', 'hidden'); }}
  svg.addEventListener('pointermove', show); svg.addEventListener('pointerleave', hide);
}})();
</script>
    <div class="prose">
        <p><b>A halt would need a run that enters the loop late.</b> A run's first meeting is usually within about 4 halvings of the full width, however close the run before it got (29 million runs checked), and every run seen is a short lead-in, at most one stretch of the loop and a short exit (147 million runs; among 5.8 billion runs from random 60-bit cycles, 3 million contain a stretch of the loop and none contains two). That alone caps a run at about two thirds of log₂ n plus a constant. Counted run by run it is sharper. At a run's first pass start, say the end is 2⁻ˢ of the width W away and L is 2^λ times W. A pass divides R by 16 and L by 64, so 3s + 2λ stays the same at every pass start of the stretch, and what matters is the last one. I searched the end of the loop exactly: from a pass start with the end distance R fixed and the other positions free, every way the run can go, for every even R up to 4096, in two independent implementations, one of which decides every comparison of positions symbolically and reports when it cannot (it never had to). The run gets within 2 cells of the end marker only from R = 2, 4, 8, 16, 24, 32, 48, 64 or 176, and each of these needs L in a fixed residue class. For R = 176, L must be a multiple of 128, so it is at least 256 in size. Together that proves (within the mark rules) that a run that halts through the loop has 3s + 2λ of at least log₂W − 6.4. Counting halvings alone had given log₂W − 24. Over a million loop entries, in random two-marker states, in the deepest classes of the exhaustive check and in the record cycles, 3s + 2λ never exceeds 32.2, which allows a halt only on tapes narrower than 2³⁹. The latest of those entries come from a staircase of short runs, a 7-round pattern that pushes run starts out to 5.6 halvings. Its own affine map pulls the last wall toward a fixed point 0.0084 of the width from the end, so like the loop it can't creep up on the end. It can still make the next run enter the loop late: from a staircase run all the way to its limit, exactly 1/32 of the ways out enter at 3s + 2λ = 36.4 (every branch from the limit followed, to 40 binary digits), and that is the latest exit from any of the 118 plateau limits that uses no round of the extra-wall loop; it allows a halt only below width 2⁴³, far inside the checked range. Exits that do pass through extra-wall rounds reach 47.3 from those limits, at measures below 10⁻¹¹, and the route tree's deep lead-ins reach 52.9. A halt beyond the checked range (tapes up to 2⁶² cells) through the loop would need 3s + 2λ ≥ 55.6, which means entering the loop at least 12 halvings below the width. The rest of the way would have to come from the extra-wall loop. Following every branch from an extra-wall state shows there is no ceiling: each meeting a run makes before it enters the plain loop adds 3 to 3s + 2λ and costs about 3.4 binary digits, against 2.5 per halving inside the loop. Among the machine's own two-marker segments, chains through the extra-wall loop found within 46 binary digits already enter 18.9 halvings below the width; all of them were checked and none halts. So the lock doesn't close the gap on its own. What it does is make about a third of the halvings a halt needs cost 3.4 digits instead of 2.5.</p>
        <p><b>The rarer loops leave a gap.</b> In the loop with an extra wall, a pass whose halving marker runs two rounds longer works as a detour. The pattern can resume after it, or the run can drop the extra wall and carry on in the plain loop. Each new stretch starts with a fresh left countdown, about 50 times E in size, while the right end keeps closing in. So the lock limits each stretch but not a run made of several. These chains are no cheaper: each further 4 meetings still costs 10 binary digits. In clean cycles the extra-wall states have a share of only about 4 in 10⁸. Among every residue class settled within 40 digits, 631 runs use the extra-wall loop, all of them short, and no run contains two stretches of any loop. A proof would need to rule chains out some other way, and the hand-built tapes below show that the rules alone can't.</p>
        <p><b>Why one loop is locked and a mixture isn't.</b> A pattern of rounds that repeats is an affine map, and over the ordinary numbers it pulls the state toward its fixed point. That point is a fraction with a fixed denominator, and when it isn't a whole-number state, the state's distance to it is a nonzero multiple of 1/D that shrinks every pass. So the pattern can only repeat a bounded number of times. The mod-7 lock is this, with the 7 coming from 63 = 64 − 1. The detour is a second 8-round pass whose map has irrational eigenvalues, (13 ± √153)/256. So no linear countdown locks the detour, but a quadratic one does: the product of its two eigenforms is an integer quadratic, never 0, that every detour divides by 4096, so a stretch of detours, like the plain loop, covers at most two thirds of the halvings. Every repeating word of standard passes and detours has a lock of this kind (checked for all 747 words up to length 12), and none covers more than 4/5 of the halvings. Each different order of standard passes and detours has its own fixed point, with its own denominator, so a long mixture has no single point to be held away from, and no lock for every mixture can exist: the hand-built tapes below halt at every width by a mixture. What the locks still say is that such a halt has to change words at least once, and each change starts a fresh lock. Such mixtures cost 16 to 18 binary digits per pass, against 10 for the plain loop.</p>
        <p><b>Every other repeating pattern parks short of the end.</b> I scanned the machine's runs for any sequence of rounds that repeats, in 4 × 10⁸ random two-marker states and about 200,000 of the machine's own cycles, and found 125 kinds. For each I read off its affine map and the point it pulls the marks toward. Only the plain loop and two-round pieces of the plain and extra-wall loops pull a mark onto the end; the pieces never repeat more than three times, and the extra-wall loop never ran two whole passes in these samples (its own pass map also pulls a mark onto the end, and it has a lock too). The other 118 settle a fixed fraction of the width short of the end, at most 7.9 halvings away, the staircase being the latest. So the only repetitions that can carry the right end toward a halt are the ones with a lock.</p>
      </div>
    <div class="two cleanrow">
      <div class="card">
        <table class="clean quick"><thead><tr><th scope="col">Tape width</th><th scope="col">Run at the end</th><th scope="col">Steps to halt</th></tr></thead><tbody>
          <tr><th scope="row">7.1 × 10¹⁶</th><td>53 meetings</td><td>9.3 × 10³⁴</td></tr>
          <tr><th scope="row">1.6 × 10⁶⁰</th><td>197 meetings</td><td>1.8 × 10¹²²</td></tr>
          <tr><th scope="row">about 2¹⁰⁰⁰</th><td>997 meetings</td><td>4.2 × 10⁶⁰⁴</td></tr>
        </tbody></table>
        <p class="small">Hand-built round starts with a gap and four walls, at 0.65%, 12.5%, 46% and 87% of the width. The run is a stretch of the extra-wall loop, one detour, and a second stretch. Each halt is reached through the proven rules alone, and each width is 3 more than a multiple of 6, so the tapes pass the mod-3 test from <a href="#h-big">The big picture</a> that every tape reached from blank must pass.</p>
      </div>
      <div class="prose">
        <p><b>With one detour the machine halts on tapes of any size.</b> I wrote the congruences that make a run follow the extra-wall loop for m passes, then one detour, then m more passes, and solved them as a lattice of starting tapes. Lattice reduction then finds one with the right proportions at any width. At 2²⁰⁰ cells one stretch of either loop is limited to about 35 passes and a halt needs about 50, so two stretches of 24 do it. The same recipe gives a halting tape at every width from 2¹⁶ to 2⁴⁰⁰ cells, each checked one by one, while the loop alone stops producing them above 2²⁷. On the two smallest, 67,431 and 131,487 cells wide, I also ran the bare transition table with no rules at all: it halts at steps 15,940,135,477 and 61,437,118,279, exactly as predicted. The machine then halts the same way every time: the meetings at the end run …, 14, 6, 2, 0, the last one is a swap that fuses the end marker into a block, and the carry halts on it.</p>
        <p>To run these tapes I used the proven rules themselves, checking the tape against each rule's pattern before applying it, so the step counts are exact. The same simulator matches direct simulation on 550 random small tapes and reproduces the 72-cell tape's 10,302 steps.</p>
        <p><b>So a proof has to use where the tapes come from.</b> Nothing in the rules stops a long run. What has kept every run short so far is that the machine's own tapes are not chosen freely. Each run starts from a family with a single free number, n, and a long run needs that one number to satisfy about two and a half binary conditions per meeting. A tape built by hand has four free positions, enough to satisfy them all. Nor does a conserved count rule these tapes out: they pass the mod-3 count of 1s, and a search for other counts of the same kind, weighting each cell by its value and its position modulo up to 6 and the head by its state, with moduli 2, 3, 5 and 7, finds none.</p>
        <p><b>A halt needs at least three free numbers; the machine's runs have two.</b> One stretch of the plain loop covers at most about two thirds of the meetings a halt needs, and it always ends the run. So at least the first third has to come from a pattern the lock does not cover: the extra-wall loop, at 14 binary conditions per 4 meetings, then a drop into the plain loop that keeps the progress made, then the plain stretch at 10 per 4. That averages 17/6, about 2.83 conditions per meeting. A family of tapes with d free numbers at width W can meet about d·log₂W conditions, and a halt needs about log₂W meetings, so it needs d above 2.83: at least three free numbers. Three do suffice. With one combination of the hand-built tapes' walls held fixed, so that three free numbers remain, the same lattice method finds a 2¹²⁰-cell tape on which the machine halts after ten extra-wall passes, a drop and eighteen plain passes, and tapes that halt the same way at every width tried, 2²⁴, 2³², 2⁴⁰, 2⁴⁸, 2⁶⁴, 2⁸⁰, 2⁹⁶, 2¹²⁸, 2¹⁶⁰ and 2²⁰⁰, while words made only of extra-wall passes and detours find nothing in that family at 2¹²⁰. On a 129,963-cell tape built the same way (one extra-wall pass, the drop, two plain passes), the bare transition table halts at step 75,047,708,436, exactly as the rules predict. The drops are picky: right after an extra-wall pass the simplest one is impossible, and most of the others leave the last wall between a half and a seventeenth of the tape from the end, losing all the progress. And every cycle from an even clean tape is, one round in, at a state with just the gap, one marker and the end marker, so everything after depends on two numbers (really one, n). And for such states the extra-wall loop is capped outright, not just made unlikely. Each of its passes has to keep three countdowns divisible by growing powers of 2, where the plain loop has two. A family with three free numbers can do that for as many passes as its size allows; in a two-number family the third countdown is tied to the other two by a fixed number, which then needs four more binary digits to line up for every pass. Random two-number families never allowed two passes in my tests, random three-number families allowed every word of five, and the 144 ways from a two-marker state into that loop within 30 binary digits allow at most one pass, decided by their position alone. Rarer ways in allow more, each extra pass about ten times rarer than the last: there are two-marker states about 2³⁵ cells wide whose segments run three extra-wall passes in a row, and they still come no closer to the end than 2⁻¹⁵ of the width. Even a chain that keeps its progress falls further behind as it goes: after two extra-wall passes and a drop, each further plain pass needs about 5 more binary digits of width before any two-marker state follows it, and buys only 4 halvings; the first state that adds 8 plain passes is 2⁷⁷ cells wide and stops 38 halvings short. Two-marker states in general have odds of ending within 2⁻ʰ of the width that fall by about 2.5 binary digits for each extra halving, at every width, and the machine's own tapes, a one-number line inside that family, have odds 20 to 30 times smaller still.</p>
        <div class="scroll"><table class="clean loops"><caption>How far each loop can run</caption><thead><tr><th scope="col">Loop</th><th scope="col">Count&shy;downs</th><th scope="col">2 free numbers (two-marker states)</th><th scope="col">1 free number (a cycle's own states)</th></tr></thead><tbody><tr><td>Plain</td><td>2</td><td>No fixed cap; the lock stops it at &#8532; of the halvings</td><td>Fixed cap per way in</td></tr><tr><td>1 extra wall</td><td>3</td><td>Fixed cap per way in</td><td>Fixed cap per way in</td></tr><tr><td><i>k</i> extra walls</td><td>2&#8239;+&#8239;<i>k</i></td><td>Fixed cap per way in</td><td>Fixed cap per way in</td></tr></tbody></table></div>
        <p class="note">Checked on random families of tapes for 0 to 3 extra walls: with fewer free numbers than countdowns, every family stopped after one pass (3 of 40 managed a second); with as many or more, every family ran every pass tried.</p>
        <p><b>None of this depends on where the marks sit.</b> Every rule places a new mark at the midpoint of two neighbouring marks, give or take a few cells, or moves marks by a few cells. Measure each mark by its distances to the marks that started out on the tape: if two neighbours are ordered in every one of those measures, so is their midpoint. So the left-to-right order of the marks is the same whatever the starting distances are, as long as they are large. For a two-marker state that means the whole tree of cases is the same wherever the marker sits; built at nine positions from 1/64 to 63/64 of the width, it came out identical, and none of its 250 million comparisons of two positions depends on the ratio. The same fact settles a loose end in the earlier analysis: the searches that fixed one geometry for convenience give the same answer for every geometry. It also bears on the touching marks the rules can't handle. Along every branch decided within 42 binary digits, the only two neighbouring marks that ever sit a fixed distance apart, rather than a distance that grows with the tape, are the end marker and the end itself: of 69 million neighbouring pairs checked, 13 million are that pair and no other pair ever is. So on a large tape, marks can touch only on a branch that needs more digits than that.</p>
        <p><b>Every halt would have to start from a two-marker state.</b> A cycle reaches its first two-marker state after one round (odd n go straight to the next clean tape in two fixed rounds), and from then on it is a chain of segments, each depending only on where its marker and end marker sit. So from any clean tape the machine can halt only by reaching a two-marker state whose own segment halts, a question about one fixed two-number family rather than about the states the machine happens to visit. I ran every two-marker state up to 262,143 cells wide through its segment, 8.6 billion of them, but left out the marker's last position, three cells before the end marker: only 7, all between 11 and 29 cells wide, get within 2 cells of the end or let marks touch, and on the real machine exactly one of those halts. It is 13 cells wide with the marker touching the gap, and its end meetings run 6, 2, 0. The last position holds two more halting states, 9 and 17 cells wide; at every other width up to 262,143 it reaches the clean tape, and the other narrowest gaps add no new halt. No cycle passes through any of the three: the narrowest two-marker state the machine reaches is 15 cells wide, and its segment leads to one 27 cells wide. The odds measured on random two-marker states predict about one halting state below 2¹⁶ (there are three, all tiny) and about 0.014 beyond 2¹⁸. For the commonest way into the loop, the one 230 of the 256 longest cascades below 2⁴⁹ take, the question can be settled at every size. That route always starts at a two-marker state, and a halt through it needs both of its countdowns to be divisible by large powers of 2, which pins the width to a residue of −38423/1225 and then the marker to one residue. Counted with two halvings to spare, that leaves 332,846 candidate states between 2¹⁷ and 2⁶¹ and none beyond, since the lock forbids it there. None of them halts, so within the mark rules no cycle can ever halt through that route. The best candidate, about 2⁴⁶ cells wide, runs the loop for 8 passes and gets to 1,030 cells from the end, within 2⁻³⁶ of the width, before its left countdown runs out, much closer than the machine's own record of about 2⁻¹⁵: that is what a second free number buys. The same argument works for any fixed way into the loop. Following every branch of a two-marker segment exactly gives 759,918 ways in that are decided within 46 binary digits (2,767 within 30). Of 1,020 random segments that come within 2⁻⁸ of the width, every one whose deepest run uses the loop, 1,019 of them, enters it by one of these, and already by one decided within 34 digits. Together they leave 866,445 candidates, and none of them halts either. (A first pass at this asked for a quarter pass too many at some widths, because a meeting can do slightly better than halve the distance; it was redone with two halvings to spare.) Chains fare no better: of the 31,048 first ways from a two-marker state into the extra-wall loop within those 46 digits, 1,635 allow one pass of it, 226 two, 21 three and one four, and the 1,989 ways those passes can drop back into the plain loop, 346 of them keeping their progress, leave no candidate state at any size. So within the mark rules, a run that enters the loop by any of these ways can never halt, at any size. The exact end of the loop now does this without any search. At each way in, 3s + 2λ depends only on where the marker sits as a fraction of the width, so each way has a ceiling, and a halt through it needs a tape narrower than 2 to the power of the ceiling plus 6.4. The commonest way has a ceiling of 16.0, so it can't lead to a halt on any tape wider than 2²²·⁴ cells. Following every branch to 62 binary digits, no way in has a ceiling above 52.9, so no two-marker state decided within 62 digits can halt on a tape wider than 2⁵⁹·² cells, which is still inside the checked range, though only just. The highest ceilings come from long lead-ins through pieces of the extra-wall loop; the top one enters the loop 15.1 halvings below the width, and I checked it and three others on rebuilt integer states. For that top route I also listed every state whose two countdowns line up exactly as a halt would need, at tape widths from 2⁴⁰ to 2⁶²: there are none. The same exact listing over all 232,456 ways in found within 46 digits, at every width from 2¹⁷ up to each one's lock limit, finds no state at all; the earlier version of that check had 866,445 looser candidates to run. The first way in past the threshold, found at 64 digits with a ceiling of 54.2, turns out to have R fixed at 12 more than a multiple of 16 by its own route, so it can neither pass nor close at any width. What stays open is the segments that need more than 62 digits to decide, about eight in ten billion of all two-marker states, a share that shrinks by 0.71 with each further digit; none of the deep runs sampled was among them. A halt of the machine also needs its own sequence to land on such a state; if its two-marker states hit them like random points, the expected number of halts beyond 2⁵⁵ is around 10⁻²⁵ to 10⁻²⁴, inside the range above, and that is before taking out the routes now excluded.</p>
        <p><b>The machine's own states start out special.</b> A cycle is a chain of segments, each running from one two-marker state to the next or to the clean tape, and each segment ends in another two-marker state with odds of about a third. Starting from a random two-marker state, any segment gets within 2⁻⁴ of the width with odds of about 1.5 in 1,000. On the machine's own tapes the first segment never does: following every residue class through it proves that its meetings stay at least 2<sup>−1.6</sup> of the width from the end. The second segment does so about 3 times in 10 million, and the odds then climb, reaching the random level only by the seventh to ninth segment. The reason is how few kinds of state come first. With the marker at cell m and the width E, the first two-marker state of every cycle lies on the line E = 2m + 7; the second lies on one of just two lines, E = 8m + 13 or 13E = 16m + 127; the third on dozens, the fourth on hundreds. Each return also brings about 3.5 new binary digits of n into the marker's position, while the width's low digits stay the few that the history allows. The record 14-meeting cycle below 2⁴⁹ has its long run in its eighth segment. The same returns are what make the exhaustive check expensive: the digits a class needs grow by about 3.5 per return, whether or not the cycle comes close to the end.</p>
        <p><b>On the machine's own tapes, each gap is a count of binary zeros.</b> There every position is λN + κ with N = 2n + 6, and λ and κ are fractions over the same power of 2. At a loop pass start, the difference between the two countdowns' targets, scaled by their slopes, is a number Δ: in all 878 pass starts reached from long-cascade clean tapes it is below 800. Each gap is the number of trailing zeros Δ has when written to as many binary places as λ. So for one stretch to finish the job, Δ must be a whole number, or nearly, with about as many trailing binary zeros as n still has unread digits at the pass start, give or take the few halvings the exit adds. With Δ below 800, that allows at most about 16 unread digits. The 256 longest cascades below 2⁴⁹ reach their first pass start with 2 to 19 digits unread, but their Δ's are far from whole: written out in binary they run to within 8 places of λ's, some 25 places past the point. Ruling out such a Δ for every n is a statement about binary digits of the same kind as the open questions about Collatz-type maps, where the odds are easy to estimate and no proof method is known.</p>
        <p><b>The commonest way into the loop has a ceiling.</b> Of all pass starts on the machine's tapes up to 38 binary digits, 90% come in by the same four rounds: a halving marker and the end marker, then three markers, then two markers and a wall, then a marker and two walls. For those the gap has a closed form, and it depends only on the tape's width W at the first of the four rounds: it is 3 less than the number of binary digits in which W agrees with the 2-adic number −38423/1225. (Every mark's line passes through the same 2-adic point, W itself, to as many digits as the class has read, and the halving marker's slope then cancels out.) On every such line up to 39 digits, all 308,333 of them, W agrees in at least 5 digits and never in 12, so this route's gap never exceeds 8. The route occurs only at particular stages of the cycle, each with a fixed growth g of the width since the clean tape: g = 23, 95, 119, 191, 215, 287 and 383 among all those found, with a search that follows the longest-lived residue classes out to 80 binary digits. At each stage the low digits a clean tape needs in order to get there stay a few places away from the digits of the 2-adic number (−38423/1225 − 6 − g)/2, and the best stage's gap is still 8. 230 of the 256 longest cascades below 2⁴⁹ come in this way, all at exactly that ceiling, which is why they stop after one or two passes. The larger gaps, up to 12 by 43 digits, come from rarer routes.</p>
      </div>
    </div>
    <figure class="card cd-fig">
      <h3 class="ch"><span class="chtext">The detour refills the countdown</span></h3>
      <div class="cd-wrap">{CD_SVG}<div class="cd-tip" id="cd-tip" role="tooltip" hidden></div></div>
      <figcaption class="cap"><span class="cd-key"><span class="cd-sw cd-swL"></span>Left countdown, the extra-wall loop's L at each pass start</span> <span class="cd-key"><span class="cd-sw cd-swR"></span>Distance from the last wall to the end</span><br>The 2²⁰⁰-cell tape from the table, which also passes the mod-3 test every tape reached from blank must pass. Each pass costs the countdown 6 binary digits and the distance 4. A single stretch would have run out of countdown at meeting 137, with the wall still about 2⁶⁰ cells from the end; the one detour pass resets the countdown to full size, and the second stretch carries the wall the rest of the way.</figcaption>
      {CD_TABLE}
    </figure>
    <script>
(function () {{
  const D = {CD_DATA}, svg = document.getElementById('cd-svg'), tip = document.getElementById('cd-tip'),
        cross = document.getElementById('cd-cross');
  if (!svg) return;
  const x0 = +svg.dataset.x0, x1 = +svg.dataset.x1, vb = svg.viewBox.baseVal;
  const fmt = v => v.toFixed(1).replace(/[.]0$/, '');
  function show(ev) {{
    const r = svg.getBoundingClientRect(), sx = (ev.clientX - r.left) * vb.width / r.width;
    const m = (sx - x0) / (x1 - x0) * 200;
    let best = D[0]; for (const d of D) if (Math.abs(d[0] - m) < Math.abs(best[0] - m)) best = d;
    const px = x0 + (x1 - x0) * best[0] / 200;
    cross.setAttribute('x1', px); cross.setAttribute('x2', px); cross.setAttribute('visibility', 'visible');
    tip.innerHTML = '<b>Meeting ' + best[0] + '</b><br><span class="k kL"></span>countdown about 2<sup>' + fmt(best[1]) +
      '</sup><br><span class="k kR"></span>distance about 2<sup>' + fmt(best[2]) + '</sup>';
    tip.hidden = false;
    const left = px * r.width / vb.width, w = tip.offsetWidth;
    tip.style.left = Math.min(Math.max(left + 12, 0), r.width - w) + 'px';
    tip.style.top = '8px';
    if (left + 12 + w > r.width) tip.style.left = Math.max(left - w - 12, 0) + 'px';
  }}
  function hide() {{ tip.hidden = true; cross.setAttribute('visibility', 'hidden'); }}
  svg.addEventListener('pointermove', show); svg.addEventListener('pointerleave', hide);
}})();
</script>
    <figure class="card cd-fig">
      <h3 class="ch"><span class="chtext">How the odds of a close approach fall</span></h3>
      <div class="cd-wrap">{OD_SVG}<div class="cd-tip" id="od-tip" role="tooltip" hidden></div></div>
      <figcaption class="cap"><span class="cd-key"><span class="cd-sw cd-swR"></span>All two-marker states (gap, a marker anywhere, the end marker)</span> <span class="cd-key"><span class="cd-sw cd-swL"></span>The ones the machine reaches (the marker just past half the width)</span><br>A billion random states of each kind, about 2⁴⁸ cells wide, run under the mark rules to the next clean tape; the share is out of each billion. Each extra halving costs both about 2.5 binary digits of odds, at every width tried from 2²⁴ to 2⁴⁸. For a single segment from a random two-marker state the odds can also be computed exactly, by following every binary branch to 46 digits: they match a count of all 6.4 billion states 2¹⁷ to 2¹⁸ cells wide, and fall exactly 10 binary digits per 4 halvings, the price of one pass of the plain loop. A halt on a tape of width W needs about log₂W halvings, so with 2.5 digits per halving a family needs more than 2.5 free numbers to keep producing candidates, and more than 17/6 once the lock forces the costlier patterns. The two-marker states have two, the machine's own tapes one.</figcaption>
      {OD_TABLE}
    </figure>
    <script>
(function () {{
  const D = {OD_DATA}, svg = document.getElementById('od-svg'), tip = document.getElementById('od-tip'),
        cross = document.getElementById('od-cross');
  if (!svg) return;
  const x0 = +svg.dataset.x0, x1 = +svg.dataset.x1, vb = svg.viewBox.baseVal;
  const cell = d => d ? d[0].toLocaleString('en-US') + ' (2<sup>' + d[1].toFixed(1) + '</sup>)' : 'none';
  function show(ev) {{
    const r = svg.getBoundingClientRect(), sx = (ev.clientX - r.left) * vb.width / r.width;
    let h = Math.round(2.5 + (sx - x0) / (x1 - x0) * 10); h = Math.min(12, Math.max(3, h));
    const px = x0 + (x1 - x0) * (h - 2.5) / 10;
    cross.setAttribute('x1', px); cross.setAttribute('x2', px); cross.setAttribute('visibility', 'visible');
    tip.innerHTML = '<b>h at least ' + h + '</b><br><span class="k kR"></span>all: ' + cell(D.plane[h]) +
      '<br><span class="k kL"></span>machine’s own: ' + cell(D.line[h]);
    tip.hidden = false;
    const left = px * r.width / vb.width, w = tip.offsetWidth;
    tip.style.left = Math.min(Math.max(left + 12, 0), r.width - w) + 'px';
    tip.style.top = '8px';
    if (left + 12 + w > r.width) tip.style.left = Math.max(left - w - 12, 0) + 'px';
  }}
  function hide() {{ tip.hidden = true; cross.setAttribute('visibility', 'hidden'); }}
  svg.addEventListener('pointermove', show); svg.addEventListener('pointerleave', hide);
}})();
</script>
    <figure class="card cd-fig">
      <h3 class="ch"><span class="chtext">Each return makes the machine's states more random</span></h3>
      <div class="cd-wrap">{SG_SVG}<div class="cd-tip" id="sg-tip" role="tooltip" hidden></div></div>
      <figcaption class="cap"><span class="cd-key"><span class="cd-sw cd-swR"></span>Cycles from random two-marker states (5 × 10⁷)</span> <span class="cd-key"><span class="cd-sw cd-swL"></span>Cycles from the machine's own clean tapes (2 × 10⁸)</span><br>A cycle is a chain of segments, each from one two-marker state to the next or to the clean tape; about a third of segments end in another two-marker state. Shown: among cycles that reach a given segment, the share in which that segment's closest meeting with the end is within 2⁻⁴ of the width. The machine's first two-marker state always lies on the line E = 2m + 7 and its second on one of two lines, so its early segments are tame; only after six or seven returns do its odds catch up with a random state's.</figcaption>
      {SG_TABLE}
    </figure>
    <script>
(function () {{
  const D = {SG_DATA}, svg = document.getElementById('sg-svg'), tip = document.getElementById('sg-tip'),
        cross = document.getElementById('sg-cross');
  if (!svg) return;
  const x0 = +svg.dataset.x0, x1 = +svg.dataset.x1, vb = svg.viewBox.baseVal;
  const ords = ['1st', '2nd', '3rd', '4th', '5th', '6th', '7th', '8th', '9th'];
  const cell = d => d[0] ? d[0].toLocaleString('en-US') + ' of ' + d[1].toLocaleString('en-US') : 'none of ' + d[1].toLocaleString('en-US');
  function show(ev) {{
    const r = svg.getBoundingClientRect(), sx = (ev.clientX - r.left) * vb.width / r.width;
    let k = Math.floor((sx - x0) / (x1 - x0) * 9); k = Math.min(8, Math.max(0, k));
    const px = x0 + (x1 - x0) * (k + 0.5) / 9;
    cross.setAttribute('x1', px); cross.setAttribute('x2', px); cross.setAttribute('visibility', 'visible');
    tip.innerHTML = '<b>' + ords[k] + ' segment</b><br><span class="k kR"></span>random: ' + cell(D[k].plane) +
      '<br><span class="k kL"></span>machine’s own: ' + (k === 0 ? 'never (proved)' : cell(D[k].line));
    tip.hidden = false;
    const left = px * r.width / vb.width, w = tip.offsetWidth;
    tip.style.left = Math.min(Math.max(left + 12, 0), r.width - w) + 'px';
    tip.style.top = '8px';
    if (left + 12 + w > r.width) tip.style.left = Math.max(left - w - 12, 0) + 'px';
  }}
  function hide() {{ tip.hidden = true; cross.setAttribute('visibility', 'hidden'); }}
  svg.addEventListener('pointermove', show); svg.addEventListener('pointerleave', hide);
}})();
</script>
  </section>

{established.section()}
  <section class="block" aria-labelledby="h-steps">
    <h2 id="h-steps">Where the steps go</h2>
    <div class="prose">
      <p>In the first 3 billion steps, 66.4% are carry steps and 33.2% are pass steps. The last 0.4% are turns (0.18%), gap steps (0.10%), other fixed sequences (0.09%) and shifts (0.03%).</p>
      <p>The 2-to-1 split comes from the bounce: the head crosses the same stripes once each way, at one step per cell going right and two coming back. In that stretch there were 522,285 marker turns, 441,791 wall turns, 807 swaps and 647 merges. Every swap started with a multiple of 4 stripe cells between the gap and the marker, and every merge with 2 more than a multiple of 4.</p>
    </div>
  </section>

  <footer>I couldn't find a published analysis of this machine, so the names and the account above are my own, worked out from the simulation. Every frame, rule sequence and count on this page was checked against a step-by-step simulation from a blank tape. The rules for the marks were proved from the rule table by running the machine on symbolic tapes. The statements about every n below 2⁵⁹ come from running those rules on whole residue classes of n, with every comparison a class makes recorded and checked.</footer>
</div>
'''

# ---------------------------------------------------------------- rule look-up: hover/tap tokens + floating reference
def rule_def(r):
    st, sym = r[0], int(r[1])
    txt, chips = RULES[st][sym]
    if txt == "---":
        return f"{st} reads {sym}: no rule, so the machine halts", chips
    w, d, n = txt[0], txt[1], txt[2]
    return f"{st} reads {sym}: write {w}, move {'right' if d == 'R' else 'left'}, go to {n}", chips

DEFS = {f"{s}{y}": dict(zip(("text", "chips"), rule_def(f"{s}{y}"))) for s in RULES for y in (0, 1)}
TOKEN = re.compile(r'(?<![A-Za-z0-9])([A-F][01])(?![A-Za-z0-9])')
SKIP = ("style", "script", "svg", "title", "code", "aside")
def wrap_tokens(doc):
    out, skip = [], []
    for part in re.split(r'(<[^>]+>)', doc):
        if part.startswith("<"):
            m = re.match(r'<(/?)([a-zA-Z0-9]+)', part)
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
    sws = "".join(f'<span class="sw {c}" title="{NAMES[c]}"></span>' for c in chips)
    if txt == "---":
        return f'<td data-r="{r}"><span class="rpc"><span class="mono"><b>halt</b></span><span class="sws">{sws}</span></span></td>'
    w, d, n = txt[0], txt[1], txt[2]
    return f'<td data-r="{r}"><span class="rpc"><span class="mono"><b>{w}</b> {"→" if d == "R" else "←"} <b>{n}</b></span><span class="sws">{sws}</span></span></td>'

OVERLAY_JS = open(os.path.join(S, "overlay.js")).read()
def overlay_html():
    rows = "".join(f'<tr><th scope="row">{s}</th>{panel_cell(s + "0")}{panel_cell(s + "1")}</tr>' for s in RULES)
    defs_js = json.dumps({k: {"text": v["text"], "chips": [[c, NAMES[c]] for c in v["chips"]]} for k, v in DEFS.items()})
    return f'''
<button type="button" class="rules-fab" id="rules-fab" aria-expanded="false" aria-controls="rules-panel"><span class="fab-grid" aria-hidden="true"></span>Rules</button>
<aside class="rules-panel" id="rules-panel" aria-label="Rule reference" hidden>
  <div class="rp-head"><b>The rule table</b><button type="button" class="rp-close" id="rp-close" aria-label="Close the rule reference">×</button></div>
  <table class="rp"><thead><tr><th></th><th scope="col">reads 0</th><th scope="col">reads 1</th></tr></thead><tbody>{rows}</tbody></table>
  <p class="rp-foot">Each cell: what to write, which way to move, and the next state. Squares show the routine.</p>
</aside>
<div class="rk-tip" id="rk-tip" role="tooltip" hidden></div>
<script>
const DEF = {defs_js};
{OVERLAY_JS}
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
open(OUT, "w").write(PRE + page + SUF)
print("ok", len(page), "bytes")
print("badge clearances:", sorted(COLLIDE, key=lambda c: c[2])[:8])
print("TOO CLOSE:", [c for c in COLLIDE if c[2] < 2])
print("cycle starts:", CYCLE_STARTS)
