"""Write README.md and status.json for the 14 machines of the block-list family that were analysed first (frames.FIRST)
from the shared analysis; f05_records.py then adds the part common to all 40 machines of the family.

The generated parts (Blank.lean claims, the triage run, the "shape" section of the explainer) come from
holdouts/gen.py as before; the rest is the family analysis, with the numbers of each machine taken from its
data/trajectory.json (trajectory.py) and data/round_check.txt (c/family events + check_rounds.py).

usage: python3 write_records.py [MACHINE ...]      (default: all 14)
"""
import html
import json
import os
import sys

PY = os.path.dirname(os.path.abspath(__file__))
M0DIR = os.path.dirname(PY)
HOLD = os.path.dirname(M0DIR)
REPO = os.path.dirname(HOLD)
sys.path.insert(0, PY)
sys.path.insert(0, HOLD)
sys.path.insert(0, os.path.join(REPO, "tools", "py"))
import frames  # noqa: E402
import gen  # noqa: E402
from bbtools.machine import Machine  # noqa: E402

M0 = frames.FAMILY[0][0]
CORE = "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_?---"
FAMILY_NAME = "Nested block counter (core 1RB0LC_0RC0RB_1LD0RE_0LE?LF_1LA0LB, frames A/B/X)"
SHARED = f"holdouts/{M0}"

# Runs that are literally the same from blank tape (same tapes at the same moments, up to a delay).
SAME_RUN = {
    "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---": ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---",
        "F0 = 0RE moves right into E at once; F0 = 1LB writes 1, steps left onto a 0 (B0 = 0RC), comes back "
        "and C1 = 0RE erases the 1: the same configuration two steps later. This needs a 0 left of the cell F "
        "reads, which holds at every F-event of the run (all of them sit in <code>...0100 0100 [F]0 010...</code>)."),
    "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---": ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---",
        "F0 = 1LB writes 1, steps left onto a 0 (B0 = 0RC), comes back and C1 = 0RE erases the 1: the "
        "configuration that F0 = 0RE reaches in one step, two steps later. This needs a 0 left of the cell F "
        "reads, which holds at every F-event of the run."),
    "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---": ("1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---",
        "The two tables differ in B1 (0RF / 1RF) and F0 (1RE / 1LD); from an F-event they reach the same "
        "configuration after the same number of steps, given a 0 next to the cell F reads (true at every F-event "
        "of the run), so the runs agree step for step."),
    "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---": ("1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---",
        "The two tables differ in B1 (1RF / 0RF) and F0 (1LD / 1RE); from an F-event they reach the same "
        "configuration after the same number of steps, given a 0 next to the cell F reads (true at every F-event "
        "of the run), so the runs agree step for step."),
}

# relatives with the same core in other folders (another group's machines)
RELATIVES = ["1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---",
             "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---",
             "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---", "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---"]

EFF = ["(+2)", "(&minus;4, +12)", "(&minus;4, &minus;18, +60)", "(&minus;4, &minus;18, &minus;90, +300)"]
EFF_MD = ["(+2)", "(-4, +12)", "(-4, -18, +60)", "(-4, -18, -90, +300)"]


def sup(n):
    return gen.fmt_html(n)


def pow10(x):
    """10^k for an exact power of ten, else the number with separators (html)."""
    s = f"{x:.0f}"
    if s.startswith("1") and set(s[1:]) <= {"0"} and len(s) > 4:
        return f"10<sup>{len(s) - 1}</sup>"
    return f"{x:,}"


def pow10_md(x):
    s = f"{x:.0f}"
    if s.startswith("1") and set(s[1:]) <= {"0"} and len(s) > 4:
        return f"10^{len(s) - 1}"
    return f"{x:,}"


def load(m):
    d = os.path.join(HOLD, m, "data")
    with open(os.path.join(d, "trajectory.json")) as f:
        tr = json.load(f)
    rc = None
    p = os.path.join(d, "round_check.txt")
    if os.path.exists(p):
        with open(p) as f:
            rc = f.read().strip()
    return tr, rc


def load_hy(m):
    with open(os.path.join(HOLD, m, "data", "hybrid.json")) as f:
        return json.load(f)


def sci(x, md=False):
    """'6.8053e+100' -> 6.8&middot;10<sup>100</sup>"""
    a, e = f"{float(x):.1e}".split("e")
    return f"{a}·10^{int(e)}" if md else f"{a}&middot;10<sup>{int(e)}</sup>"


VISIT_SVG = (
    '<svg viewBox="0 0 560 150" role="img" aria-label="a visit to blocks b1..bk calls five visits to the blocks '
    'after b1" style="width:100%;max-width:560px;height:auto;font:11px var(--mono);">'
    '<rect x="10" y="8" width="540" height="24" fill="none" stroke="var(--accent)"/>'
    '<text x="280" y="24" text-anchor="middle" fill="var(--accent)">visit [b1, b2, ..., bk]  (b1 odd: spread it, phase 1)</text>'
    + "".join(
        f'<rect x="{30 + 102 * i}" y="52" width="92" height="24" fill="none" stroke="var(--line)"/>'
        f'<text x="{76 + 102 * i}" y="68" text-anchor="middle" fill="var(--fg2)">visit #{i + 1}</text>'
        f'<text x="{76 + 102 * i}" y="94" text-anchor="middle" fill="var(--muted)">{t}</text>'
        for i, t in enumerate(["[b2+1, ...]", "tail +3", "tail +1", "tail +1", "tail +1"]))
    + '<text x="280" y="122" text-anchor="middle" fill="var(--fg2)">each visit #i is the same thing one level down: '
    'five visits to [b3, ...], and so on</text>'
    '<text x="280" y="140" text-anchor="middle" fill="var(--muted)">after the fifth: POP turns the spread b1 back '
    'into the plain block b1 &#8722; 5</text>'
    '</svg>')


def own_state(fr, s):
    return frames.frame_map(fr)[s]


def table_md(m):
    t = frames.parse(m)
    rows = ["| state | read 0 | read 1 |", "|---|---|---|"]
    for s in frames.STATES:
        c = []
        for y in (0, 1):
            x = t[(s, y)]
            c.append("---" if x is None else f"{x[0]}{x[1]}{x[2]}")
        rows.append(f"| {s} | {c[0]} | {c[1]} |")
    return "\n".join(rows)


def family_table_html(me):
    head = ("<div style=\"overflow-x:auto\"><table class=\"tbl\"><thead><tr><th>machine</th><th>frame</th>"
            "<th>F0 in frame A</th><th>D1</th><th>starts in</th><th>F-events to 10<sup>11</sup></th></tr></thead><tbody>")
    rows = []
    for m, fr, fa, st in frames.FIRST:
        try:
            tr, _ = load(m)
            nf = str(len(tr["f_events"]))
        except OSError:
            nf = "?"
        g = fa.split("_")
        name = m if m == me else f'<a href="../{m}/explainer.html">{m}</a>'
        b = ("<b>", "</b>") if m == me else ("", "")
        rows.append(f"<tr><td><code>{b[0]}{name}{b[1]}</code></td><td>{fr}</td><td>{g[5][:3]}</td><td>{g[3][3:]}</td>"
                    f"<td>{st}</td><td>{nf}</td></tr>")
    return head + "".join(rows) + "</tbody></table></div>"


def family_table_md(me):
    rows = ["| machine | frame | F0 in frame A | D1 | frame-A start | F-events to 10^11 |", "|---|---|---|---|---|---|"]
    for m, fr, fa, st in frames.FIRST:
        try:
            tr, _ = load(m)
            nf = str(len(tr["f_events"]))
        except OSError:
            nf = "?"
        g = fa.split("_")
        name = f"**{m}**" if m == me else f"[{m}](../{m}/README.md)"
        rows.append(f"| {name} | {fr} | {g[5][:3]} | {g[3][3:]} | {st} | {nf} |")
    return "\n".join(rows)


TAPE_SVG = (
    '<svg viewBox="0 0 560 92" role="img" aria-label="the tape at an event: spread blocks on the left, the head, '
    'plain blocks on the right" style="width:100%;max-width:560px;height:auto;font:11px var(--mono);">'
    '<rect x="4" y="20" width="150" height="26" fill="none" stroke="var(--line)"/>'
    '<text x="79" y="37" text-anchor="middle" fill="var(--fg2)">(1000)^q &#8230;</text>'
    '<rect x="158" y="20" width="50" height="26" fill="none" stroke="var(--line)"/>'
    '<text x="183" y="37" text-anchor="middle" fill="var(--fg2)">tail</text>'
    '<text x="222" y="37" text-anchor="middle" fill="var(--head)">A&gt;0</text>'
    '<rect x="240" y="20" width="96" height="26" fill="none" stroke="var(--accent)"/>'
    '<text x="288" y="37" text-anchor="middle" fill="var(--accent)">(10)^b1</text>'
    '<text x="344" y="37" text-anchor="middle" fill="var(--fg2)">1</text>'
    '<rect x="352" y="20" width="80" height="26" fill="none" stroke="var(--accent)"/>'
    '<text x="392" y="37" text-anchor="middle" fill="var(--accent)">(10)^b2</text>'
    '<text x="442" y="37" text-anchor="middle" fill="var(--fg2)">1 &#8230; 1</text>'
    '<rect x="464" y="20" width="60" height="26" fill="none" stroke="var(--accent)"/>'
    '<text x="494" y="37" text-anchor="middle" fill="var(--accent)">(10)^bk</text>'
    '<text x="540" y="37" text-anchor="middle" fill="var(--fg2)">1 0&#8734;</text>'
    '<text x="4" y="68" fill="var(--muted)">spread block (left sweep A,C,D,E: 4 steps per 1000)</text>'
    '<text x="240" y="84" fill="var(--muted)">plain blocks (right sweep B: 6 steps per 1010 &#8594; 0100)</text>'
    '</svg>')


def top_table_html(tr, n_first=9, n_last=6):
    ev = tr["top_events"]
    pick = ev if len(ev) <= n_first + n_last else ev[:n_first] + [None] + ev[-n_last:]
    rows = []
    for e in pick:
        if e is None:
            rows.append("<tr><td>&#8230;</td><td></td><td></td></tr>")
            continue
        rows.append(f"<tr><td>{e['step']:,}</td><td>{-e['left_end']}</td><td><code>{e['blocks']}</code></td></tr>")
    return ("<div style=\"overflow-x:auto\"><table class=\"tbl\"><thead><tr><th>step</th><th>cells left of start"
            "</th><th>blocks b1, b2, &#8230;</th></tr></thead><tbody>" + "".join(rows) + "</tbody></table></div>")


def top_table_md(tr):
    rows = ["| step | cells left of start | blocks |", "|---|---|---|"]
    for e in tr["top_events"]:
        rows.append(f"| {e['step']:,} | {-e['left_end']} | `{e['blocks']}` |")
    return "\n".join(rows)


def fev_summary(tr):
    fe = [e for e in tr["f_events"] if not e.get("halt")]
    ctx = {}
    for e in fe:
        k = e["left"][-12:] + "[F]" + e["right"][:7]
        ctx[k] = ctx.get(k, 0) + 1
    zeros = all(e["reads"] == 0 for e in fe)
    return fe, ctx, zeros


def records(m):
    fr, fa, st = frames.info(m)
    mp = frames.frame_map(fr)
    by = {r["machine"]: r for r in gen.load_triage()}
    row = by[m]
    mach = Machine.parse(m)
    base = gen.status_spec(row, mach)
    tr, rc = load(m)
    hy = load_hy(m)
    fe, ctx, zeros = fev_summary(tr)
    hs, hs_md = sci(hy["steps"]), sci(hy["steps"], md=True)
    hv = hy["validated_against"]
    h_ok = hv["left_end_match"] and hv["f_match"] and hy["f_reads_one"] == 0 and not hy["halted"]
    h_ctx = "; ".join(f"<code>{html.escape(c['context'])}</code> ({c['count']}&times;)" for c in hy["f_contexts"])
    h_ctx_md = "; ".join(f"`{c['context']}` ({c['count']}x)" for c in hy["f_contexts"])
    ns = gen.ns_of(row)
    N = tr["steps"]
    Nr = float(f"{N:.0e}") if abs(N - float(f'{N:.0e}')) < 1e6 else N
    nb = pow10(Nr)
    nb_md = pow10_md(Nr)
    f0a = fa.split("_")[5][:3]
    d1a = fa.split("_")[3][3:]
    own_f = own_state(fr, "F")
    halting = f"{own_f}1"
    is_m0 = m == M0
    # F-events
    first_f = fe[0]["step"] if fe else None
    f_steps = ", ".join(f"{e['step']:,}" for e in fe)
    ctx_html = "; ".join(f"<code>{html.escape(k)}</code> ({v}&times;)" for k, v in ctx.items())
    ctx_md = "; ".join(f"`{k}` ({v}x)" for k, v in ctx.items())
    same = SAME_RUN.get(m)
    tops = tr["top_events"]
    # frame sentence
    if fr == "A":
        frame_html = (f"This machine is written in <b>frame A</b>, the frame the analysis uses: states A to E do all "
                      f"the work, D1 = {d1a} is the only way into F, F0 = {f0a} is this machine's own transition, "
                      f"and F1 halts.")
        frame_md = (f"This machine is written in **frame A**, the frame the analysis uses: states A to E do all the "
                    f"work, D1 = {d1a} is the only way into F, F0 = {f0a} is this machine's own transition, and F1 "
                    f"halts.")
    else:
        ren = ", ".join(f"{s}&rarr;{mp[s]}" for s in frames.STATES)
        ren_md = ", ".join(f"{s}->{mp[s]}" for s in frames.STATES)
        frame_html = (f"This machine is in <b>frame {fr}</b>: its table is the mirror image (L and R exchanged) of "
                      f"the frame-A table <code>{fa}</code> with the states renamed {ren}, and it starts where that "
                      f"machine would be in state {st}. So its run from blank tape is, step for step and mirrored, "
                      f"the run of <code>{fa}</code> started in {st} (checked from the two tables by "
                      f"<code>frames.py</code> and by simulation). The F-transition of the analysis is this "
                      f"machine's {mp['D']}1, the halting state is {own_f}.")
        frame_md = (f"This machine is in **frame {fr}**: its table is the mirror image (L and R exchanged) of the "
                    f"frame-A table `{fa}` with the states renamed {ren_md}, and it starts where that machine would "
                    f"be in state {st}. So its run from blank tape is, step for step and mirrored, the run of `{fa}` "
                    f"started in {st} (checked from the two tables by `frames.py`, and by simulation). Below, states "
                    f"are named as in frame A; the F-transition of the analysis is this machine's {mp['D']}1, the "
                    f"halting state is {own_f}.")
    same_html = same_md = ""
    if same:
        same_html = (f"<p><b>Same run as <a href=\"../{same[0]}/explainer.html\"><code>{same[0]}</code></a>.</b> "
                     f"{same[1]}</p>")
        same_md = f"**Same run as [{same[0]}](../{same[0]}/README.md).** " + html.unescape(
            same[1].replace("<code>", "`").replace("</code>", "`"))
    rc_line = rc or "not run"
    # ---- claims
    claims = base["claims"][:4]
    claims += [
        {"level": "trusted", "title": "One of 14 machines with the same five-state core",
         "text": (f"States A to E of every machine of the family are the core {CORE} (in frame A); the machines "
                  f"differ in F0 and the start state, and some are mirror images. "
                  + ("This one is frame A itself." if fr == "A" else
                     f"This one is the mirror image of <code>{fa}</code>, renamed, started in its state {st}.")),
         "where": f"<code>{SHARED}/py/frames.py</code>, <code>py/conjugacy_steps.py</code>"},
    ]
    if same:
        claims.append({"level": "trusted", "title": f"Same run from blank as {same[0]}",
                       "text": same[1] + f" Checked on tape snapshots to 2&middot;10<sup>8</sup> steps.",
                       "where": f"<code>{SHARED}/c/family.c snapshot</code>"})
    claims += [
        {"level": "kernel", "title": "The visit rule for every depth",
         "text": ("A <em>visit</em> starts with the head in state A on the 0 in front of plain blocks "
                  "<code>(10)^b1 1 (10)^b2 1 &#8230; 1</code> and ends when it first steps left of that cell; it never "
                  "reads the tape on its left. <code>go_spec</code> proves, by induction on the depth n and for every "
                  "left context, that a <em>clean</em> visit (a decidable condition: every block it spreads is odd and "
                  "&ge; 7, every second block nonempty) turns the list l into <code>go n l</code> in exactly "
                  "<code>goT n l</code> steps, where <code>go</code> is the recursion: spread b1, five visits to "
                  "[b2+1, b3, &#8230;] with the tail bumps +3, +1, +1, +1 between them, then b1&minus;5. It is built "
                  "from seven rules (PUSH, TURN, TAIL1&ndash;4, POP) proved by bbtools.symtm for all counts."),
         "where": "<code>go_spec</code>, <code>push</code> &#8230; <code>pop</code>, <code>lean/Family.lean</code>"},
        {"level": "kernel", "title": "Its closed form",
         "text": ("<code>go_closed</code>: if b1 is odd and &ge; 7 and the later blocks are even, the last &ge; 2 and "
                  "block i (i = 2..k&minus;1) &ge; 2 + 18&middot;5<sup>i&minus;2</sup>, then the visit is clean and gives "
                  "(b1&minus;5, b2&minus;18, b3&minus;90, &#8230;, b<sub>k&minus;1</sub>&minus;18&middot;5<sup>k&minus;3</sup>, "
                  "b<sub>k</sub>+12&middot;5<sup>k&minus;2</sup>) (a single odd block gains 1); <code>visit_closed</code> "
                  "states it on the tape. With the tail bump after the visit this is the measured round rule "
                  "(&minus;4, &minus;18, &#8230;, +12&middot;5<sup>m&minus;2</sup>) for every m."),
         "where": "<code>go_closed</code>, <code>visit_closed</code>, <code>lean/Family.lean</code>; closed step count in "
                  f"<code>{SHARED}/py/cf.py</code> (trusted)"},
        {"level": "kernel", "title": "Rounds, births and the F-event",
         "text": ("<code>round1</code>&ndash;<code>round4</code>: a clean visit followed by one phase of the tail on its "
                  "left. <code>birth</code>: a visit to a single even block [2k+4] gives [2k+2, 8] in 10k+188 steps (where "
                  "new blocks come from). <code>fevent</code> and <code>fevent_reads_zero</code>: the only way into F "
                  "seen in the runs (a C exit onto the 0 of a phase-1 tail, then C0, D1) makes F read the last cell of a "
                  "<code>1000</code> or of <code>100</code>, which is 0 for every q and every tape around."),
         "where": "<code>round1</code> &#8230; <code>birth</code>, <code>fevent_reads_zero</code>, <code>lean/Family.lean</code>"},
        {"level": "kernel", "title": "The rules hold for this machine's own table",
         "text": ("The rules are proved on the frame-A table <code>FA.trans</code>. "
                  + ("This machine is frame A; " if fr == "A" else
                     "This machine is its mirror image: the map <code>img</code> (mirror the tape, rename the states) "
                     "sends every frame-A step to a step of this machine (<code>step_img</code>, <code>steps_img</code>); ")
                  + "<code>halts_iff</code> says that this machine halts from blank tape iff the frame-A table halts "
                  f"from blank in state {st}, and <code>visit</code> restates <code>go_spec</code> for this machine."),
         "where": "<code>halts_iff</code>, <code>visit</code>, <code>lean/Family.lean</code>"},
        {"level": "kernel", "title": "The round rule on one and two blocks (first pass)",
         "text": ("Eight theorems on the machine's own table: a round on the last block changes it by +2 (+4 from "
                  "phase 1), on the last two by (&minus;4, +12), for each phase, with exact step counts. Now special "
                  "cases of the rules above."),
         "where": "<code>round_m1_p1</code> &#8230; <code>round_m2_p4</code>, <code>lean/Rules.lean</code>"},
        {"level": "trusted", "title": f"The events follow the round rule",
         "text": (f"Listing every event (A turning right with plain blocks on its right) and comparing consecutive "
                  f"ones: {html.escape(rc_line)}. The few exceptions (X) are the left end, the birth of a new last block, "
                  f"the merge after a block runs out, and the F-events."),
         "where": f"<code>{SHARED}/c/family.c events</code>, <code>{SHARED}/py/check_rounds.py</code>"},
        {"level": "trusted", "title": f"No halt in the first {nb} steps",
         "text": (f"The exact run-length simulator (macro steps over <code>(10)^n</code>, <code>(1000)^n</code>, checked "
                  f"against plain simulation) runs {N:,} steps from blank tape without a halt. It meets {len(tops)} "
                  f"left-end events and {len(fe)} F-events" + (f" (first at step {first_f:,})" if first_f else "") +
                  (", and at every F-event the cell F reads is 0." if zeros else ".")),
         "where": f"<code>data/trajectory.json</code>, <code>{SHARED}/py/trajectory.py</code>"},
    ]
    if is_m0:
        claims.append({"level": "trusted", "title": "No halt in the first 10<sup>12</sup> steps",
                       "text": ("The same simulator runs 10<sup>12</sup> steps (about an hour): 13 F-events, at steps "
                                "39,734, 84,610, 7,423,096, 61,170,138, 83,341,005, 19,760,364,771, &#8230;, "
                                "49,599,980,477, 92,401,008,442, all reading 0."),
                       "where": f"<code>{SHARED}/py/rle.py</code> (<code>watch</code>)"})
    claims += [
        {"level": "trusted", "title": "The whole run as an exact map on block lists",
         "text": ("<code>hybrid.py</code> runs the machine as a map on block lists: clean visits by the closed form "
                  "(a theorem), every other visit (small or even first blocks, merges after a block runs out, births, "
                  "the left end) by the exact run-length simulator, recursively and memoised. It is exact, not a model: "
                  f"against <code>data/trajectory.json</code> ({hv['trajectory_steps']:,} steps of the machine) it "
                  f"reproduces all {hv['left_end_events']} left-end events (step and block list) and all "
                  f"{hv['f_events']} F-events (step and cell read)"
                  + (" (apart from one extra logged visit to [0] at step 4)" if hv["left_end_extra_initial"] else "")
                  + ("." if hv["left_end_match"] and hv["f_match"] else " &mdash; MISMATCH, see data/hybrid.json.")),
         "where": f"<code>{SHARED}/py/hybrid.py</code>, <code>{SHARED}/py/hybrid_run.py</code>, <code>data/hybrid.json</code>"},
        {"level": "trusted", "title": f"No halt in the first {hs} steps",
         "text": (f"The exact map runs {hs} steps ({hy['seconds']:.0f} s): {hy['left_end_events']} left-end events, "
                  f"{hy['f_events_count']} F-events, every one reading 0 and every one of the proved kind ({h_ctx}). "
                  "The block list grows to about 40 blocks, block i of size about 5<sup>i</sup>.")
                 + (" The same run to 1.0&middot;10<sup>200</sup> steps (2 minutes): 505 left-end events, 278 F-events, "
                    "no halt." if is_m0 else ""),
         "where": "<code>data/hybrid.json</code>" + (", <code>data/hybrid_1e200.txt</code>" if is_m0 else "")},
        {"level": "heuristic", "title": "Where a halt would have to come from",
         "text": ("F is entered only by D1 (D reads a 1 during the left sweep, where a spread block is turned back), "
                  f"and halts only when it then reads a 1. In this run every F-event has the same clean context ({ctx_html}). "
                  "Random block lists do reach a halting F-event (about 1 in 150 F-entries; e.g. "
                  "<code>[15, 31, 17, 59, 31]</code> halts after 63,153 steps), so the halt is reachable in principle; "
                  "whether the blank-tape run ever produces such a list is the open part. F-events get rarer as the "
                  "blocks grow (the top-level round time grows about fivefold per block)."),
         "where": f"<code>{SHARED}/py/random_lists.py</code>"},
        {"level": "open", "title": "Does it halt from blank tape?",
         "text": ("Not known. The visit rule is proved for every depth, its closed form, births and the F-event "
                  "too; what is missing is a proof that the unclean visits of the blank-tape run (merges, small "
                  "first blocks, the left end) always end in a C exit of the proved kind and never in an F exit onto a "
                  "1, that is an invariant on the block lists reached from blank tape."),
         "where": "README.md, Further work"},
    ]
    claims += [base["claims"][4]]  # growth shape (heuristic)
    # ---- explainer sections
    sec_family = {
        "id": "family", "eyebrow": "The family", "heading": "The fourteen machines of the first pass",
        "html": [f"<p>{frame_html}</p>",
                 "<p>The table below lists the family. Frame B machines are mirror images of frame-A ones started in "
                 "state C; the X machine is a mirror image started in F (and its D1 writes 1). Different F0 or start "
                 "states give different runs after the first F-event, but the same rules between F-events.</p>",
                 family_table_html(m), same_html,
                 "<p>The shared analysis code is in the folder of <a href=\"../" + M0 + "/explainer.html\"><code>" + M0 +
                 "</code></a> (<code>py/</code>, <code>c/</code>). Other holdouts with the same core, for example "
                 + ", ".join(f"<a href=\"../{r}/explainer.html\"><code>{r}</code></a>" for r in RELATIVES[:3])
                 + ", are studied in another group.</p>"]}
    sec_blocks = {
        "id": "blocks", "eyebrow": "The mechanism", "heading": "Blocks of 10 and a nested counter",
        "html": ["<p>Away from rare moments the tape (in frame A) is a list of <em>blocks</em>: runs "
                 "<code>(10)^b</code> separated by single 1s. At an <em>event</em> the head, in state A, has just turned "
                 "right at the left edge of the blocks it is about to work on; everything to its left is spread out as "
                 "<code>(1000)^q</code> ending in a short tail.</p>", TAPE_SVG,
                 "<p>A <em>round</em> on the last m blocks runs the head right over them (state B, six steps per "
                 "<code>1010</code>, which becomes <code>0100</code>) and back (states E, A, C, D, four steps per "
                 "<code>1000</code>). A round on blocks j..k contains five rounds on blocks j+1..k, so the work is "
                 "nested like a counter in base 5, and a round on the last m blocks changes them by:</p>"
                 "<div style=\"overflow-x:auto\"><table class=\"tbl\"><thead><tr><th>blocks</th><th>change</th><th>steps</th>"
                 "<th>proved</th></tr></thead><tbody>"
                 "<tr><td>1</td><td>(+2)</td><td>10u+59 (&asymp;5b)</td><td>Lean kernel</td></tr>"
                 "<tr><td>2</td><td>(&minus;4, +12)</td><td>10u<sub>0</sub>+50u<sub>1</sub>+485 (&asymp;5b<sub>1</sub>+25b<sub>2</sub>)</td><td>Lean kernel</td></tr>"
                 "<tr><td>3</td><td>(&minus;4, &minus;18, +60)</td><td>&asymp;5b<sub>1</sub>+25b<sub>2</sub>+125b<sub>3</sub></td><td>Lean kernel</td></tr>"
                 "<tr><td>m</td><td>(&minus;4, &minus;18, &minus;90, &#8230;, &minus;18&middot;5<sup>m&minus;3</sup>, +12&middot;5<sup>m&minus;2</sup>)</td>"
                 "<td>&asymp;&Sigma; 5<sup>i</sup>b<sub>i</sub></td><td>Lean kernel, every m</td></tr></tbody></table></div>",
                 "<p>(From phase 1 of the tail the first block gets 2 more.) After the round the tail on the left has "
                 "moved one phase on (<code>10, 1, 1001, 101, 11</code>); after five phases one <code>1000</code> of "
                 "the spread block on the left is used up, which is how the deeper block counts down. "
                 f"Between consecutive events of this run: {html.escape(rc_line)}.</p>"]}
    sec_visits = {
        "id": "visits", "eyebrow": "The whole run", "heading": "A visit calls five visits",
        "html": ["<p>Cut the run into <em>visits</em>: a visit starts when the head (state A) stands just left of a list "
                 "of plain blocks and ends when it steps back out to the left. It never looks at the tape on its left, so "
                 "its outcome depends on the list alone. A visit to [b1, b2, &#8230;, bk] with b1 odd spreads b1 (PUSH), "
                 "then makes five visits to the shorter list [b2+1, b3, &#8230;], nudging the tail between them "
                 "(+3, +1, +1, +1), and finally folds b1 back up, 5 smaller (POP). That is a counter in base 5, "
                 "and it is now a Lean theorem for every depth.</p>", VISIT_SVG,
                 "<p>When the blocks are big enough the whole visit has a closed form: b1 loses 5, block i loses "
                 "18&middot;5<sup>i&minus;2</sup>, the last gains 12&middot;5<sup>k&minus;2</sup>, in about "
                 "&Sigma; 5<sup>i+1</sup>b<sub>i</sub> steps (also proved). The rest are exceptions: a single even "
                 "block gives birth to a new last block 8 (proved), a block that runs out merges with its neighbour, and "
                 "the left end sees an even first block.</p>",
                 f"<p>Doing clean visits by formula and only the exceptions cell by cell gives an exact simulator of the "
                 f"machine that reaches {hs} steps in {hy['seconds']:.0f} seconds; it agrees with the plain simulation "
                 f"event for event for the first 10<sup>11</sup> steps.</p>"]}
    sec_top = {
        "id": "leftend", "eyebrow": "The top level", "heading": "What the left end sees",
        "html": ["<p>Each time the head comes back to the left end of the tape it starts a round on the whole list "
                 "and the tape grows by 3 cells on the left. At these moments the block list is:</p>",
                 top_table_html(tr),
                 "<p>Between left-end events b<sub>2</sub> drops by 18, b<sub>3</sub> by about 90, b<sub>4</sub> by about 450 (the round "
                 "rule seen from the top), while a new last block is born or grows. When a block runs out the list "
                 "shortens and its neighbours merge; these steps, and the births, are the part of the map that is "
                 "handled exactly by the simulator but not yet written as closed rules. Values such as 296, 524, 1136, 37496 recur in several machines of "
                 "the family: they are fixed outcomes of a block being born.</p>"]}
    halt_html = [f"<p>Only D1 enters F; F1 halts, F0 = {f0a} (frame A) lets the run go on. In {hs} steps of the exact "
                 f"map there are {hy['f_events_count']} F-events, all reading 0, of two kinds: {h_ctx}.</p>",
                 "<p>All of them happen the same way: an unclean visit ends in state C instead of B, on the 0 of a "
                 "spread block's tail <code>10</code>. C0 writes 1 and steps left onto the tail's 1, D1 sends the head "
                 "into F one cell further left, and that cell is the last 0 of a <code>1000</code> (or of the "
                 "<code>100</code> that starts a spread block). This is proved for every tape around "
                 "(<code>fevent_reads_zero</code>), so these F-events can never halt.</p>",
                 "<p>A halt would need a different way in: an unclean visit that exits into F directly, or a C exit "
                 "onto some other tail. Random block lists do that now and then (about once per 150 F-entries), so the "
                 "question is whether the lists that the blank-tape run builds avoid it forever. Nobody has proved "
                 "that.</p>"]
    sec_halt = {"id": "halting", "eyebrow": "The halting condition", "heading": "Where a halt could come from",
                "html": halt_html}
    shape = base["explainer"]["sections"][0]
    lede = (f"Nobody knows, but the machinery is clear. In frame A the tape is a list of blocks <code>(10)^b</code>; the "
            f"head works through them like a nested counter in base 5, and the only way to halt is a rare "
            f"<em>F-event</em> going wrong. The counter is proved in Lean for every depth; run as an exact map on block lists it "
            f"reaches {hs} steps and meets {hy['f_events_count']} F-events, all harmless."
            + ("" if fr == "A" else f" This machine is the mirror image of <code>{fa}</code>, started in its state {st}."))
    facts = [
        {"level": "kernel", "value": "every depth", "text": "The visit rule (a visit calls five visits) and its closed form, in Lean (Family.lean)."},
        {"level": "trusted", "value": f"{hs} steps",
         "text": f"No halt in the exact map on block lists; {hy['f_events_count']} F-events, all reading 0."},
        {"level": "trusted", "value": f"{len(tops)} top events", "text": "Visits of the head to the left end, each a round on the whole list."},
    ]
    if is_m0:
        facts[1] = {"level": "trusted", "value": "10<sup>200</sup> steps",
                    "text": "No halt in the exact map on block lists; 278 F-events, all reading 0."}
    if same:
        facts.append({"level": "trusted", "value": "same run", "text": f"As {same[0]} from blank tape."})
    summary = ("Block counter: in frame A the tape is a list of (10)^b blocks run like a base-5 nested counter "
               f"(visit rule for every depth and its closed form in Lean); halting needs a rare F-event (D1) to read a 1. "
               + ("" if fr == "A" else f"Mirror image of {fa} started in {st}. ")
               + (f"Same run as {same[0]}. " if same else "")
               + f"No halt in {'10^200' if is_m0 else hs_md} steps of the exact block-list map, all F-events clean.")
    verdict = [f"<b>The question is open.</b> {frame_html} The nested counter that drives the run is proved in Lean "
               f"for every depth (<code>go_spec</code>), with its closed form, the birth of blocks and the F-event; the "
               f"remaining exceptions (merges, the left end) are simulated exactly. No halt in "
               f"{'10<sup>200</sup>' if is_m0 else hs} steps: every F-event so far is of the proved harmless kind."]
    spec = dict(base)
    spec.update({
        "generated": False,
        "family": FAMILY_NAME,
        "summary": summary,
        "decision": "open",
        "verdict": verdict,
        "claims": claims,
        "check": [". /etc/profile.d/lean.sh      # after scripts/setup-lean.sh",
                  f"holdouts/{m}/lean/check.sh",
                  f"python3 {SHARED}/py/gen_family_lean.py {m} {ns} > holdouts/{m}/lean/Family.lean",
                  f"python3 {SHARED}/py/hybrid_run.py {m} 1e100     # writes data/hybrid.json",
                  f"python3 {SHARED}/py/gen_lean.py {m} {gen.ns_of(row)} > holdouts/{m}/lean/Rules.lean",
                  f"python3 {SHARED}/py/trajectory.py {m} 1e11 holdouts/{m}/data/trajectory.json",
                  f"cc -O2 -o family {SHARED}/c/family.c && ./family events {fa}:{st} 1e8 > ev.txt && "
                  f"python3 {SHARED}/py/check_rounds.py ev.txt"],
    })
    spec["explainer"] = dict(base["explainer"])
    spec["explainer"].update({"lede": lede, "facts": facts,
                              "sections": [sec_family, sec_blocks, sec_visits, sec_top, sec_halt, shape]})
    # ---- README
    lvl = "\n".join(f"| {c['level']} | **{strip(c['title'])}.** {strip(c['text'])} | {strip(c['where'])} |" for c in claims)
    readme = f"""# {m}

bbchallenge id {row['id']}. One of the six-state holdouts whose halting from blank tape is open. Group G01.
**Family:** {FAMILY_NAME}. The shared analysis code is in [`{SHARED}`](../{M0}/) (`py/`, `c/`).

{table_md(m)}

## What it does

{frame_md}

{same_md}

All 14 machines of the family share this five-state core (frame A: `{CORE}`):

{family_table_md(m)}

Related holdouts with the same core but a different D1 or F0 (another group): {", ".join(f"`{r}`" for r in RELATIVES)}.

### Blocks and rounds

In frame A, away from rare moments, the tape is a list of blocks `(10)^b` separated by single 1s. At an *event*
the head is in state A on a 0 right after moving left, and the tape is

    0^inf (1000)^q  tail  A> 0 (10)^b_j 1 (10)^b_(j+1) 1 ... (10)^b_k 1 0^inf

where the blocks left of the head are *spread* as `(1000)^q` and the tail is in one of five phases
`10, 1, 1001, 101, 11`. A *round* runs right over the plain blocks (B: six steps per `1010`, which becomes
`0100`) and back (E, A, C, D: four steps per `1000`). A round on blocks j..k contains five rounds on blocks
j+1..k, so the blocks form a nested counter in base 5. A round on the last m blocks advances the tail one phase and
changes the blocks by (u is about half a block value, the theorems state the exact offsets)

| m | change | steps | proved |
|---|---|---|---|
| 1 | {EFF_MD[0]} | 10u+59 (+53 from phase 1) | Lean kernel (`round_m1_p*`) |
| 2 | {EFF_MD[1]} | 10u0+50u1+485 (+469 from phase 1) | Lean kernel (`round_m2_p*`) |
| 3 | {EFF_MD[2]} | 10u0+50u1+250u2+8455 (+8439 from phase 1) | Lean kernel (`go_spec`, `go_closed`) |
| m | (-4, -18, -90, ..., -18·5^(m-3), +12·5^(m-2)) | about sum 5^i b_i | Lean kernel, every m (`go_spec`, `go_closed`) |

(from phase 1 of the tail the first block gets 2 more). After five phases a `1000` of the spread block on the left is
used up: that is how the deeper block counts down.

Checking consecutive events of the run against this rule (`c/family.c events` + `py/check_rounds.py`): {rc_line}.
`same`/`same*` is one round, `upN` a round after which N more blocks are visible, `down` a block finished; the
exceptions `X` are the left end, the birth of a new last block, the merges after a block runs out, and F-events.

### Visits: the run as a map on block lists

A *visit* starts when the head, in state A after a move left, reads the 0 in front of plain blocks

    A> 0 (10)^b1 1 (10)^b2 1 ... (10)^bk 1 0^inf

and ends when the head first steps left of that cell. It never reads the tape on its left, so its result depends
only on the list l = [b1, ..., bk]: an exit state, a short prefix and a new list. In `lean/Family.lean` (generated
by `{SHARED}/py/gen_family_lean.py` from the template `py/family_generic.lean`; all frame A, then carried to this
machine by the conjugacy) the pieces are:

- seven tape rules proved by bbtools.symtm for all counts: PUSH `(2k+3)::(c+1)::R` spreads the first block
  (6k+15 steps), TURN `[2k+1] -> [2k+2]` (10k+14), TAIL1..TAIL4 move the tail of the spread block one phase
  (first block +3, +1, +1, +1; 9, 15, 15, 15 steps), POP folds a spread block of phase 5 back into the plain block
  2q+2 (4q+9), BIRTH `[2k+4] -> [2k+2, 8]` (10k+188);
- `go n l`, `goT n l`, `clean n l`: the recursion `go (b::c::bs) = (b-5) :: go l4` with `l0 = (c+1)::bs`,
  `l1 = bump3 (go l0)`, `l2..l4 = bump1 (go ...)`, and `go [b] = [b+1]`; `clean` (decidable) asks every spread block
  to be odd and >= 7 and every second block nonempty;
- **`go_spec`** (induction on the depth n, every left context L):
  `steps (goT n l) (L, 0 enc l, A) = some (L, 1 0 enc (go n l), E)` for every clean l;
- **`go_closed`** / `visit_closed`: if b1 is odd >= 7, the later blocks even, the last >= 2 and block i >= 2 +
  18·5^(i-2) for the middle ones, the visit is clean and gives (b1-5, b2-18, b3-90, ..., bk + 12·5^(k-2)) (a single
  odd block: b1+1); the step count is sum 5^(i+1) b_i + K_k with K = 9, 265, 4245, 91645, ... (`py/cf.py`, checked
  against the recursion, trusted);
- `round1..round4` (a visit and then a tail phase: the round rule of the table above), `birth`, `fevent`,
  `fevent_reads_zero`; `halts_iff` and `visit` for this machine's own table.

Every other visit (a small or even first block, a block that runs out and merges, the left end) is not a closed rule
yet but is still a function of the list. `py/hybrid.py` runs the machine as this map: clean visits by the closed
form, every other visit by the exact run-length simulator, recursively (visits inside visits) and memoised. Against
the direct run (`data/trajectory.json`, {hv['trajectory_steps']:,} steps) it reproduces all {hv['left_end_events']}
left-end events and all {hv['f_events']} F-events exactly{" (the hybrid also logs a visit to [0] at step 4)" if hv["left_end_extra_initial"] else ""}.
It then runs to **{hs_md} steps** in {hy['seconds']:.0f} s (`data/hybrid.json`): {hy['left_end_events']} left-end
events, {hy['f_events_count']} F-events, no halt{" (and to 1.0·10^200 steps in two minutes: 505 left-end events, 278 F-events, no halt; `data/hybrid_1e200.txt`)" if is_m0 else ""}.
The list grows to about 40 blocks, block i of size about 5^i; most visits are clean.

### The left end

Each return of the head to the left end of the tape starts a round on the whole list and adds 3 cells on the left.
The block lists at these moments (from `data/trajectory.json`, {N:,} steps):

{top_table_md(tr)}

Between left-end events b2 drops by 18, b3 by 90, b4 by about 450 (the closed form seen from the top: the
first block at the left end is even, so the top-level visit itself is unclean and simulated), while the last block
is born or grows; when a block runs out the list shortens and the neighbours merge. Values such as 296, 524, 1136, 37496 recur across the family: they are
fixed outcomes of a block being born.

### The halting condition

F is entered only by D1 = {d1a} (frame A). F1 halts; F0 = {f0a} (frame A) continues. In {N:,} steps there are
{len(fe)} F-events, at steps {f_steps}; in the {hs_md} steps of the exact map there are {hy['f_events_count']},
all reading 0, with surroundings {h_ctx_md}.

Every one of them is the same mechanism: an unclean visit exits in state C (prefix `0`) onto the 0 of a phase-1 tail
`10`; C0 = 1LD writes 1 and moves onto the tail's 1, D1 enters F one cell further left, and F reads the last cell of a
`1000` (or of the `100` in front of the spread block). `fevent` and `fevent_reads_zero` prove that this cell is 0
for every q and every tape around, so this kind of F-event can never halt. A halt needs another kind: a visit that
exits into F itself, or a C exit onto a different tail. Started from random block lists the machine does halt (about
one F-entry in 150; `[15, 31, 17, 59, 31]` halts after 63,153 steps, `py/random_lists.py`), so whether the blank-tape
run stays clean is a real question.

## What is established

| level | claim | where |
|---|---|---|
{lvl}

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/{m}/lean/check.sh          # Blank.lean + Rules.lean + Family.lean
python3 {SHARED}/py/gen_family_lean.py {m} {ns} > holdouts/{m}/lean/Family.lean
python3 {SHARED}/py/cf.py                                       # closed form vs the recursion
python3 {SHARED}/py/hybrid_run.py {m} 1e100                     # exact block-list map, checked against trajectory.json
cd tools/py && python3 ../../{SHARED}/py/gen_lean.py {m} {gen.ns_of(row)} > ../../holdouts/{m}/lean/Rules.lean
python3 {SHARED}/py/frames.py                                   # the 14 tables are conjugate as claimed
python3 {SHARED}/py/conjugacy_steps.py 1e6                      # and the runs agree step by step
python3 {SHARED}/py/trajectory.py {m} 1e11 holdouts/{m}/data/trajectory.json
cc -O2 -o family {SHARED}/c/family.c
./family events {fa}:{st} 1e8 > ev.txt && python3 {SHARED}/py/check_rounds.py ev.txt
./family enter {m} 1e9 {mp['F']}                                 # the F-events, with the cells around them
```

## Further work

- Done in the second pass: the round rule for every depth (`go_spec`), its closed form (`go_closed`), births and the
  F-event in Lean; the exact block-list map (`hybrid.py`).
- Write the unclean visits as closed rules too (merge `[3, y, ...]` exits C with `[y-1, ...]`; visits with an even
  or small first block; the left end with first block 6 or 8). There are many cases, because an unclean visit
  contains clean and unclean visits at every depth.
- Nonhalting needs an invariant on the reachable block lists showing that every unclean visit ends with a B, A or C
  exit and every C exit lands on a phase-1 tail (the proved harmless F-event), never an F exit onto a 1. The list
  entries are large and grow like 5^i, so a parity/size invariant per depth is the natural candidate; none has been
  found yet.
- The closed step count (`cf.steps`) is checked against `goT` in Python, not proved in Lean.

## Pages

- [`pages/holdouts/{m}/explainer.html`](../../pages/holdouts/{m}/explainer.html)
- [`pages/holdouts/{m}/proof-status.html`](../../pages/holdouts/{m}/proof-status.html)
"""
    return spec, readme


def strip(s):
    s = s.replace("<code>", "`").replace("</code>", "`").replace("<sup>", "^").replace("</sup>", "")
    s = s.replace("<sub>", "").replace("</sub>", "").replace("<b>", "**").replace("</b>", "**")
    s = s.replace("<em>", "*").replace("</em>", "*").replace("&middot;", "·")
    import re
    s = re.sub(r"<[^>]+>", "", s)
    return html.unescape(s).replace("|", "\\|")


def main(argv):
    ms = argv or [r[0] for r in frames.FIRST]
    for m in ms:
        spec, readme = records(m)
        with open(os.path.join(HOLD, m, "status.json"), "w") as f:
            json.dump(spec, f, indent=1, ensure_ascii=False)
            f.write("\n")
        with open(os.path.join(HOLD, m, "README.md"), "w") as f:
            f.write(readme)
        print("wrote", m)


if __name__ == "__main__":
    main(sys.argv[1:])
