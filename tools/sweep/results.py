"""Collect the sweep's checkpoints into a results table (markdown).

usage: python3 tools/sweep/results.py CKPT_DIR [RESIDUE_DIR] > RESULTS.md

Engine checkpoints: CKPT_DIR/<slug>.json. Residue-walk checkpoints: RESIDUE_DIR/<slug>.json. C checkpoints
(CKPT_DIR/c_*.ck) are the first line of tools/c/redmaps.c, tools/c/doubling_phases.c and the psq program of
1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
import engine  # noqa: E402

C_RUNS = {  # slug -> (checkpoint, unit, program)
    "m_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_ZZZ0RE": ("c_ph1.ck", "phases", "tools/c/doubling_phases.c 1"),
    "m_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_ZZZ0RE": ("c_ph2.ck", "phases", "tools/c/doubling_phases.c 2"),
    "m_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_ZZZ0RE": ("c_ph3.ck", "phases", "tools/c/doubling_phases.c 3"),
    "m_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_ZZZ0RE": ("c_ph4.ck", "phases", "tools/c/doubling_phases.c 4"),
    "m_1RB1RF_1LC1LF_0RE1LD_0LB1LD_ZZZ1RC_1RA0RD": ("c_psq.ck", "phases", "holdouts/…/c/psq.c"),
    "m_1RB1RC_1LC1LC_1RE0LD_1LB1RF_ZZZ1RA_0RD1RD": ("c_map_rc.ck", "rounds", "tools/c/redmaps.c rc"),
    "m_1RB1RB_1LC0RE_ZZZ1LD_0RA1LB_1RA1LF_0LE1LE": ("c_map_rb.ck", "rounds", "tools/c/redmaps.c rb"),
    "m_1RB1RE_1LC0RA_0RD1LB_ZZZ1RC_1LF1RE_0LB0LE": ("c_map_re0.ck", "map steps", "tools/c/redmaps.c re0"),
    "m_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_ZZZ0LE": ("c_map_re1.ck", "map steps", "tools/c/redmaps.c re1"),
}
NOT_RUN = {
    "m_1RB1RE_1LC1LD_ZZZ1LA_1LB1LE_0RF0RA_1LD1RF": "epoch 4 is about 10^14·(3/2)^… phases away; Lean already covers epochs to 459271258863231",
    "m_1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_ZZZ1LB": "round 4 has fuel 2.2·10^22; nothing can be decided before it runs out",
    "m_1RB0LF_1RC1RA_0RD0RB_1LEZZZ_0LA1LE_1RD1LA": "busycoq PR 60's halt is about 10^25 returns away; the module reproduces PR 60's 86-node endgame",
    "m_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_ZZZ1LC": "c/odo.c already at 10^11 operations; not extended here",
    "m_1RB1LF_1RC1RF_0LD1RE_ZZZ1LC_0RB1RE_1LA0LE": "c/fast.c already at 10^11 operations; not extended here",
}


def sci(n):
    n = int(n)
    if n < 10 ** 7:
        return f"{n:,}"
    s = str(n)
    return f"{s[0]}.{s[1:3]}·10^{len(s) - 1}"


def head_json(path, keys):
    with open(path) as f:
        h = f.read(400)
    out = {}
    for k in keys:
        m = re.search(r'"%s": ("?[^,"]*"?)' % k, h)
        if m:
            out[k] = m.group(1).strip('"')
    return out


def main(ck, rd=None):
    rows = []
    for slug in engine.slugs():
        m = engine.load(slug)
        name = m.MACHINE
        bound = getattr(m, "BOUND", "")
        now, how, note = "", "", ""
        if slug in C_RUNS:
            f, unit, prog = C_RUNS[slug]
            p = os.path.join(ck, f)
            if os.path.exists(p):
                with open(p) as fh:
                    now = sci(int(fh.readline().split()[0])) + " " + unit
                how = prog
        if rd and os.path.exists(os.path.join(rd, slug + ".json")):
            h = head_json(os.path.join(rd, slug + ".json"), ["n", "result"])
            now = sci(h["n"]) + " steps"
            how = "residue.py"
            if h.get("result") not in (None, "running"):
                note = h["result"]
        p = os.path.join(ck, slug + ".json")
        if not now and os.path.exists(p):
            with open(p) as fh:
                st = json.load(fh)
            n = int(st["n"])
            acc = hasattr(m, "accel")
            now = sci(n) + (" Lean steps" if acc and n > 10 ** 12 else " steps")
            how = "engine.py"
            if st.get("closest") is not None:
                note = f"closest {st['closest']} bits"
            if st["result"] not in ("running",):
                note = st["result"]
            now += f", {sci(st['max_bits'])} bits"
        if not now and slug in NOT_RUN:
            now, how = "not extended", NOT_RUN[slug]
        rows.append((name, m.KIND, bound, now, how, note))
    print("| machine | kind | before this sweep | now (no halt) | run by | note |")
    print("|---|---|---|---|---|---|")
    for r in rows:
        print("| " + " | ".join(str(x).replace("|", "/") for x in r) + " |")


if __name__ == "__main__":
    main(*sys.argv[1:])
