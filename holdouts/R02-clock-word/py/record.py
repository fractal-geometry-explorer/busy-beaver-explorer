"""Add the 21 November 2026 clock results to the READMEs and status.json of the six table-sharing R02 machines.

usage (from holdouts/): python3 R02-clock-word/py/record.py"""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
import clockx  # noqa: E402
from clockx import clock  # noqa: E402

# machine: (block start, growth, visits checked to 2e9, run reached, phases, Lean new?)
RES = {
    "1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---": (113, "2.72·10^177", 31, True),
    "1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---": (90, "3.91·10^162", 28, True),
    "1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---": (124, "1.43·10^199", 27, True),
    "1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---": (132, "3.64·10^202", 30, True),
    "1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD": (56, "6.30·10^79", None, False),
    "1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---": (84, "1.27·10^139", None, True),
}


def sup(x):
    a, b = x.split("^")
    return f"{a}<sup>{b}</sup>"


for m, (nv, reach, ph, newlean) in RES.items():
    base = clockx.DERIVED[m]
    pi, mir = clockx.find_map(base, m)
    ren = ", ".join(f"{clockx.S[i]}→{clockx.S[pi[i]]}" for i in range(6))
    X, Y, B0 = clock.PARAMS[m][:3]
    g = clock.PARAMS[m][3] if len(clock.PARAMS[m]) > 3 else 2
    phs = f" ({ph} phases)" if ph else ""
    md = (f"\n## The clock (21 November 2026)\n\n"
          f"This table is the table of `{base}` with the states renamed ({ren}{', left and right exchanged' if mir else ''}), "
          f"so this machine runs the same clock from another start: a block at the {'right' if m in clock.MIRROR else 'left'} end grows by {g} per tick, and "
          f"tick k makes 2^k trips (one word map P each) into the word beside it. Family R02, see "
          f"[`../R02-clock-word/README.md`](../R02-clock-word/README.md).\n\n"
          + (f"- Lean, kernel: the clock for every k and every word, for each tick whose 2^k trips all return, with "
             f"its exact step count (`tick`, `tick_right_end` in `lean/MirrorBridge.lean`; proved on the mirror image "
             f"in `lean/MirrorMachine.lean`, `MirrorRules.lean`, `MirrorClock.lean`, written by "
             f"`holdouts/R02-clock-word/py/gen_clockx.py`).\n" if newlean else "")
          + f"- Trusted computation: the exact accelerated simulator (`clock.py` with `R02-clock-word/py/clockx.py`) "
          f"agrees with `tools/c/tmrun.c` at all {nv} visits of the clock end in the first 2·10^9 steps, and follows "
          f"the run past {reach} steps{phs} without a halt (`R02-clock-word/out/run_{m}.txt`).\n"
          f"- A halt can only come at a phase end, when a trip does not return.\n")
    p = os.path.join(m, "README.md")
    s = open(p).read()
    if "## The clock (21 November 2026)" not in s:
        anchor = "\n<!-- related machines"
        i = s.find(anchor)
        s = s[:i] + md + s[i:] if i >= 0 else s + md
        open(p, "w").write(s)
    p = os.path.join(m, "status.json")
    d = json.load(open(p))
    claims = [c for c in d["claims"] if not c["title"].startswith("Clock")]
    new = []
    if newlean:
        new.append({"level": "kernel", "title": "Clock: 2^k trips per tick, for every k",
                    "text": f"The table is the table of {base} renamed ({ren}{', mirrored' if mir else ''}). At the "
                            f"{'right' if m in clock.MIRROR else 'left'} end a block grows by {g} per tick, and tick k "
                            f"applies one word map P (one trip of the head into the word) 2<sup>k</sup> times, for every k and "
                            f"every word, whenever the 2<sup>k</sup> trips all return; with the exact step count.",
                    "where": "<code>tick</code>, <code>tick_right_end</code>, <code>lean/MirrorBridge.lean</code> "
                             "(<code>MirrorClock.lean</code>, written by <code>holdouts/R02-clock-word/py/gen_clockx.py</code>)"})
    new.append({"level": "trusted", "title": f"Clock run: no halt to {sup(reach)} steps",
                "text": f"The exact accelerated clock simulator agrees with tools/c/tmrun.c at all {nv} visits of the clock "
                        f"end in the first 2&middot;10<sup>9</sup> steps and follows the run past {sup(reach)} steps{phs} "
                        f"without a halt. A halt can only come at a phase end, when a trip does not return.",
                "where": "<code>holdouts/R02-clock-word/py/runx.py</code>, <code>out/run_" + m + ".txt</code>"})
    k = next((i for i, c in enumerate(claims) if c["title"].startswith("Does it halt")), len(claims))
    d["claims"] = claims[:k] + new + claims[k:]
    d["summary"] = (f"Same table as {base} (renamed{', mirrored' if mir else ''}): a clock at the "
                    f"{'right' if m in clock.MIRROR else 'left'} end, block +{g} per tick, 2^k trips of one word map P "
                    f"per tick{' (Lean, every k)' if newlean else ''}; exact accelerated run past {sup(reach)} steps, no halt. "
                    f"A halt can only come at a phase end.")
    d["verdict"] = ["<b>The question is open.</b> " + d["summary"]]
    d["asof"] = "Status as of 21 November 2026."
    with open(p, "w") as f:
        json.dump(d, f, ensure_ascii=False, indent=1)
        f.write("\n")
    print("ok", m)
