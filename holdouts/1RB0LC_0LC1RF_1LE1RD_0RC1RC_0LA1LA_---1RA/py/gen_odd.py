"""Writes lean/OddCases.lean and lean/oddcases.json for 1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA: the odd-a rows of
the A-event map (never used from blank tape), as Lean theorems for all values of their variables.

Covered: every odd a >= 15 (any b), and every odd a < 15 with b >= 30.  The rest (odd a < 15, b < 30) is a finite
set that the table leaves to direct simulation.

Same method as gen_map.py, with new loops: with a odd the left of the head is a plain run of 1s from blank tape,
so a round is `0^inf 1^r (111111)^i A> 0 ...` (r < 6) with the rest of the round's tape given literally:
`ob0`, `ob2` (b odd: a block of 4x+4 or 4x+6 1s loses four) and `oe1`, `oe2` (both even: both blocks lose two).

usage: python3 gen_odd.py      (about 5 min)
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_map as G  # noqa: E402

C = G.C
N0 = len(G.lib.thms)   # the loops of gen_map.py, already in Cases.lean
G.LOOPS[:] = []
LOOPMARK = {}


def mk(name, t, doc):
    mark = len(G.lib.thms)
    G.LOOPS.append(C.Loop(G.lib, name, t, doc=doc))
    LOOPMARK[name] = (mark, len(G.lib.thms))


for r in range(6):
    L = "0^inf " + " ".join(["1"] * r)
    mk(f"ob0_{r}", f"{L} (111111)^i A> 0 (1111)^x+1 0 (11)^y 1 0^inf",
       "A round of the b-odd phase with odd a: the block of 4x+4 1s loses four, six 1s join the left.")
    mk(f"ob2_{r}", f"{L} (111111)^i A> 0 (1111)^x+1 1 1 0 (11)^y 1 0^inf",
       "A round of the b-odd phase with odd a (a block of 4x+6 1s).")
    mk(f"oe1_{r}", f"{L} (111111)^i A> 0 (11)^x+1 0 (11)^x+y+1 0^inf",
       "A round of the Euclid phase with odd a (first block the shorter): both lose two 1s, six join the left.")
    mk(f"oe2_{r}", f"{L} (111111)^i A> 0 (11)^x+y+1 0 (11)^x+1 0^inf",
       "A round of the Euclid phase with odd a (second block the shorter).")
G.LCTX[:] = ["0^inf"]

CASES = []

# The symbolic prover chains its segments with `steps_seq`, so each meeting point is a definitional equality.  With
# repeats like `rep (x + 5) [1,1,1,1,1,1]` on the tape and the two sides written differently (`app [] (rep 1 w X)`
# against `rep 1 w X`), Lean's defeq check unfolds both sides with backtracking and takes minutes (the kernel times
# out).  So every meeting point is bridged instead by an equation that `simp` proves by rewriting both sides to
# the same normal form (cons cells, `rep x`, blank).
JOIN = "(by simp only [app_nil, app_cons, rep_succ, rep_zero])"


def bridged(text):
    out = []
    for line in text.split("\n"):
        if line.startswith("  exact steps_congr"):
            line = re.sub(r"steps_seq trans (h\d+) \(", lambda m: f"bridge trans {m.group(1)} {JOIN} (", line)
            line = re.sub(r"steps_seq trans (h\d+) (h\d+)", lambda m: f"bridge trans {m.group(1)} {JOIN} {m.group(2)}", line)
        out.append(line)
    return "\n".join(out)


def att(name, F, a, b, ga, gb, vs):
    md = G.attempt(name, F, a, b, ga, gb, vs)
    if md:
        CASES.append(md)
    return md


def generic(prefix, F, mk_, Kmax=4):
    for K in range(Kmax):
        if att(f"{prefix}_g{K}", F, *mk_(K)):
            return K
    raise SystemExit(f"no generic case for {prefix}")


def must(*a):
    assert att(*a), a[0]


if __name__ == "__main__":
    for F in "UV":
        # a >= 15 odd, b odd: a = 1 mod 4, a = 3 mod 4
        K = generic(f"O1{F}", F, lambda K: (f"4*x+{4 * K + 17}", "2*y+1", f"(1111)^x+{K + 4} 1", "(11)^y 1", ["x", "y"]))
        for a in range(17, 4 * K + 17, 4):
            must(f"O1{F}_a{a}", F, str(a), "2*y+1", G.ones(a), "(11)^y 1", ["y"])
        K = generic(f"O3{F}", F, lambda K: (f"4*x+{4 * K + 15}", "2*y+1", f"(1111)^x+{K + 3} 1 1 1", "(11)^y 1", ["x", "y"]))
        for a in range(15, 4 * K + 15, 4):
            must(f"O3{F}_a{a}", F, str(a), "2*y+1", G.ones(a), "(11)^y 1", ["y"])
        # a >= 15 odd, b even: b >= a - 7, b <= a - 13 (b >= 2), b = 0, b = a - 11, b = a - 9
        for tag, mk_ in (
                ("OE", lambda K: (f"2*x+{2 * K + 15}", f"2*x+2*y+{2 * K + 8}", f"(11)^x+{K + 7} 1", f"(11)^x+y+{K + 4}", ["x", "y"])),
                ("OD", lambda K: (f"2*x+2*y+{2 * K + 15}", f"2*y+{2 * K + 2}", f"(11)^x+y+{K + 7} 1", f"(11)^y+{K + 1}", ["x", "y"])),
                ("O0", lambda K: (f"2*x+{2 * K + 15}", "0", f"(11)^x+{K + 7} 1", "", ["x"])),
                ("O11", lambda K: (f"2*x+{2 * K + 15}", f"2*x+{2 * K + 4}", f"(11)^x+{K + 7} 1", f"(11)^x+{K + 2}", ["x"])),
                ("O9", lambda K: (f"2*x+{2 * K + 15}", f"2*x+{2 * K + 6}", f"(11)^x+{K + 7} 1", f"(11)^x+{K + 3}", ["x"]))):
            K = generic(f"{tag}{F}", F, mk_)
            assert K == 0, (tag, K)
        # odd a < 15, b >= 30
        for a in range(1, 15, 2):
            must(f"S{F}_a{a}_e", F, str(a), "2*y+30", G.ones(a), "(11)^y+15", ["y"])
            must(f"S{F}_a{a}_o", F, str(a), "2*y+31", G.ones(a), "(11)^y+15 1", ["y"])
    # keep only the loops the cases use
    body = "\n".join(G.lib.thms[LOOPMARK[max(LOOPMARK, key=lambda n: LOOPMARK[n][1])][1]:])
    keep = []
    for j, t in enumerate(G.lib.thms):
        owner = [n for n, (s, e) in LOOPMARK.items() if s <= j < e]
        if owner and not re.search(r"\b" + re.escape(owner[0]) + r"\b", body):
            continue
        if j >= N0:
            keep.append(t)
    G.lib.thms[:] = [bridged(t) for t in keep]
    out = C.lean_file(G.lib, ["Cases"],
                      "The odd-a cases of the A-event map, generated by `py/gen_odd.py` with "
                      "`../1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/py/chain.py`; do not edit by hand.")
    open(os.path.join(HERE, "..", "lean", "OddCases.lean"), "w").write(out)
    json.dump(CASES, open(os.path.join(HERE, "..", "lean", "oddcases.json"), "w"), indent=1)
    print(len(CASES), "cases", len(keep), "theorems")
