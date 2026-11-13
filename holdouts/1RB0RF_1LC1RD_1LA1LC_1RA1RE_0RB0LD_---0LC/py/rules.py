"""Rewrite ../lean/Rules.lean: the shift rules of this machine (and any cycle rules below), proved by bbtools.symtm.

usage: python3 holdouts/MACHINE/py/rules.py        (from the repository root; then lean/check.sh)
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402
from bbtools.machine import Machine  # noqa: E402

M = "1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC"
# (direction, state, word): the head in that state crosses copies of the word; found in the run by counting.
SHIFTS = ['l:C:1']
# (name, start, end, doc): longer rules proved by symbolic simulation.
CYCLES = []

symtm.MAX_CARRY = 8


def shift_rule(m, d, q, w):
    qi = "ABCDEF".index(q)
    w = tuple(int(c) for c in w)
    for lu in range(0 if d == "r" else 1, 7):
        for x in range(2 ** lu):
            u = tuple((x >> i) & 1 for i in range(lu))
            r = (symtm._one_copy_right if d == "r" else symtm._one_copy_left)(m, qi, u, w)
            if r:
                v, s = r
                us, ws, vs = " ".join(map(str, u)), "".join(map(str, w)), "".join(map(str, v))
                if d == "r":
                    start, end = f"L {us} {q}> ({ws})^n R", f"L ({vs})^n {us} {q}> R"
                else:
                    start, end = f"L ({ws})^n {q}> {us} R", f"L {q}> {us} ({vs})^n R"
                doc = (f"Shift rule: in state {q} the head crosses n copies of {ws} "
                       + ("rightward" if d == "r" else "leftward") + f", {s} steps per copy, leaving {vs} behind"
                       + (f" (the word {''.join(map(str, u))} next to the head travels along)" if u else "") + ".")
                return symtm.prove(m, f"shift_{d}_{q}_{ws}", start, end, doc=doc)[0]
    raise SystemExit(f"no shift rule for {d} {q} {w}")


def main():
    m = Machine.parse(M)
    th = [shift_rule(m, *s.split(":")) for s in SHIFTS]
    for name, start, end, doc in CYCLES:
        th.append(symtm.prove(m, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=40)[0])
    lean = os.path.join(HERE, "..", "lean")
    ns = re.search(r"namespace (\w+)", open(os.path.join(lean, "Machine.lean")).read()).group(1)
    doc = (f"# {M}: proved rules\n\nShift rules (the head crossing a run of copies of a word in one go) found in the run "
           "and proved for every count and every tape around them by `tools/py/bbtools/symtm.py` "
           "(the folder's `py/rules.py` rewrites this file).")
    with open(os.path.join(lean, "Rules.lean"), "w") as f:
        f.write(symtm.rules_file("Machine", ns, th, doc))


if __name__ == "__main__":
    main()
