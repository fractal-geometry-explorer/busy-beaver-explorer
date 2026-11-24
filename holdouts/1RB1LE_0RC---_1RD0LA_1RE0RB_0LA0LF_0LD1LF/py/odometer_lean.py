"""Generate lean/Odometer.lean: the digit rules of the wall odometer of 1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF,
for every block length and any tape L to the left, proved by tools/py/bbtools/symtm.py (crossing lemmas + rfl).

A block is a^n with a = 100.  A wall is one of the four glyphs 1010, 0, 1110, 1 (digits 0..3).  At an R-instant the
tape ends in `1 D> 1 0` followed by blank tape.  One trip moves the head left to the first wall that is not 1 (digit 3),
changes it, and comes back.  The theorems below are those trips for the last wall and for one carry, plus the same
for the double wall 10101010 (two walls with an empty block between them) and the left end.

usage: python3 odometer_lean.py > ../lean/Odometer.lean
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, rules_file  # noqa: E402

M = "1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF"
NS = "H" + open(os.path.join(HERE, "..", "lean", "Machine.lean")).read().split("namespace H")[1].split()[0]
END = "1 D> 1 0 0^inf"
NAMES = {"1010": "d0", "0": "d1", "1110": "d2", "1": "d3", "10101010": "e0", "10101000": "e1", "11101010": "e2",
         "11101000": "e3"}
# carry rule of each wall glyph: next glyph, change of the block to its left, change of the block to its right,
# whether the carry goes on to the left, constant part of the step count (found by py/odometer/macro.py: learn)
RULE = {"1010": ("0", 1, 1, 0, 19), "0": ("1110", -2, 2, 0, 31), "1110": ("1", 0, 2, 0, 19), "1": ("1010", -2, 1, 1, 4),
        "10101010": ("10101000", 0, 1, 0, 19), "10101000": ("11101010", -1, 2, 0, 41),
        "11101010": ("11101000", 0, 1, 0, 19), "11101000": ("10101010", -2, 2, 1, 22)}


def blk(v, k):
    return f"(100)^{v}" if k == 0 else (f"(100)^{v}+{k}" if k > 0 else None)


def check(res, want):
    th, fin = res
    if want is not None and str(fin.steps) != want:
        raise SystemExit(f"step count {fin.steps}, expected {want}")
    sys.stderr.write(f"{th.split(chr(10))[1].split()[1]}: {fin.steps} steps\n")
    return th


def last_rule(g):
    """g is the last wall: L a^(x+s) g a^y 1 D> 1 0  ->  L a^(x+s+dl) g' a^(y+dr) 1 D> 1 0"""
    g2, dl, dr, ps, kap = RULE[g]
    s = max(0, -dl)
    start = f"L {blk('x', s)} {g} (100)^y {END}"
    if ps:
        return None
    end = f"L {blk('x', s + dl)} {g2} {blk('y', dr)} {END}"
    doc = (f"Last wall `{g}` -> `{g2}`: the block on its left changes by {dl}, the last block by {dr}; "
           f"8 steps per word of the last block plus {kap}.")
    return check(prove(M, f"last_{NAMES[g]}", start, end, doc=doc, rotate=True, max_seg=40), f"8*y+{kap}")


def carry_rule(g, inner):
    """inner wall (digit 3 kind) passes the carry to g on its left."""
    g2, dl, dr, ps, kap = RULE[g]
    i2, il, ir, ips, ikap = RULE[inner]
    s = max(0, -dl)
    t = max(1, -(dr + il))
    start = f"L {blk('x', s)} {g} {blk('y', t)} {inner} (100)^z {END}"
    end = f"L {blk('x', s + dl)} {g2} {blk('y', t + dr + il)} {i2} {blk('z', ir)} {END}"
    doc = (f"Carry: the last wall `{inner}` becomes `{i2}` and the wall `{g}` on its left becomes `{g2}`.")
    return check(prove(M, f"carry_{NAMES[inner]}_{NAMES[g]}", start, end, doc=doc, rotate=True, max_seg=40), None)


def main():
    ths = []
    for g in RULE:
        th = last_rule(g)
        if th:
            ths.append(th)
    for inner in ("1", "11101000"):
        for g in ("1010", "0", "1110", "10101010", "10101000", "11101010"):
            ths.append(carry_rule(g, inner))
    # walls of any width: (1010)^(r+2), r+2 walls with empty blocks between them, is one digit with the same totals
    ths.append(check(prove(M, "multi_0", f"L (100)^x (1010)^r+2 (100)^y {END}", f"L (100)^x (1010)^r+1 1 0 0 0 (100)^y+1 {END}",
                           doc="A wall of r+2 walls `(1010)^(r+2)`, digit 0 -> 1: the last block grows by 1.",
                           rotate=True, max_seg=40, count_first=True), "8*y+19"))
    ths.append(check(prove(M, "multi_1", f"L (100)^x+1 (1010)^r+1 1 0 0 0 (100)^y {END}",
                           f"L (100)^x 1 1 1 0 (1010)^r+1 (100)^y+2 {END}",
                           doc="Digit 1 -> 2 of a wall of r+2 walls: the block on its left loses 1, the last block gains 2.",
                           rotate=True, max_seg=40, count_first=True), "10*r+8*y+41"))
    ths.append(check(prove(M, "multi_2", f"L (100)^x 1 1 1 0 (1010)^r+1 (100)^y {END}",
                           f"L (100)^x 1 1 1 0 (1010)^r 1 0 0 0 (100)^y+1 {END}",
                           doc="Digit 2 -> 3 of a wall of r+2 walls: the last block grows by 1.",
                           rotate=True, max_seg=40, count_first=True), "8*y+19"))
    ths.append(check(prove(M, "multi_3_carry", f"L (100)^x 1010 (100)^w+2 1 1 1 0 (1010)^r+1 1 0 0 0 (100)^y {END}",
                           f"L (100)^x+1 0 (100)^w+1 (1010)^r+3 (100)^y+2 {END}",
                           doc="Digit 3 -> 0 of a wall of r+3 walls, with the carry to a wall `1010` on its left.",
                           rotate=True, max_seg=40, count_first=True), "10*r+8*w+8*y+67"))
    # the left end: 10 a^x ... (digit 0 of the binary left digit) absorbs a carry and becomes 00
    ths.append(check(prove(M, "left_10", f"0^inf 1 0 (100)^x+1 1 (100)^z {END}", f"0^inf 0 0 (100)^x 1010 (100)^z+1 {END}",
                     doc="The left end `10` absorbs a carry from a last wall `1` and becomes `00`.", rotate=True, max_seg=40), None))
    # after a left visit (the left end 00 overflows; its zigzag sweep of 19 steps per word is not a shift rule that
    # symtm finds, so the visit itself is not here) the head arrives at the right end in E or C, depending on the
    # parity of the number of walls; after an arrival in C the right end grows a new wall:
    ths.append(check(prove(M, "spawn", "L (100)^y 1010 (100)^z+3 C> 1 0 0^inf",
                           f"L (100)^y+1 0 (100)^z 1010 (100)^5 {END}",
                           doc="After an arrival in C the right end grows a new wall `1010` with a block of 5 words.",
                           rotate=True, max_seg=40), None))
    sys.stdout.write(rules_file("Rules", NS, ths,
                                f"Odometer digit rules of {M}, generated by `py/odometer_lean.py`; do not edit by hand."))


if __name__ == "__main__":
    main()
