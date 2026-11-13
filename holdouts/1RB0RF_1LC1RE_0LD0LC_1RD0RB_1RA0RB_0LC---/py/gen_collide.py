"""Write lean/Collide.lean for 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---: the rules of the irregular steps that
Rules.lean and Transients.lean leave out, each proved by `bbtools.symtm.prove`.

* The word phase (three shapes of the word's end).  From `W 0 1 1 1 B> 0 R` the head rewrites the end of the word
  as phi(phi(W)) and comes back to `phi(phi(W)) 0 1 1 A> 0 1 R` without reading R.  The regular one-unit Q-step and
  every collision start this way.
* The A phase of a regular one-unit step: from `L 0 1 1 A> 0 1 X` with X = t gaps of 2 and then at least three
  0s (or blank tape) to the next Q event (2 rules).
* The A phase of a collision.  From `L 0 1 1 A> 0 1 X` where X, the counter's gaps, is t gaps of length 2, then a
  gap g of 0 or 1 (the misaligned gap at the end of its run), then U gaps of length 2, then a gap of h+5 >= 5
  (or blank tape): the head turns the counter's low part into new blocks at the end of the word and stops at the
  next Q event.  Cases: t = 2s or 2s+1, g = 0 or 1, U = 0, 1 or more (U = 2 and U >= 3 separately when t is even
  and g = 0, where an F event splits them), gap or blank tape: 26 rules.  They never read L.
* The anomaly with a one-unit counter (the word a block 2c+2 and a single 1): t gaps of 2 after the unit, then a
  gap of h+3 >= 3 or blank tape, with t = 0 and t >= 1 separately: 4 rules.  (0LC machine only: this anomaly passes
  an F event and differs in the other five machines.)

The case table was found by direct simulation (every collision and anomaly of 300 transients of the accelerated
run from blank tape is one of these cases); Lean checks each rule for all values of the parameters.

usage (from the repository root):
  python3 holdouts/1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---/py/gen_collide.py MACHINE > holdouts/MACHINE/lean/Collide.lean
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file  # noqa: E402

WORD = [
    ("wp_big", "L 0 1 (11)^j+2 0 1 1 1 B> 0 R", "L 1 1 0 (10)^j 1 1 1 0 1 1 A> 0 1 R",
     "word phase, last block 2j+5"),
    ("wp_three", "L 0 1 1 1 0 1 1 1 B> 0 R", "L 1 1 1 1 0 1 1 A> 0 1 R", "word phase, last block 3"),
    ("wp_one", "L 0 1 (11)^i 0 1 0 1 1 1 B> 0 R", "L 1 1 0 1 (01)^i 0 1 1 A> 0 1 R",
     "word phase, last block 1 after a block 2i+1"),
]
APH = [
    ("aph_unit", "L 0 1 1 A> 0 1 (001)^t 0 0 0 R", "L 0 (111)^t+2 B> 0 R",
     "the A phase of a regular one-unit step: t gaps of 2, then at least three 0s"),
    ("aph_unit_blank", "L 0 1 1 A> 0 1 (001)^t 0^inf", "L 0 (111)^t+2 B> 0^inf",
     "the A phase of a regular one-unit step: t gaps of 2, then blank tape"),
]
ANOM = [
    ("anom_unit0_gap", "0^inf (11)^c+1 0 1 0 1 1 1 B> 0 0^h+3 1 R",
     "0^inf 1 1 0 (10)^c 1 1 1 1 1 0 1 1 1 B> 0 0^h 1 R"),
    ("anom_unit0_blank", "0^inf (11)^c+1 0 1 0 1 1 1 B> 0^inf", "0^inf 1 1 0 (10)^c 1 1 1 1 1 0 1 1 1 B> 0^inf"),
    ("anom_units_gap", "0^inf (11)^c+1 0 1 0 1 1 1 B> 0 (001)^t+1 0^h+3 1 R",
     "0^inf 1 1 0 (10)^c 1 1 1 1 1 0 (111)^t+2 B> 0 0^h 1 R"),
    ("anom_units_blank", "0^inf (11)^c+1 0 1 0 1 1 1 B> 0 (001)^t+1 0^inf",
     "0^inf 1 1 0 (10)^c 1 1 1 1 1 0 (111)^t+2 B> 0^inf"),
]
# (t parity, g, U) -> (last appended blocks after (1)*3s, new low part, new first gap minus h)
TABLES = {
    "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---": {
        (0, 0, '0'): ([3], '1', 0), (0, 1, '0'): ([3], '1', 1), (0, 0, '1'): ([5], '1', 1),
        (0, 1, '1'): ([5], '1', 2), (0, 0, '2'): ([7], '1', 2), (0, 0, 'u+3'): ([7], 'u+2', 2),
        (0, 1, 'u+2'): ([5], 'u+2', 2),
        (1, 0, '0'): ([1, 1, 1], '1', 1), (1, 1, '0'): ([1, 1, 1], '1', 2), (1, 0, '1'): ([1, 1, 3], '1', 2),
        (1, 1, '1'): ([1, 1, 1], '2', 2), (1, 0, 'u+2'): ([1, 1, 3], 'u+2', 2),
        (1, 1, 'u+2'): ([1, 1, 1], 'u+3', 2),
    },
}
# The other five machines: only the rows of the same form (next gap h+5 or blank tape, one new gap) that hold for
# all values of the parameters.  Their other collisions (shorter next gap, several new gaps, the word rewritten
# further left) are not covered.
_COMMON = {(0, 0, '0'): ([3], '1', 0), (0, 0, '1'): ([5], '1', 1), (1, 0, '0'): ([1, 1, 1], '1', 1)}
TABLES["1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RB---"] = dict(_COMMON)
TABLES["1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---"] = dict(_COMMON)
TABLES["1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---"] = dict(_COMMON)
TABLES["1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RE---"] = {
    (0, 0, '0'): ([3], '1', 0), (0, 0, '1'): ([5], '1', 1), (0, 0, 'u+2'): ([5], 'u+2', 1),
    (1, 0, '0'): ([1, 1, 1], '1', 1), (1, 0, '1'): ([1, 1, 1], '2', 1), (1, 0, 'u+2'): ([1, 1, 1], 'u+3', 1),
}
TABLES["1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---"] = {
    (0, 0, '0'): ([3], '1', 0), (0, 0, '1'): ([5], '1', 1), (0, 0, '2'): ([7, 1], '1', 0),
    (0, 0, '3'): ([7, 3], '1', 1), (0, 1, 'u+1'): ([1, 1, 1], 'u+1', 2),
    (1, 0, '0'): ([1, 1, 1], '1', 1), (1, 0, '1'): ([1, 1, 3, 1], '1', 0), (1, 0, '2'): ([1, 1, 3, 3], '1', 1),
    (1, 1, '0'): ([1, 1, 1, 1], '1', 0), (1, 1, '1'): ([1, 1, 1, 3], '1', 1),
}


# The anomaly with a one-unit counter in the other five machines (it passes an F event, so it depends on A1 and
# F0): the cases found uniform in simulation, as tape-level rules only.
_S = "0^inf (11)^c+1 0 1 0 1 1 1 B> "
_E = "0^inf 1 1 0 (10)^c "
_ORB = [
    ("anomx_unit0_blank", _S + "0^inf", _E + "1 1 1 1 1 0 1 1 1 0 1 1 1 B> 0^inf"),
    ("anomx_unit0_gap", _S + "0 0^h+7 1 R", _E + "1 1 1 1 1 0 1 1 1 0 1 1 1 B> 0 0^h 1 R"),
    ("anomx_units_blank", _S + "0 (001)^t+1 0^inf", _E + "1 1 1 1 1 0 1 0 1 1 1 B> 0 (000)^t 1 0^inf"),
    ("anomx_units_gap", _S + "0 (001)^t+1 0^h+3 1 R", _E + "1 1 1 1 1 0 1 0 1 1 1 B> 0 (000)^t 1 0^h 1 R"),
]
ANOMX = {
    "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RB---": _ORB,
    "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---": _ORB,
    "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---": [
        ("anomx_unit0_blank", "0^inf (11)^c+2 0 1 0 1 1 1 B> 0^inf", _E + "1 1 1 1 1 0 1 1 1 B> 0 0 1 0^inf"),
        ("anomx_unit0_gap", "0^inf (11)^c+2 0 1 0 1 1 1 B> 0 0^h+3 1 R",
         _E + "1 1 1 1 1 0 1 1 1 B> 0 0 1 0^h 1 R"),
        ("anomx_units_blank", "0^inf (11)^c+2 0 1 0 1 1 1 B> 0 (001)^t+1 0^inf",
         _E + "1 1 1 1 1 0 1 1 1 B> 0 0 (000)^t+1 1 0^inf"),
        ("anomx_units_gap", "0^inf (11)^c+2 0 1 0 1 1 1 B> 0 (001)^t+1 0^h+3 1 R",
         _E + "1 1 1 1 1 0 1 1 1 B> 0 0 (000)^t+1 1 0^h 1 R"),
    ],
    "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---": [
        ("anomx_unit0_blank", _S + "0^inf", _E + "1 1 1 1 1 0 1 0 1 1 1 B> 0^inf"),
        ("anomx_unit0_gap", _S + "0 0^h+5 1 R", _E + "1 1 1 1 1 0 1 0 1 1 1 B> 0 0^h 1 R"),
        ("anomx_unit1_blank", _S + "0 0 0 1 0^inf", _E + "1 1 1 1 1 0 1 1 1 0 1 1 1 B> 0^inf"),
        ("anomx_unit1_gap", _S + "0 0 0 1 0^h+4 1 R", _E + "1 1 1 1 1 0 1 1 1 0 1 1 1 B> 0 0^h 1 R"),
    ],
    "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RE---": [
        ("anomx_units_blank", _S + "0 (001)^t 0^inf", _E + "1 1 1 0 (111)^t+2 B> 0^inf"),
        ("anomx_units_gap", _S + "0 (001)^t 0^h+4 1 R", _E + "1 1 1 0 (111)^t+2 B> 0 0^h 1 R"),
    ],
}


def coll_cases(table):
    for (tp, g, U), (C, ap, d) in table.items():
        for tail in ("gap", "blank"):
            T = "(001001)^s" if tp == 0 else "(001001)^s 0 0 1"
            gs = "1" if g == 0 else "0 1"
            Us = " ".join(["0 0 1"] * int(U)) if U.isdigit() else "(001)^" + U
            tl = "0^h+5 1 R" if tail == "gap" else "0^inf"
            start = f"L 0 1 1 A> 0 1 {T} {gs} {Us} {tl}"
            endr = ("0 0^h 1 R" if d == 0 else "0 0^h+%d 1 R" % d) if tail == "gap" else "0^inf"
            blocks = " ".join("1" * c + " 0" for c in C)
            end = f"L 1 1 0 (101010)^s {blocks} (111)^{ap} B> {endr}"
            name = f"coll_{'e' if tp == 0 else 'o'}{g}_{U.replace('+', '')}_{tail}"
            doc = (f"collision: t = {'2s' if tp == 0 else '2s+1'} gaps of 2, misaligned gap {g}, then {U} gaps of 2 "
                   f"and {'a gap of h+5' if tail == 'gap' else 'blank tape'}: appended blocks (1)*3s {C}, low part "
                   f"{ap}" + (f", next gap h+{d}" if tail == "gap" else ""))
            yield name, start, end, doc


def main():
    m = sys.argv[1]
    mach = open(os.path.join(HERE, "../../", m, "lean/Machine.lean")).read()
    ns = re.search(r"^namespace (\w+)", mach, re.M).group(1)
    ths = []
    for name, s, e, doc in WORD:
        ths.append(prove(m, name, s, e, doc=doc + ": the head reads neither L nor R.", count_first=True,
                         max_seg=40, rotate=True)[0])
    for name, s, e, doc in APH:
        ths.append(prove(m, name, s, e, doc=doc, count_first=True, max_seg=40, rotate=True)[0])
    for name, s, e in (ANOM if m == "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---" else []):
        ths.append(prove(m, name, s, e, doc="anomaly, word a block 2c+2 and a single 1, one-unit counter",
                         count_first=True, max_seg=40, rotate=True)[0])
    for name, s, e in ANOMX.get(m, []):
        ths.append(prove(m, name, s, e, doc="anomaly, word a block and a single 1, one-unit counter (this machine's "
                         "form; found uniform in simulation, proved here for all parameters)",
                         count_first=True, max_seg=40, rotate=True)[0])
    for name, s, e, doc in coll_cases(TABLES[m]):
        ths.append(prove(m, name, s, e, doc=doc, count_first=True, max_seg=40, rotate=True)[0])
    print(rules_file("Transients", ns, ths,
                     f"The irregular steps of {m} not in Rules.lean or Transients.lean: the word phase, the A phase "
                     "of a collision, the anomaly with a one-unit counter.  Generated by `py/gen_collide.py` in the "
                     "folder of 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---; do not edit by hand."), end="")


if __name__ == "__main__":
    main()
