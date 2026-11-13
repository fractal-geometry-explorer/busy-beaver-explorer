"""Writes lean/Rules.lean: the moves of the head in the two-cell picture (X = 10, Y = 11, O = 00), each proved by
bbtools.symtm (shift rules, `rfl`, `omega`) for every count and every tape in the contexts L, R.

* reflect, flipX*, flipY*: F moving left turns X into Y and Y into X, and on a blank pair turns round (O -> Y, B right);
* turn0/turn1: `Y B> X X` becomes `<F Y Y Y` (the head turns back at the first double X);
* digit1, digit: `Y B> X Y^d X` becomes `X O^(d-1) Y Y Y B>` (a digit d leaves d - 1 blank pairs: d visits of the
  rest in all);
* bounce, cross: the two moves at the left end found first;
* phase1, phase2, phase4_in, phase4_out: the four phases of the first block's counter, for every block length n
  and every tape R to its right: 0000000 -> 3 00000 -> (+1) 0000 3 -> 3 00 3 -> (+1) 0000000 and one visit of R;
* pure_tape_halts: a tape of X and Y pairs on which the wall visit halts.

usage: python3 rules.py > ../lean/Rules.lean
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, rules_file, cfg_term, Config
from bbtools.machine import Machine

M = "1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA"
NS = "H9123"
HALT_PAIRS = "XYYYYYYYXX"          # the wall visit of this tape of pairs halts
HALT_STEPS = 253

RULES = [
    ("reflect", "F on a blank pair (both cells 0): the pair becomes 11 and B leaves it to the right.",
     "L 0 F> 0 R", "L 1 1 B> R"),
    ("flipX0", "F on the pair 10, a 0 to its left: the pair becomes 11, F goes on to the left.",
     "L 0 1 F> 0 R", "L F> 0 1 1 R"),
    ("flipX1", "The same with a 1 to its left.", "L 1 1 F> 0 R", "L F> 1 1 1 R"),
    ("flipY0", "F on the pair 11, a 0 to its left: the pair becomes 10, F goes on to the left.",
     "L 0 1 F> 1 R", "L F> 0 1 0 R"),
    ("flipY1", "The same with a 1 to its left.", "L 1 1 F> 1 R", "L F> 1 1 0 R"),
    ("turn0", "Y B> X X becomes <F Y Y Y: the head turns back at a double X (a 0 to the left of the Y).",
     "L 0 1 1 B> 1 0 1 0 R", "L F> 0 1 1 1 1 1 1 R"),
    ("turn1", "The same with a 1 to the left of the Y.", "L 1 1 1 B> 1 0 1 0 R", "L F> 1 1 1 1 1 1 1 R"),
    ("digit1", "Y B> X Y X becomes X Y Y Y B>: a digit 1 passes the visit on.",
     "L 1 1 B> 1 0 1 1 1 0 R", "L 1 0 1 1 1 1 1 1 B> R"),
    ("digit", "Y B> X Y^(k+2) X becomes X O^(k+1) Y Y Y B>: a digit d leaves d - 1 blank pairs behind the head.",
     "L 1 1 B> 1 0 (11)^k+2 1 0 R", "L 1 0 (00)^k+1 1 1 1 1 1 1 B> R"),
    ("bounce", "A visit of the left end in F with 0 1 0 1 0 1 0 ahead: back in F at the left end, 16 steps.",
     "0^inf F> 0 1 0 1 0 1 0 R", "0^inf F> 0 1 1 1 1 1 1 1 0 R"),
    ("cross", "From the visit with 0 1 1 1 1 1 1 1 0 (111010)^n ahead, the head crosses the block and enters R in D.",
     "0^inf F> 0 1 1 1 1 1 1 1 0 (111010)^n R", "0^inf 1 1 (111110)^n 1 1 1 1 1 0 0 0 D> R"),
    ("phase1", "Digit word 0...: from the visit `3 (10)^n 0 R` (digits) to the visit `000 (10)^n YYY R`.",
     "0^inf F> 0 1111111 0 (111010)^n 10 R", "0^inf F> 0 101010 (111010)^n 111111 R"),
    ("phase2", "Digit word 3 00000: from the visit `3 (10)^n 3 00000 R` to the visit `000 (10)^(n+1) 0000 3 R`.",
     "0^inf F> 0 1111111 0 (111010)^n 11111110 1010101010 R",
     "0^inf F> 0 101010 (111010)^n 111010 10101010 111111 10 R"),
    ("phase4_in", "Digit word 3 00 3: from the visit `3 (10)^n 3 00 3 R` the head enters R in D (the carry).",
     "0^inf F> 0 1111111 0 (111010)^n 11111110 1010 11111110 R",
     "0^inf 1111111 (011111)^n 0 1111111111111111111 0 0 0 D> R"),
    ("phase4_out", "When F comes back from R, the next visit is `000 (10)^(n+1) 0000000 Y R`.",
     "0^inf 1111111 (011111)^n 0 111111111111111111 1 F> 0 R",
     "0^inf F> 0 101010 (111010)^n 111010 10101010101010 11 R"),
]


def halting_run():
    """The run from the wall visit of HALT_PAIRS to the halting configuration, as two config strings."""
    m = Machine.parse(M)
    cells = "".join({"X": "10", "Y": "11"}[p] for p in HALT_PAIRS)
    start = "0^inf F> 0 " + " ".join(cells) + " 0^inf"
    tape = {i + 1: int(ch) for i, ch in enumerate(cells)}
    pos, st, n = 0, 5, 0
    while True:
        tr = m.table[st][tape.get(pos, 0)]
        if tr is None:
            break
        w, d, s = tr
        tape[pos] = w
        pos += d
        st = s
        n += 1
    assert n == HALT_STEPS, n
    lo, hi = min(min(tape), pos), max(max(tape), pos)
    left = " ".join(str(tape.get(p, 0)) for p in range(lo, pos))
    right = " ".join(str(tape.get(p, 0)) for p in range(pos, hi + 1))
    end = "0^inf " + left + " " + "ABCDEF"[st] + "> " + right + " 0^inf"
    return start, end


def main():
    thms = [prove(M, name, s, e, doc=doc, rotate=True, count_first=True, max_seg=60)[0] for name, doc, s, e in RULES]
    s, e = halting_run()
    t, fin = prove(M, "pure_tape_run", s, e, doc="The wall visit of the tape %s (pairs X = 10, Y = 11): %d steps to a "
                   "configuration with E on a 1." % (HALT_PAIRS, HALT_STEPS), cross=False, count_first=True, max_seg=60)
    thms.append(t)
    thms.append("/-- A tape made of pairs 10 and 11 only on which the wall visit halts (not a tape of the run from blank). -/\n"
                "theorem pure_tape_halts : ∃ c, steps (%d) %s = some c ∧ step c = none :=\n"
                "  ⟨_, pure_tape_run, rfl⟩" % (HALT_STEPS, cfg_term(Config.parse(s))))
    print(rules_file("Machine", NS, thms, "The head's moves in the two-cell picture, the four phases of the first block's "
                     "counter, and a halting tape of pairs. Generated by `py/rules.py`."), end="")


if __name__ == "__main__":
    main()
