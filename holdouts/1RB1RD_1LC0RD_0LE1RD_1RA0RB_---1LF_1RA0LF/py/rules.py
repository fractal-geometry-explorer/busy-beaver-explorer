"""Writes lean/Shifts.lean: the long crossings of 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF.

The bulk of the tape is a run of 11-cell words. Going right the head (B, carrying 01111 behind it) turns every word
01010000000 into 01111111111; coming back (F, with twelve 0s in front) it turns every 01111111111 into
10100000000; and in the counter list F turns 011 into 101:

    L 01111 B> (01010000000)^(n+1) R   ->   L (01111111111)^(n+1) 01111 B> R        53 steps a word
    L (01111111111)^n F> 0^12 R        ->   L F> 0^12 (10100000000)^n R             19 steps a word
    L (011)^n F> 0^4 R                 ->   L F> 0^4 (101)^n R                      11 steps a word

The first is found and proved by `bbtools.symtm.prove`; the two leftward ones are `TM.cross_l` with the one-word run
checked by `rfl`. `c/accsim.c` finds the same rules on the fly (and others, e.g. B and D alternating over 101 101).

usage: python3 rules.py > ../lean/Shifts.lean
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF"
NS = "H71111"


def bools(s):
    return "[" + ", ".join("true" if c == "1" else "false" for c in s) + "]"


def left_rule(name, doc, word, ctx, out, steps):
    """`L word^n F> ctx R -> L F> ctx out^n R`: word and out in tape order, the head on the first cell of ctx."""
    w, u, v = bools(word[::-1]), bools(ctx), bools(out)
    return (f"/-- {doc} -/\n"
            f"theorem {name} (n : Nat) (L R : Tape) :\n"
            f"    steps (n * {steps}) ⟨rep n {w} L, app {u} R, .F⟩ = some ⟨L, app {u} (rep n {v} R), .F⟩ := by\n"
            f"  have c0 : ∀ L R : Tape, steps {steps} ⟨app {w} L, app {u} R, .F⟩ = some ⟨L, app {u} (app {v} R), .F⟩ :=\n"
            f"    fun _ _ => rfl\n"
            f"  exact cross_l trans c0 n L R\n")


def main():
    thms = [prove(M, "bulk_right", "L 0 1 1 1 1 B> (01010000000)^n+1 R", "L (01111111111)^n+1 0 1 1 1 1 B> R",
                  doc="Going right through the bulk: B, with 01111 behind it, turns every word 01010000000 into "
                      "01111111111, 53 steps a word.", rotate=True, max_seg=80)[0],
            left_rule("bulk_left", "Coming back through the bulk: F, on the first of twelve 0s, turns every word "
                      "01111111111 on its left into 10100000000 on its right, 19 steps a word.",
                      "01111111111", "0" * 12, "10100000000", 19),
            left_rule("list_left", "In the counter list: F, on the first of four 0s, turns every 011 on its left into 101 on "
                      "its right, 11 steps a word.", "011", "0000", "101", 11)]
    print(rules_file("Machine", NS, thms, "The long crossings of 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF. Written by "
                     "`py/rules.py` (`bbtools.symtm.prove` and `TM.cross_l`); checked by the kernel."), end="")


if __name__ == "__main__":
    main()
