"""Writes lean/Rules.lean: shift rules of 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC.

Write `a` for the word 1111110.  The head works between the rightmost `000` and the right end of the tape:

* `walk`:          C walks left over ones, five steps a cell, changing nothing;
* `words_left`:    C walks left through a block of words `a`: every 0 moves one cell to the right;
* `glider`:        the three cells `110` with B on the first pass a block of words `a` to the right, unchanged;
* `ones_to_words`: E turns a run of ones into words of five ones (`101111` per six cells);

The level cycle  1^(x+1) 000 a^(y+2) 11111 0 1111 0 1^12 B>  ->  1^(x+16) 000 a^(y+1) (same tail), 144 y + 598 steps,
is a chain of 21 such pieces; `bbtools.symtm.prove` finds it, but its Lean term is too heavy for the kernel in one
theorem, so it is checked by replay only (py/cyc.py proves it symbolically each time it uses it).

usage: python3 rules.py > ../lean/Rules.lean
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC"
NS = "H92170"
RULES = [
    ("walk", "C walks left over ones without changing them (five steps a cell).",
     "L 1 (1)^n C> 1 R", "L C> 1 (1)^n 1 R", {}),
    ("words_left", "C walks left through a block of words 1111110: every 0 moves one cell to the right.",
     "L 1 (0111111)^n+1 C> 1 R", "L C> 1 (1011111)^n+1 1 R", {}),
    ("glider", "The glider 110 (B on its first cell) passes a block of words 1111110 and leaves it unchanged.",
     "L B> 1 1 0 (1111110)^n R", "L (1111110)^n B> 1 1 0 R", {"rotate": True}),
    ("ones_to_words", "E turns a run of ones into words of five ones.",
     "L E> 1 1 1 1 1 1 1 (111111)^n R", "L 1 0 1 1 1 1 (101111)^n E> 1 R", {"rotate": True}),
]


def main():
    thms = []
    for name, doc, a, b, kw in RULES:
        t, _ = prove(M, name, a, b, doc=doc, max_seg=3000, **kw)
        thms.append(t)
    print(rules_file("Machine", NS, thms, __doc__.split("\n\n")[0] + " Written by `py/rules.py` with "
                     "`bbtools.symtm.prove`; checked by the kernel."), end="")


if __name__ == "__main__":
    main()
