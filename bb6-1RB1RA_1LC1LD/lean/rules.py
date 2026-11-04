"""Generate Rules.lean: the rules of 1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB that the macro step of `Macro.lean` is
built from, each proved along a symbolic run (tools/py/bbtools/symtm.py: single steps by `rfl`, shift rules by
`TM.cross_r`/`TM.cross_l`).

usage: python3 rules.py > Rules.lean      (tests/test_machine.py checks that the committed file is current)

Tapes are written left to right: `S>` is the head in state S on the next cell, `1^n` is n ones, `(w)^t` the word w
repeated t times, L and R are any tape.  The pass configuration is `K = L 0 1^n B> 1 0 1 0^inf`, three steps after A
reaches the blank cell right of a last block of n + 1 ones.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "py"))
from bbtools.symtm import prove, rules_file  # noqa: E402

M = "1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB"

RULES = [
    ("start", "L 0 1^n 1 A> 0^inf", "L 0 1^n B> 1 0 1 0^inf",
     "A at the blank cell right of the last block: three steps later the pass configuration `K`."),
    # The converter: B runs left over the last block, 7 steps per 3 cells, turning `111` into `101`; what happens at
    # the block's left end depends on its length mod 3 (and the parity of the quotient, for the A-phase below).
    ("conv3", "L 0 1^x 0 1 1 1 B> 1 0 1 0^inf", "L 0 1^x+6 0 B> 1 0 1 0^inf",
     "Last block 4: the block to its left gains 6 and the last block becomes 1."),
    ("conv6t9", "L 0 1^x 0 1 1 1 (111111)^t+1 B> 1 0 1 0^inf", "L 0 1^x+6 0 1 1 1 A> 0 1 (101101)^t 1 0^inf",
     "Last block 6t + 10: the block to its left gains 6, a block 3 starts, and A runs right over the converted cells."),
    ("conv6t6", "L 0 1^x 0 (111111)^t+1 B> 1 0 1 0^inf", "L 0 1^x+6 0 1 1 A> (101101)^t 1 0^inf",
     "Last block 6t + 7: the block to its left gains 6, a block 2 starts, and A runs right over the converted cells."),
    ("conv6t1", "L 0 1^d 0 1^c 0 1 (111111)^t B> 1 0 1 0^inf", "L 0 1^d+2 0 1^c+2 A> (101101)^t 1 0^inf",
     "Last block 6t + 2: B carries to the block two to the left, which gains 2, and the block before gains 2."),
    ("conv6t4", "L 0 1^d 0 1^c 0 1 1 1 1 (111111)^t B> 1 0 1 0^inf", "L 0 1^d+2 0 1^c+3 0 1 B> (101101)^t 1 0^inf",
     "Last block 6t + 5: as for 6t + 2, with one cell left over (`0 1 B>`)."),
    ("left_end", "L 0 1^d 0 1^c 0 1 B> 1 0^inf", "L 0 1^d+2 0 1^c+1 B> 1 0 1 0^inf",
     "The left-over cell with nothing after it: the pass configuration again."),
    ("left_two", "L 0 1^d 0 1^c 0 1 B> 1 0 1 1 0 1 1 R", "L 0 1^d+2 0 1^c+4 0 0 1 B> R",
     "The left-over cell before two converted words `011`: a bounce, ending in the phase `Y`."),
    # The two phases of the run back to the right: `A` (A before the next word `011`) and `Y` (`0 0 1 B>` before it).
    # Each word `011` moves the head from one phase to the other; going from Y to A the two blocks to the left grow.
    ("a_two", "L 0 1^x 0 1^y A> 0 1 1 R", "L 0 1^x 0 1^y 0 0 1 B> R",
     "Phase A meets a word `011`: phase Y."),
    ("y_two", "L 0 1^x 0 1^y 0 0 1 B> 0 1 1 R", "L 0 1^x+2 0 1^y+4 A> R",
     "Phase Y meets a word `011`: a bounce to the block two to the left, then phase A with the blocks 2 and 4 longer."),
    ("y_end", "L 0 1^x 0 1^y 0 0 1 B> 0^inf", "L 0 1^x+2 0 1^y+1 B> 1 0 1 0^inf",
     "Phase Y at the blank end of the tape: the pass configuration again."),
    # The block machine of `Recur.lean`, for the recursive case (last block a multiple of 3): one rule per state and
    # first word, with `1^k` the ones of the word under the head (`0 1^k`) and `(0)^k` that many 0s.
    ("ra_tok", "L A> 0 1 1^k R", "L (0)^k 0 1 B> R", "A at a word `0 1^(k+1)`: B starts converting a block 1."),
    ("rd_one", "L 0 1^x D> 0 1 R", "L 0 1^x+2 D> R", "D at a word `01`: the block gains 2."),
    ("rd_two", "L 0 1^x D> 0 1 1 R", "L 0 1^x+2 0 F> R", "D at a word `011`: the block gains 2, F next."),
    ("rd_tok", "L 0 1^x D> 0 1 1 1 1^k R", "L 0 1^x+2 (0)^k 0 1 B> R", "D at a word `0 1^(k+3)`."),
    ("re_one", "L 0 1^x E> 1 0 1 R", "L 0 1^x+3 D> R", "E at a word `01`."),
    ("re_two", "L 0 1^x E> 1 0 1 1 R", "L 0 1^x+3 0 F> R", "E at a word `011`."),
    ("re_tok", "L 0 1^x E> 1 0 1 1 1 1^k R", "L 0 1^x+3 (0)^k 0 1 B> R", "E at a word `0 1^(k+3)`."),
    ("ra_run", "L A> 1^h R", "L 1^h A> R", "A runs right over ones."),
    ("rf_tok", "L 0 1^x F> 0 1^k R", "L 0 1^x+k+1 A> R", "F at a word: it joins the block."),
    ("rc_tok", "L 0 1^c 1 C> 0 1^k R", "L 0 1^c (0)^k 0 1 B> R", "C after a block `1^(c+1)`: one cell moves on."),
    ("rc_one", "L 0 1^d 0 C> 0 1 R", "L 0 1^d+2 0 F> R", "C after an empty block, at a word `01`."),
    ("rc_more", "L 0 1^d 0 C> 0 1 1 1^k R", "L 0 1^d+2 (0)^k 0 1 B> R", "C after an empty block, at a word `0 1^(k+2)`."),
    ("rb_one", "L 0 1^c 0 1 (111)^j B> 0 1^k R", "L 0 1^c B> 0 0 (101)^j 1 1^k R",
     "The converter at a block `3j+1`: it goes on to the next block, the converted cells become words."),
    ("rb_two", "L 0 1^c 0 1 1 1 1 1 (111)^j B> 0 1^k R", "L 0 1^c 1 1 1 E> (101)^j 1 0 1 1 1^k R",
     "The converter at a block `3j+5`: E turns back."),
    ("rb_two0", "L 0 1^c 0 1 1 B> 0 1^k R", "L 0 1^c 1 1 1 E> 1 1^k R", "The converter at a block 2."),
    ("rb_zero", "L 0 1^c 0 (111)^j B> 0 R", "L 0 1^c C> 0 1 (011)^j R",
     "The converter at a block `3j` before an empty word: C turns back."),
    ("rb_three", "L 0 1^d 0 1^c 0 1 1 1 (111)^j B> 0 1 1^k R", "L 0 1^d+2 0 1^c+2 A> 1 (011)^j 1 1^k R",
     "The converter at a block `3j+3` before a word: a carry to the block two to the left, then A."),
    ("rb_empty", "L 0 1^c 0 B> 0 1 1^k R", "L 0 1^c C> 0 1 1 1^k R", "The converter at an empty block before a word."),
    ("k_start", "L 0 1^c 0 1 1 (111)^j B> 1 0 1 0^inf", "L 0 1^c B> 0 0 (101)^j 1 0 1 1 0^inf",
     "The pass configuration with the last block `3j+3`: the converter goes on into the block to its left."),
]


def main():
    ths = [prove(M, name, a, b, doc=doc)[0] for name, a, b, doc in RULES]
    sys.stdout.write(rules_file("Machine", "BB6c", ths, f"Rules of {M}, generated by `rules.py`; do not edit by hand."))


if __name__ == "__main__":
    main()
