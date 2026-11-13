# 1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB

Group G08 (two-sided square-root growth). Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 0RC | 0LE |
| C | 0RD | 1RC |
| D | 1LD | 1RE |
| E | 1LA | 1RF |
| F | --- | 0RB |

## What it does

Round trips over a list of blocks. At each turn at the right end, writing `b = 110` and `c = 10`:

      561  c c 1 b^2 0 1 b c b^4 1 1 D>0
      756  c c 1 b 1 b^2 c b^6 1 1 D>0
    1,089  c c 1 1 b c b c c b^8 1 1 D>0
    1,456  c c 1 b^2 0 b^2 1 b^10 1 1 D>0

The leftward pass rewrites every `110` as `010` (A, fifteen steps a word, `pass_left`), so that from the left end
the tape is blocks of `100`; the rightward pass turns them back (C, seven steps a word, `pass_right`). The last block
grows by two on every round trip; the blocks in front of it are rewritten a little each time like the low digits of
a counter, now and then further right like a carry.

**New last blocks** (`c/events.c 3e10`). The last run of b grows by two copies a round trip until a carry reaches
it. Then it is frozen and a new last run starts. Up to 3·10¹⁰ steps this happens at steps 1,909, 13,265, 47,957,
319,522 and 98,472,504. The frozen runs have 11, 23, 35, 133 and 3923 copies. After step 9.8·10⁷ the last run grows
to more than 50,000 copies without a carry reaching it. So the counter in front of the last run has a capacity that
grows very fast. In front of it the list is about 20 runs of b with separators (`c`, `1`, `0`, `1 c`). Most round
trips change the list deep into it: of the 4,170 round trips in the first 10⁸ steps, more than 90% change the list
at 19 or more runs from the front. So a round trip is not a change of a few low digits.

The only halt is F reading a 0, i.e. `E> 1 0` (`halt_E`); in the run F always reads a 1.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `pass_right`, `pass_left` for any n; `halt_E`.
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a
  halt is `1 B> 1` or `D> 1 1 0`.
- `py/turns.py` (heuristic): the tape as words at every turn at an end of the tape.
- `c/events.c` (heuristic): the steps where a new last run of b starts, with the list of runs.

## What is open, next steps

A non-halting proof needs the rule of one round trip on the list of runs, for lists of any length and runs of any
size, and a proof that the rule is defined on every list it produces. A finite table of templates with a
few linear counts, as in the certificate of `1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC` (`lean/SymCheck.lean`), does
not fit directly: the list has a growing number of runs, and a round trip rewrites most of them. Window-based closed
tape languages (`tools/py/bbtools/ctl.py`) find no closed set for windows of 3 to 8 cells. Next steps:

1. Write a round trip as a left pass (`pass_left`), a turn at the left end and a right pass with carries, at the
   level of runs of b and separators, and find the carry rule.
2. Prove the pieces as rules with unknown tape around them and chain them by induction over the list (as in
   `holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/lean/Chain.lean`).
3. Find an invariant language of lists closed under the rule, without `E> 1 0`.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB/lean/check.sh
python3 holdouts/1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB/py/rules.py    # rewrites lean/Rules.lean
python3 holdouts/1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB/py/turns.py 40000 R   # the list at the right-end turns
gcc -O2 -o events holdouts/1RB0LA_0RC0LE_0RD1RC_1LD1RE_1LA1RF_---0RB/c/events.c && ./events 3e10   # new last blocks
```
