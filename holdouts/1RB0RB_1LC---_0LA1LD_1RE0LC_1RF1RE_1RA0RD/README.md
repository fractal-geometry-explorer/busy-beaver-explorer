# 1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD

bbchallenge id 126123. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 1LC | --- |
| C | 0LA | 1LD |
| D | 1RE | 0LC |
| E | 1RF | 1RE |
| F | 1RA | 0RD |

## What it does

Here the left side is the bouncer: about 2 new cells per round trip (square root of the steps); the right side
grows very slowly. With the head in D at the left end the tape is runs of 1 separated by single 0s, alternating
1 and 4j + 1, i.e. a string of digits j (seen up to 8). Step 28,947,103 (width 8,068) starts with runs
`1 1 1 5 1 5 1 9 1 5 1 1 1 1 1 5 1 9 1 9 1 5 ...`. One round trip later the string is completely different, with no
visible regularity.

The passes are local rewritings, proved for every n in `lean/Rules.lean`:

- `left_pass`: `(11)^n C> 1  ->  C> 1 (01)^n` (2n steps);
- `right_D`: `D> (0101)^n  ->  (1110)^n D>`; `right_E`: `E> (0101)^n  ->  (1011)^n E>` (4n steps);
- `right_ones`: E crosses `1^n` unchanged.

What happens at the boundaries between runs, where one rule hands over to another, scrambles the digits.

## Status

Open. The only halt is B reading a 1. B always follows A; A follows C reading 0 (then B reads the 0 C wrote) or F
reading 0, which needs E to read a 0 followed by another 0. Inside the tape that never happened: in 2·10^8 steps E
read a 0 about 12.5 million times and inside the tape the next cell was always a 1; all 44 visits of F to a 0 in
10^10 steps were at the blank right end. So it halts iff a `00` (with a 1 two cells after it) ever forms inside
the tape ahead of a right-moving E.

- Lean, kernel: the four pass rules (`lean/Rules.lean`); halting configurations, 10^4 steps (`lean/Blank.lean`).
  `native_decide`: 10^7 steps.
- Computed: no halt in 10^10 steps (`tools/c/tmrun.c`); `bbtools.ctl` K = 2..7 allows a halt; n-gram CPS fails.

## Notes for later

- Find what one round trip does to the digit string (it may be arithmetic on a number written in an unusual base:
  compare consecutive samples at the left end in D).
- Look for an invariant excluding `00` inside the tape (it is not a K <= 7 window language).

## Pages

- [`pages/holdouts/1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD/explainer.html`](../../pages/holdouts/1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD/explainer.html)
- [`pages/holdouts/1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD/proof-status.html`](../../pages/holdouts/1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD`](../1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF`](../1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/README.md): rename A→B, B→C, C→D, D→E, E→F, F→A; it is this table started in state F
- [`1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA`](../1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/README.md): rename A→D, B→E, C→F, D→A, E→B, F→C; it is this table started in state D
- [`1RB1RA_1RC0RF_1RD0RD_1LE---_0LC1LF_1RA0LE`](../1RB1RA_1RC0RF_1RD0RD_1LE---_0LC1LF_1RA0LE/README.md): rename A→C, B→D, C→E, D→F, E→A, F→B; it is this table started in state E

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---`](../1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/README.md) (in a mirror): 4,990,813 configurations, the last at step 10,000,000 here and step 6,660,591 there

<!-- end of related machines -->
