# 1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA

bbchallenge id 158007. One of the six-state holdouts whose halting from blank tape is open. It is `1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD` with the states renamed, and runs the same binary counter in epochs.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 1RC | 0RD |
| C | 1LD | 0RE |
| D | 0LA | 0LC |
| E | 1LC | 1RF |
| F | --- | 0RA |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 1,000,000,000 steps.

## What it does

The table is that of `1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD` with states renamed (here A, B, C, D = there D, A, B, C), so the start state differs.
The runs fall into step: at every time this machine is at the left end in state A, its tape equals the twin's tape
77 steps later (state D at the left end), except for the last two cells (at step 553,148,029 this one ends
`...1 0 1 0 1`, the twin at 553,148,106 ends `...1 0 1 0 1^3`). See the twin's README for the counter: digits as
`00`/`11` pairs, overflows `A>0 0 1^(2n+1) -> A>0 0 1^(2n+3)` doubling in time, a marker walking right one `10` per
overflow, epoch restarts (here at steps 8, 37, 206, 809, 3,782, 17,297, 22,706,588 and 81,579,887;
`python3 holdouts/1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/py/digits.py 100000000 twin` prints the digit strings).

Halting: only F0; F is entered only from E1 (`1RF`), 9,523,774 times in 10^8 steps, always onto a 1.

## Later

- Run-length frame map (`py/frames.py`, `lean/Pieces.lean`, `lean/Cases.lean`, `lean/Frames.lean`): frames
  are the two sides of the head as lists of runs; 68 cases, each proved by a symbolic run for all parameters
  and all lists, so the frame map is sound (`rlNext_sound`); the run from blank tape reaches its first frame and
  the first 100,000 frames exist (`native_decide`). Open: that the table is defined on every frame the machine reaches.
  That needs an invariant of the run lists closed under the table; `NGramClosure` in `bbtools.listframe` (n-grams
  of runs, lengths cut at 4) did not close for 1RB0RC_1LC0RE with n = 3 (the over-approximation reaches a frame
  that halts) and ran out of time with n = 4.
- Frame maps with scalar parameters (the method of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC) do not close here:
  `py/shapes.py 1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA 10000000 7` finds 455,393 distinct tape shapes at head turns in 10^7 steps, growing tenfold
  per decade (32 for that machine). A proof needs frames with a list parameter (the counter's digit word), and
  Lean pieces that act on the word by induction.
- Any proof for the twin should carry over; the different right end needs checking.

## First look

Growth class **fixed/power** (left: power, exponent 0.155; right: fixed,
exponent 0.081). After 1,000,000,000 steps: 181 cells visited (155 left of the
start, 23 right), 103 ones.

- left, step 553,148,028: `D>0 1^35 0 1^25 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1`

## Pages

- [`pages/holdouts/1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/explainer.html`](../../pages/holdouts/1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/explainer.html)
- [`pages/holdouts/1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/proof-status.html`](../../pages/holdouts/1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD`](../1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
