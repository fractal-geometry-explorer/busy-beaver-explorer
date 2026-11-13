# 1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD

bbchallenge id 145349. One of the six-state holdouts whose halting from blank tape is open. It is a binary counter (digits written as 00 and 11) whose overflows double in time, organised in epochs.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 0RE |
| C | 0LD | 0LB |
| D | 1RA | 1LE |
| E | 1LB | 1RF |
| F | --- | 0RD |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 20,000,000,000 steps.

## What it does

- **Counter.** Left of the head the cells read as pairs `00`/`11`, binary digits; the head's leftward excursions
  follow the ruler sequence (2, 4, 2, 6, 2, 4, 2, 8, ... cells), as carries in a binary counter do.
- **Overflows.** At each time the head is at the left end in state D the tape starts `D>0 0 1^(2n+1) 0`, n going up by
  one each time within an epoch, and the gaps between these times double (58,949,630, 117,899,246, 235,798,526
  steps, ...).
- **Marker and epochs.** Read the tape after `D>0 0` at an overflow as digits d (blocks `1^(2d+1)` between single
  0s; `py/digits.py`). The first digit is n. In an epoch the other digits are mostly 0 with one marker digit,
  alternately 2 and 1, moving right 3 places per 2 overflows; when it reaches the `1 0 0 1` at the right end the
  string is rewritten and n starts again from 0. Restarts in the first 10^8 steps: 5, 54, 233, 846, 3,829, 17,354,
  22,706,655 (n was 20), 81,579,964 (n was 19); at 15,172,656,784 n = 22. Width grows like the log of the time.
- **Epoch restarts do not close (yet).** The rewritten string differs in shape from epoch to epoch
  (`0 1 0 2 0 2 0 6 0 3 0...0 1 0 0 1` at 22,706,655, `0 1 12 1 0 0 0 0 0 0 0 1 0 0 2 2 0...0 1 0 0 1` at 81,579,964):
  its left part is a higher-level counter that changes once per epoch. An exact epoch map needs a description of that
  level too; it was not found in Phase 2.
- **Halting.** Only F0 halts; F is entered only from E1 (`1RF`). In 10^8 steps F is entered 9,523,781 times, always
  onto a 1.
- **Twin.** `1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA` is this machine with states renamed (A->D, B->A, C->B, D->C); at step 553,148,029 its tape
  equals this one's at step 553,148,106 except for the last two cells (`...1 0 1` instead of `...1 0 1^3`).

## Later

- Run-length frame map (`py/frames.py`, `lean/Pieces.lean`, `lean/Cases.lean`, `lean/Frames.lean`): frames
  are the two sides of the head as lists of runs; 69 cases, each proved by a symbolic run for all parameters
  and all lists, so the frame map is sound (`rlNext_sound`); the run from blank tape reaches its first frame and
  the first 1,000,000 frames exist (`native_decide`). Open: that the table is defined on every frame the machine reaches.
  That needs an invariant of the run lists closed under the table; `NGramClosure` in `bbtools.listframe` (n-grams
  of runs, lengths cut at 4) did not close for 1RB0RC_1LC0RE with n = 3 (the over-approximation reaches a frame
  that halts) and ran out of time with n = 4.
- Frame maps with scalar parameters (the method of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC) do not close here:
  `py/shapes.py 1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD 10000000 7` finds 454,843 distinct tape shapes at head turns in 10^7 steps, growing tenfold
  per decade (32 for that machine). A proof needs frames with a list parameter (the counter's digit word), and
  Lean pieces that act on the word by induction.
- Describe one counter increment symbolically (`bbtools.symtm` shift rules over the `00`/`11` digits) and prove the
  overflow rule `D>0 0 1^(2n+1) ... -> D>0 0 1^(2n+3) ...` for all n by induction in Lean.
- Work out the epoch change exactly. The marker walk inside an epoch is regular (see above); the restart rewrites
  the left part of the digit string by a rule not yet known, so a higher-level counter has to be identified first.
- Do the same for the twin `1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA`; one proof should cover both.

## First look

Growth class **fixed/power** (left: power, exponent 0.152; right: fixed,
exponent 0.085). After 1,000,000,000 steps: 183 cells visited (158 left of the
start, 22 right), 108 ones.

- left, step 553,148,105: `C>0 1^35 0 1^25 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1^3`

## Pages

- [`pages/holdouts/1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/explainer.html`](../../pages/holdouts/1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/explainer.html)
- [`pages/holdouts/1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/proof-status.html`](../../pages/holdouts/1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/lean/check.sh
```
