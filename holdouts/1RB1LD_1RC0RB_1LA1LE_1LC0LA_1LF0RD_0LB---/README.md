# 1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---

bbchallenge id 70273. One of the six-state holdouts whose halting from blank tape is open. It is a counter whose overflows come four times further apart each time, in epochs.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1RC | 0RB |
| C | 1LA | 1LE |
| D | 1LC | 0LA |
| E | 1LF | 0RD |
| F | 0LB | --- |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 20,000,000,000 steps.

## What it does

- **Overflows.** When A is at the left end the tape starts `A>0 1^n 110 ...`; n grows by 6 per event and the gaps grow
  by a factor tending to 4 (n = 60, 66, 72, 78, 84 at steps 20,060,883, 78,781,139, 313,662,151, 1,253,186,235,
  5,011,282,607).
- **Counter.** Between overflows the head's excursions from a home cell follow the ruler pattern 2, 4, 2, 6, 2, 4, 2,
  8, ... (both sides), the carries of a counter. Each overflow changes the word on the right (made of `10`, `110`,
  `1^k`) by a few cells.
- **Epochs.** At step 488,707 the left block drops from `1^39` to `1^18`, at step 7,842,487,335 from `1^84` to
  `1^75`, and a new word appears on the right.
- **Halting.** Only F1 halts; F is entered only from E0 (`1LF`), 16 times in 10^8 steps (12 at the left end, 4 in the
  0s left of the solid block), always with a 0 to the left, so F reads 0.

## Later

- Run-length frame map (`py/frames.py`, `lean/Pieces.lean`, `lean/Cases.lean`, `lean/Frames.lean`): frames
  are the two sides of the head as lists of runs; 310 cases, each proved by a symbolic run for all parameters
  and all lists, so the frame map is sound (`rlNext_sound`); the run from blank tape reaches its first frame and
  the first 100,000 frames exist (`native_decide`). Open: that the table is defined on every frame the machine reaches.
  That needs an invariant of the run lists closed under the table; `NGramClosure` in `bbtools.listframe` (n-grams
  of runs, lengths cut at 4) did not close for 1RB0RC_1LC0RE with n = 3 (the over-approximation reaches a frame
  that halts) and ran out of time with n = 4.
- Frame maps with scalar parameters (the method of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC) do not close here:
  `py/shapes.py 1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB--- 10000000 7` finds 617,359 distinct tape shapes at head turns in 10^7 steps, growing tenfold
  per decade (32 for that machine). A proof needs frames with a list parameter (the counter's digit word), and
  Lean pieces that act on the word by induction.
- Find the counter's digits exactly (which cells near the home position) and prove one increment and one overflow
  symbolically with `bbtools.symtm`; then the epoch-to-epoch map.

## First look

Growth class **fixed/fixed** (left: fixed, exponent 0.04; right: fixed,
exponent 0.0). After 1,000,000,000 steps: 134 cells visited (125 left of the
start, 8 right), 51 ones.

## Pages

- [`pages/holdouts/1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---/explainer.html`](../../pages/holdouts/1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---/explainer.html)
- [`pages/holdouts/1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---/proof-status.html`](../../pages/holdouts/1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---/lean/check.sh
```
