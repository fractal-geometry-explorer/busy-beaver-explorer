# 1RB1LE_1LC0LF_1LA1RD_1LB0RD_0LC0LA_---1RA

bbchallenge id 5088. One of the six-state holdouts whose halting from blank tape is open. It is a binary counter (overflows doubling in time) in epochs.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 1LC | 0LF |
| C | 1LA | 1RD |
| D | 1LB | 0RD |
| E | 0LC | 0LA |
| F | --- | 1RA |

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 10,000,000,000 steps.

## What it does

- **Overflows.** At the times E is at the left end with tape `E>0 10 1^k 110 ...`, k grows by 4 and the gaps double
  (to within a few hundred steps; k = 83, ..., 103 at steps 698,523,614, 883,072,970, 1,252,171,762, 1,990,369,658, 3,466,765,146,
  6,419,556,126).
- **Word.** The rest is blocks `1^(odd)` separated by `110` and runs of `10`, changing slowly, like higher digits.
- **Epochs.** A restart between steps 3.78*10^8 and 5.14*10^8 grew the tape from 238 to about 400 cells.
- **Halting.** Only F0 halts; F is entered only from B1 (`0LF`), 11,363,688 times in 10^8 steps, always onto a 1.

## Later

- Run-length frame map (`py/frames.py`, `lean/Pieces.lean`, `lean/Cases.lean`, `lean/Frames.lean`): frames
  are the two sides of the head as lists of runs; 165 cases, each proved by a symbolic run for all parameters
  and all lists, so the frame map is sound (`rlNext_sound`); the run from blank tape reaches its first frame and
  the first 100,000 frames exist (`native_decide`). Open: that the table is defined on every frame the machine reaches.
  That needs an invariant of the run lists closed under the table; `NGramClosure` in `bbtools.listframe` (n-grams
  of runs, lengths cut at 4) did not close for 1RB0RC_1LC0RE with n = 3 (the over-approximation reaches a frame
  that halts) and ran out of time with n = 4.
- Frame maps with scalar parameters (the method of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC) do not close here:
  `py/shapes.py 1RB1LE_1LC0LF_1LA1RD_1LB0RD_0LC0LA_---1RA 10000000 7` finds 316,491 distinct tape shapes at head turns in 10^7 steps, growing tenfold
  per decade (32 for that machine). A proof needs frames with a list parameter (the counter's digit word), and
  Lean pieces that act on the word by induction.
- Find the counter's digits and prove one overflow symbolically; then the epoch change.

## First look

Growth class **fixed/power** (left: power, exponent 0.133; right: fixed,
exponent 0.088). After 1,000,000,000 steps: 420 cells visited (349 left of the
start, 50 right), 244 ones.

- left, step 698,523,614: `E>0 1 0 1^85 0 1^61 0 1 0 1 0 1 0 1 0 1 0 1^13 0 1 0 1 0 1^5 0 1^5 0 1 0 1 0 1^9 0 1 0 1^5 0 1^5 0 1^5 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^13 0 1^5 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1^9 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1^5 0 1^5 0 1 0 1 0 1^5 0 1^5 0 1^5 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 883,072,970: `E>0 1 0 1^89 0 1^61 0 1 0 1 0 1 0 1 0 1 0 1^17 0 1^5 0 1^5 0 1 0 1 0 1^9 0 1 0 1^5 0 1^5 0 1^5 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^13 0 1^5 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1^9 0 1 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1^5 0 1^5 0 1 0 1 0 1^5 0 1^5 0 1^5 0 1^5 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB1LE_1LC0LF_1LA1RD_1LB0RD_0LC0LA_---1RA/explainer.html`](../../pages/holdouts/1RB1LE_1LC0LF_1LA1RD_1LB0RD_0LC0LA_---1RA/explainer.html)
- [`pages/holdouts/1RB1LE_1LC0LF_1LA1RD_1LB0RD_0LC0LA_---1RA/proof-status.html`](../../pages/holdouts/1RB1LE_1LC0LF_1LA1RD_1LB0RD_0LC0LA_---1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_1LC0LF_1LA1RD_1LB0RD_0LC0LA_---1RA/lean/check.sh
```
