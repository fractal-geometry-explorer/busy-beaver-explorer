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

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel,
in 10,000,000 by `native_decide`; a run-length frame map with every case proved (below, "Earlier approaches").
C (`tools/c/tmrun.c`): no halt in 20,000,000,000 steps. The macro laws below are measured, not proved.

## What it does

**Overflows.** An overflow is a time when A is at the left end with the tape `A>0 1^n 0 w` (3 steps after a time
with `A>1 1^(n-3) 0 w`). Within an epoch n goes up by 6 per overflow and the gaps follow

```
D(next) = 4 D + 36
```

except at the overflows where w changes shape (corrections 72, -108, 48, -12 in the epoch from step 488,707;
`py/overflows.py`). So the gaps grow by a factor 4: 3,670,004, 14,680,052, 58,720,256, ... 3,758,096,372 steps.

**The counter.** Between overflows the cells left of the head are `1 0^(3a+2) 1 0^(3b+2) 1 ...` (gaps of 0s, lengths
2 mod 3) and the head's excursions follow the ruler pattern 2, 4, 2, 6, ... cells on both sides: the left block
`1^n` is converted into these gaps and back during one count.

**Marker and epochs.** w is a word of blocks `1^(odd)` separated by single 0s. In an epoch most of it is fixed and one
place moves right through a run of single 1s (digits 0), one per overflow or so:
`... 1^9 0 1 0 1^3 ...`, `... 1^11 0 1^3 ...`, `... 1^11 0 1 0 1^3 ...`, `... 1^11 0 1 0 1^5 ...`, `... 1^5 0 1^3 ...` (steps 5.4·10^6 to
1.25·10^9). When it reaches the `1^2` at the right end, the epoch ends: at step 24,579 the left block falls from
`1^27` to `1^23`, at step 488,707 from `1^41` to `1^20`, at step 7,842,487,335 from `1^86` to `1^77`, and w is
rewritten (longer). Unlike 1RB0RC_1LC0RE the block does not fall back to a few cells: each epoch starts near the
scale the last one reached, and no overflow follows the one at step 7.84·10^9 in the first 8·10^9 steps.

**Halting.** Only F1 halts; F is entered only from E0 (`1LF`), 16 times in 10^8 steps (12 at the left end, 4 in the
0s left of the solid block), always with a 0 to the left, so F reads 0.

## How far it was run

C cell by cell (`tools/c/tmrun.c`): 2·10^10 steps (the overflows to n = 86 and the epoch change at 7.84·10^9). No
accelerated simulator yet.

## Open questions

- A token model: the digits are the gap lengths `0^(3a+2)` left of the head and the blocks on the right; rules for
  one increment proved for all digit words (as for 1RB0RC_1LC0RE), then the overflow law `n -> n + 6`,
  `D -> 4D + 36` and the marker step as theorems.
- The epoch change at the right end (`1^2`), and whether an epoch extrapolation (shorten the marker's run, fit,
  extrapolate) shows the next epochs.

## Earlier approaches

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
