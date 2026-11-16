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

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel,
in 10,000,000 by `native_decide`; a run-length frame map with every case proved (below, "Earlier approaches").
C (`tools/c/tmrun.c`): no halt in 10,000,000,000 steps. The macro laws below are measured, not proved.

## What it does

**Overflows.** An overflow is a time when E is at the left end of the tape and the tape reads
`E>0 1 0 1^(4n+1) 0 ...` (it comes 10 steps after a time with `E>1 1 0 1^(4n-3) ...`). Within an epoch n goes up by
one per overflow, so the left block grows by 4 cells, and the gaps follow

```
D(n+1) = 2 D(n) + 20
```

except at the overflows where the word to the right changes shape: in the epoch from step 513,974,658 the
correction is 20 at 33 of the 42 overflows up to step 6.4·10^9, and 36, 4, 112, -228, 80, 312, -304, 4 at the others
(`py/overflows.py`).

**Two phases in an epoch.** Write the tape at an overflow as `E>0 1 0 1^(4n+1) 0 w`. At the start of an epoch w
begins with a second block of the same length and a run of `0 1`s: `1^(4n+1) 0 1^(4n+1) (0 1)^r ...`, and each
overflow grows both blocks by 4 and uses up one `0 1` (`1^13 0 1^13 (0 1)^20 ...`, `1^17 0 1^17 (0 1)^19 ...`, from
step 513,975,146). When the run is used up (step 516,857,786: `1^61 0 1^65`) the second block stops at `1^61`, and
from then on each overflow changes w only further right, where a block `1^(4j+1)` grows through another run of
`0 1`s, one `0 1` per overflow (`0 1 0 1 0 1 0 1 0 1^9`, `... 1^13`, `... 1^17` at steps 6.06·10^8, 6.99·10^8,
8.83·10^8), and then a third level. So w is a slowly changing word of higher digits, each level a block walking
through a run of `0 1`s, the structure of a counter of counters.

**Epochs.** At steps 327,783, 378,432,855 and 513,974,658 the left block falls back to `1^5`
(`E>0 1 0 1^5 0 1^5 ...`) and a new epoch starts with a longer word; the width jumped from 238 cells at 10^8
steps to 419 at 10^9.

**Halting.** Only F0 halts; F is entered only from B1 (`0LF`), 11,363,688 times in 10^8 steps, always onto a 1.

## How far it was run

C cell by cell (`tools/c/tmrun.c`): 10^10 steps (n = 105 at step 6,419,556,126). No accelerated simulator yet:
the token model of `1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD` (same family) is the model to imitate; here the digits
are the blocks `1^(4j+1)` and the runs of `0 1`.

## Open questions

- The digit word at the times between overflows: during a count the tape left of the head is `1^2 0^(4a+3) 1
  0^(4b+3) 1 ...` (gaps of 0s, lengths 3 mod 4) and right of the head blocks `1^(4c+1)` between single 0s; a token
  model on these (as for 1RB0RC_1LC0RE) with rules proved in Lean is the next step, then the overflow law and the
  epoch change as theorems.
- An epoch extrapolation like the one of 1RB0RC_1LC0RE (shorten the run of `0 1`s that the walking block uses up,
  fit the laws, extrapolate) would show the next epochs; it needs that token model or a fast raw-tape version.

## Earlier approaches

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
