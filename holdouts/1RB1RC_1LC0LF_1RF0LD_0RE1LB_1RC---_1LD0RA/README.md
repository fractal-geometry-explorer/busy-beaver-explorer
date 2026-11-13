# 1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA

bbchallenge id 147335. One of the six-state holdouts whose halting from blank tape is open (group G07, family: **several counters written as runs of 11010, 110 11010, 110 11010 11010 and 1**).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1LC | 0LF |
| C | 1RF | 0LD |
| D | 0RE | 1LB |
| E | 1RC | --- |
| F | 1LD | 0RA |

## What it does

Write `a = 11010` and `b = 110`. The tape is a few long runs of the words `a`, `b a` and `b a a`, a block of 1s,
and a short **tail** at the right end, so the machine is a counter machine whose counters are run lengths. It runs
in **cycles**. A cycle starts when the head, at the left end in state D, sees

    0 0 b a^n b (b a a) (b a)^q b X 1^r T          (X = `1 b` or `0`, T the tail)

- **Phase I** (q double visits): each two visits of the left end turn one `(b a)` into two more `a`s and two more 1s:
  n += 2, q -= 1, r += 2 (e.g. `a^91 ... (ba)^95 ... 1^193` at step 3,086,637 becomes `a^280 ... (ba)^1 ... 1^381`).
- **Phase II**: the head now walks back one `a` per visit, building runs of `(b a a)` and `(b a)` out of the `a`s and
  the block of 1s, until the next cycle starts with new counters (n', q', r') and a slightly changed tail.

The cycle starts in the first 10^9 steps (step, n, q, r):

| step | n | q | r |
|---|---|---|---|
| 1,414,799 | 49 | 69 | 140 |
| 3,086,637 | 91 | 95 | 193 |
| 6,431,415 | 150 | 133 | 257 |
| 13,003,629 | 238 | 178 | 354 |
| 25,377,823 | 354 | 239 | 481 |
| 48,414,485 | 509 | 323 | 645 |
| 90,959,903 | 721 | 433 | 864 |
| 168,799,893 | 1007 | 579 | 1161 |
| 310,402,437 | 1387 | 777 | 1556 |
| 566,898,199 | 1901 | 1039 | 2081 |

Exactly, at every one of these cycles, **3q' = 4q + c** with a small c (2, 5, 7, 9, 13, 15, 17 or 19, depending on the
tail and on q mod 3), **n' + q' = n + 2q + d** with d in {-2, ..., 2}, and **r' = 2q' + e** with e in {-9, ..., 3}. So the
main counter follows a Collatz-like map q' = (4q + c)/3, growing by a factor 4/3 per cycle (a cycle takes about
1.8 times as many steps as the one before), and n/q tends to 2. The corrections c, d, e are decided by the tail,
which each cycle rewrites a little: a record of the residues, as in the other Collatz-like holdouts.

## Status

Open. Lean: the halting configurations and 10^7 steps (`lean/Blank.lean`), and the shift rules for the head
crossing runs of `a` (state D, leftwards) and of `110` (state B leftwards, state F rightwards), for any length
(`lean/Shifts.lean`, kernel). Simulation: no halt in 10^9 steps (12 complete cycles); the cycle table is printed
by `py/cycles.py`:

    ./tmrun 1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA 1000000000 at D L 100000000 | python3 holdouts/1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA/py/cycles.py

## Next steps

Prove Phase I as a Lean rule (two visits: `(b a)^(q+1)` to `(b a)^q`, n + 2, r + 2) and Phase II likewise, find how
the tail and q mod 3 fix c, d, e, and then iterate the cycle map with a reduced simulation (as for
1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA) far beyond direct simulation. The halt (state E reading a 1) would come
from the tail.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.496; right: fixed,
exponent 0.04). After 1,000,000,000 steps: 26,735 cells visited (19,632 left of the
start, 62 right), 17,233 ones.

- left, step 971,325,213: `D>0 0 1^2 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 `
- left, step 987,006,021: `D>0 0 1^2 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 `

## Pages

- [`pages/holdouts/1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA/explainer.html`](../../pages/holdouts/1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA/explainer.html)
- [`pages/holdouts/1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA/proof-status.html`](../../pages/holdouts/1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA/lean/check.sh
```
