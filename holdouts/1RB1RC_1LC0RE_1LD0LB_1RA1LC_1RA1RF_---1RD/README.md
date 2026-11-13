# 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD

bbchallenge id 136824. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1LC | 0RE |
| C | 1LD | 0LB |
| D | 1RA | 1LC |
| E | 1RA | 1RF |
| F | --- | 1RD |

## What it does

Same first four states as 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC and the same mechanism (see that README): at each
visit of the left end in state D the tape is `0^inf D>0 1^n R 0^inf`, the block grows by two per sweep and `R` is
transformed by a fixed map. Events at visits 97 (`R` = 217 cells) and 1481 (`R` = 2,987 cells).

Here the counter is very regular: its front is 131, 251, 371, 491, 683 cells deep after 2^4, 2^9, 2^13, 2^17, 2^24
visits (12, 24, 36 cells per doubling in turn, about 28 on average). About 2,300 cells remain, so the next event is
about 2^80 visits (about 1e48 steps) away. A halt needs `B>1 1 0` (B1 -> 0RE, E1 -> 1RF, F0 halts), only possible at
the far end.

## Status

Open.

- **Kernel / native_decide:** `lean/Blank.lean`.
- **Computed (trusted):** `resetsim` (in `holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/`) agrees with the true
  run at all of the first 6,000 visits apart from the two events; from visit 1490 it runs 3e7 visits (about 1.7e15
  steps) with no halt and no event.
- **Heuristic:** the front speed and the 2^80 estimate.
- **Open:** whether an event ever halts.

```sh
gcc -O2 -o resetsim holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC/c/resetsim.c -I tools/c
./resetsim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD L D 1 40 2 6000 check
FRONT=1 T0=1490 ./resetsim 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD L D 1 40 2 30000000
```

## Next steps

The regular front (12/24/36 cells per doubling) suggests an exact counter: decode its digits from the region
(`PFROM`/`PTO` print it) and prove the counter rule; then the next event, and whether it halts, could be computed.

## Pages

- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/explainer.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/explainer.html)
- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/proof-status.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/lean/check.sh
```
