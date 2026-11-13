# 1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---

bbchallenge id 126070. One of the six-state holdouts. Analyzed by hand (group G02), partly.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LB |
| B | 1RC | 1LD |
| C | 1LA | 1RE |
| D | 1RD | 0LA |
| E | 0RB | 0RF |
| F | 0RA | --- |

## What it does (observed)

With a = `110`, the visits of the head (A, reading 0) to the left end:

    6,250,987      A>0 a^7 1 0 1 0 a^1080 1
    32,338,359     A>0 a 1 0 1 0 a^2457 1
    73,227,424     A>0 a^3 1 0 1 0 a^3690 1
    373,255,331    A>0 a^8325 1
    841,543,081    A>0 a 1 0 1 0 a^12492 1
    4,268,612,169  A>0 a 1 0 a^2 1 0 a^28122 1

N grows by 1.5 (or 1.5^2 when a visit is skipped): a **Collatz-like 3n/2 map** on the run of 110, with a short
left word (counts 1-7) that changes at each visit, as in `1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA`.

## Lean

`lean/Rules.lean` (from `py/rules.py`): eleven shift rules over 1- to 3-cell words.

## Halting

Only F1 halts. Open. n-gram CPS (widths 3..7) fails; no halt in 10^10 steps (C, `ev`). `bbtools.cycles` (K = 2, 3)
makes no jumps within 100 s.

## Notes for later

* Choose a sample inside the sweep that recurs every time (as `K(P, m)` for the 3n/2 machine above), measure the map
  for small N and each left word, check it is affine in N, and find the left words that lead to F1.

## Pages

- [`pages/holdouts/1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---/explainer.html`](../../pages/holdouts/1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---/explainer.html)
- [`pages/holdouts/1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---/proof-status.html`](../../pages/holdouts/1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC`](../1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/README.md): rename A→C, B→A, C→B, D→F, E→D, F→E; it is this table started in state B
- [`1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---`](../1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
