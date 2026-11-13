# 1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---

bbchallenge id 76238. One of the six-state holdouts. Analyzed by hand (group G02), partly.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LA | 0RD |
| C | 1LB | 1LF |
| D | 1LE | 1RE |
| E | 0LA | 0RB |
| F | 0LB | --- |

## What it does (observed)

The left side is two big blocks of ones and a short tail (`B>0 1^37710 0 1^7702 0 1^138` at 10^9 steps); right of
the start ~77 cells. Each cycle moves 6 three-cell words out of one block and 8 into the other, so each regime is
about 4/3 as long as the last (cycles per regime: 3, 7, 10, 14, 18, 23, ..., 1344830, 1793083, 2390779, 3187809,
4250412, 5667216). A **Collatz-like 4n/3 map**. The small blocks between regimes (13, 24, 45, 192, 459, 597, 784,
1893 words) are the same as in `1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---`; the two machines look like
implementations of the same map.

## Lean

`lean/Cycles.lean` (from `py/cycles_rules.py`, `bbtools.cycles` with blocks of 3 cells): the 40 one-cycle rules
applied on the run to 10^15 steps, each for all values of its variables. About 2 minutes to check.

## Halting

Only F1 halts. `python3 -m bbtools.cycles M 3 1e40`: 146 jumps, 78 rules, no halt by 10^40 steps. n-gram CPS
(widths 3..7) fails. Open.

## Notes for later

* Extract the end-of-regime map (tail word, n mod 3) as for the 3n/2 machine `1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA`,
  and check the conjectured equivalence with `1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---` sample by sample.
* The sister machine `1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---` (same A, B, D rows) is a 3n/2 map instead.

## Pages

- [`pages/holdouts/1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---/explainer.html`](../../pages/holdouts/1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---/explainer.html)
- [`pages/holdouts/1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---/proof-status.html`](../../pages/holdouts/1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---`](../1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---/README.md): rename A→C, B→B, C→A, D→D, E→E, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---`](../1RB1LB_0RC0LD_1LD1RE_1RC0LA_1RD1RF_0RD---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
