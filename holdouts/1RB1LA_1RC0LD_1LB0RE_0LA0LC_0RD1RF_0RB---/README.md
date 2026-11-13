# 1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---

bbchallenge id 162730, a BB(6) holdout (group G06). **Family: nested multi-level counter on a `110` background (not
decoded).**

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 1RC | 0LD |
| C | 1LB | 0RE |
| D | 0LA | 0LC |
| E | 0RD | 1RF |
| F | 0RB | --- |

## What it does

With t = `110` and the defect D = `0 t^2 1 0 1 0`, the tape is a list of units `t^s D` followed by a reservoir
`t^R 1 1` at the right end.

* **Level 1:** every four sweeps one unit `t^13 D` is added at the left of the active region and the reservoir loses
  six t (1, 1, 3, 1).
  Exactly (`py/level1.py`, direct simulation for n <= 8, r <= 12): with U = `t^13 0 t^2 1 0 1 0` and the left end
  P = `1 0 t 1 0 1 0`, the tape `P U^n t^(r+6) E>` becomes `P U^(n+1) t^r E>` in 972n + 48r + 1014 steps (14 new
  cells on the left, 18 on the right); first at step 6,335 with n = 2, r = 5. Not proved: symtm does not find the
  rule, since a sweep does not cross a unit as a single shift.
* **Higher levels:** when the reservoir is empty, the head eats into the unit to its right and the process restarts
  with longer units: sizes 13, 51, 241, 1191 so far. By step 10⁹ a second background u = `100` appears right of the
  head, in blocks `u^1194 1 0` turned one by one into units `t^1191 D`; the left levels stand still.

| step | tape |
|---|---|
| 12,100 | `0 t^10 D [t^13 D]x3 1^2 >1` |
| 5,089,773 | `1 0 t 1 0 1 0 [t^13 D]x10 t^31 D [t^51 D]x2 t^676 D t^350 1^2 >1` |
| 87,391,760 | `... [t^13 D]x80 t^44 D [t^51 D]x68 t^141 D t^241 D t^241 0 t^2 1 0 1 >1` |
| 10⁹ | `... [t^51 D]x43 ... [t^241 D]x15 t^48 1 t^941 D [t^1191 D]x3 1 >t 0 u^1192 1 0 u^1194 1 0 u^1194 1 0 u^1194 1 0 u^6784 1` |
| 2·10⁹ | `... [t^241 D]x2 t^119 0 t^588 D [t^1191 D]x20 t^391 >0^2 u^357 1` |

## Status

Open, not reduced. No halt to 2·10¹⁰ steps (`c/reservoir.c`, width 333,559); Lean (`lean/Blank.lean`): no halt in
10⁷ steps.

## For later

* Level 1 as a symtm rule (one unit added, six t spent), then the transition between levels: how a unit of size s
  becomes the reservoir and the next unit size (13 -> 51 -> 241 -> 1191) and count are produced, and whether that
  transition can reach F reading 1. A run-length (macro) simulator over t, u and D would show many more levels.

## Pages

- [`pages/holdouts/1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---/explainer.html`](../../pages/holdouts/1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---/explainer.html)
- [`pages/holdouts/1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---/proof-status.html`](../../pages/holdouts/1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---/lean/check.sh
gcc -O2 -o reservoir holdouts/1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---/c/reservoir.c && ./reservoir 20000000000
python3 holdouts/1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---/py/level1.py
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---`](../1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F; it is this table started in state B
- [`1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB---`](../1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB---/README.md): rename A→E, B→B, C→A, D→D, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
