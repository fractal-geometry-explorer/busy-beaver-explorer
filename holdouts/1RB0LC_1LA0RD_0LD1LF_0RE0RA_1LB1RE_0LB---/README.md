# 1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB---

bbchallenge id 126204.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 0RD |
| C | 0LD | 1LF |
| D | 0RE | 0RA |
| E | 1LB | 1RE |
| F | 0LB | --- |

## Status

**Open.** The macro structure below is read off long runs (heuristic: not yet stated as rules or proved); no
decision. Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## What it does

Near the left end the tape is a stack of segments `(011)^k`, separated by the marker `(01)^3 10110` (with variants
`(101)^j 010110110`). Watching the left-end visits: in one phase the head converts the first segment into `(110)`
words, three for each `(011)` it removes (`(110)^1050 (011)^842` → `(110)^1459 1^3 (011)^705` → `(110)^1869
(011)^569`: +409, −136.5 per visit); in the other phase the first segment counts down by 4 per visit while the next
one counts up. Each layer is built from the one before it by a factor of about 3 (segments of 13, then 44 and 51,
later 646 and 1115), which is a ternary counter-like hierarchy. The halt is F1.

## For later

State the two phases as rules with the segment lengths as parameters, and the layer-to-layer map; if it is a
clean ×3 recursion, nonhalting may follow by induction on the layer.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.451; right: fixed,
exponent 1.091). After 1,000,000,000 steps: 62,238 cells visited (44,792 left of the
start, 5,553 right), 34,910 ones.

- left, step 970,392,602: `C>0 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 `
- left, step 986,140,655: `C>0 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 `

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 6.32x10^13 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.09x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 925 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB--- 400
```

## Pages

- [`pages/holdouts/1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB---/explainer.html`](../../pages/holdouts/1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB---/explainer.html)
- [`pages/holdouts/1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB---/proof-status.html`](../../pages/holdouts/1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LA0RD_0LD1LF_0RE0RA_1LB1RE_0LB---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---`](../1RB0LC_1LA0RE_0LD0LB_1RA1LD_0RC1RF_0RA---/README.md): rename A→B, B→A, C→E, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---`](../1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---/README.md): rename A→C, B→B, C→E, D→D, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror

<!-- end of related machines -->
