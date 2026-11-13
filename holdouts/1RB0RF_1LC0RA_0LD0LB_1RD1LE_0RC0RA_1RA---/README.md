# 1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---

bbchallenge id 118323, group G10 (one side grows like √t, the other like a smaller power). Family: **bouncer over a 10 background with a defect gas**. Halting from blank tape: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 1LC | 0RA |
| C | 0LD | 0LB |
| D | 1RD | 1LE |
| E | 0RC | 0RA |
| F | 1RA | --- |

## What it does

The tape is nearly all `10`. Every pass shifts the background by one cell (six proved shift rules in both phases). The right end grows like t^0.6 (88,047 cells after 10^9 steps), faster than a plain √t bouncer: most passes do not reach the left end at all.

The left end is reached rarely and moves only 153 cells in 10^9 steps; at those visits the left edge reads `: 1 : 1 . 1 . 1 …` or `. 1 . 1 …` (a double gap or none), and isolated defects (`00`, `11`, `000`) sit in the background, e.g. `… 1 0^2 1 0 1 0^2 1 0 1 … 1 0^3 1 0^2 1 0 1 …` near the right end at step 9,264.

So the head turns somewhere inside the tape most of the time; the turning points are set by the defects. We have not found the rule that decides where a pass turns.

## Halting

F reading 1 halts; in the 5-cell closed language with `0101x`/`01001` on the left and `10…` on the right.

Closed tape language with 5-cell windows (`python3 -m bbtools.ctl M 5`, trusted Python check): a halt (F reading 1) needs `01001`, `0101x` or `01010` to the left and a right side starting `10`.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- `lean/Sweeps.lean`: 12 shift rules, kernel-checked: A, B and F shift `10`↔`01` rightward; B and C cross leftward unchanged (`sweep_rA_10`, `sweep_rB_10`, `sweep_lC_10_1`, `sweep_rA_01`, `sweep_lB_01_0`, `sweep_rF_01`, `sweep_rA_1010`, `sweep_rB_1010`, `sweep_lC_1010_1`, `sweep_rA_0101`, `sweep_lB_0101_0`, `sweep_rF_0101`). Found by trying every state and direction on one copy of each background word with `bbtools.symtm` (`_one_copy_right`, `_one_copy_left`), then `symtm.prove`.

Everything else here is observation of the run (heuristic) or a trusted computation, as marked in `status.json`. Nothing proved here decides halting.

## Evidence and how to reproduce

```sh
./tmrun 1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA--- 1000000000 records 100000      # tapes at each new cell
./tokrun 1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA--- 1000000000 a=10,b=110 L 100000 # the tape as words at the left end (R for the right)
python3 -m bbtools.ctl 1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA--- 5                # (from tools/py) the closed language and its halts
```

## For later

Record the turning points of the passes and the defect positions; the t^0.6 growth suggests passes of geometrically distributed length.

## First look

Growth class **power/sqrt** (left: power, exponent 0.254; right: sqrt,
exponent 0.607). After 1,000,000,000 steps: 143,859 cells visited (153 left of the
start, 88,047 right), 71,897 ones.

- left, step 715,326,200: `E>0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 731,186,900: `D>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 969,513,405: `1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 985,172,593: `1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---/explainer.html`](../../pages/holdouts/1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---/explainer.html)
- [`pages/holdouts/1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---/proof-status.html`](../../pages/holdouts/1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_0RC0RA_1LC1RD_0LB0LE_1LA0LF_1LE---`](../1RB0LE_0RC0RA_1LC1RD_0LB0LE_1LA0LF_1LE---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB---_1RC0RA_1LD0RB_0LE0LC_1RE1LF_0RD0RB`](../1RB---_1RC0RA_1LD0RB_0LE0LC_1RE1LF_0RD0RB/README.md): rename A→B, B→C, C→D, D→E, E→F, F→A; it is this table started in state F

<!-- end of related machines -->
