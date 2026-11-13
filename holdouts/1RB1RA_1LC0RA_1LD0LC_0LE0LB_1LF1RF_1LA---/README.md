# 1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---

bbchallenge id 25733, group G10 (one side grows like √t, the other like a smaller power). Family: **bouncer over a 10 background with a defect gas**. Halting from blank tape: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RA |
| C | 1LD | 0LC |
| D | 0LE | 0LB |
| E | 1LF | 1RF |
| F | 1LA | --- |

## What it does

Again a `10` background swept by a bouncer (√t growth on the right; the passes shift the background by one cell, proved shift rules).

The left end grows slowly (exponent about 0.24). Remarkably, at every new left record from step 6.8·10^8 to 9.5·10^8 the 40 outermost runs are identical: `. 1 . 1 _4 1 . 1 . 2 . 1 . 1 . 2 . 1 . 2 . 1 . 1 . 2 . 1 : 1 . 1 . 1 . 1 . 2 . 1`. The wall pattern is frozen and the growth comes from defects (`00`, `11`, `0000`) further in, which change from sweep to sweep: e.g. `C>0 0^4 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0^2 1 0 1 …` at step 12,739.

## Halting

F reading 1 halts; in the 5-cell closed language only with `11010`/`11011` to the right.

Closed tape language with 5-cell windows (`python3 -m bbtools.ctl M 5`, trusted Python check): a halt (F reading 1) needs `11010` or `11011` to the right; any left side.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- `lean/Sweeps.lean`: 8 shift rules, kernel-checked: B and A shift `10`↔`01` rightward; B, C and D cross leftward unchanged (`sweep_rB_10`, `sweep_rA_01`, `sweep_rB_1010`, `sweep_lC_1010_1`, `sweep_lD_1010_1`, `sweep_rA_0101`, `sweep_lB_0101_0`, `sweep_lC_0101_0`). Found by trying every state and direction on one copy of each background word with `bbtools.symtm` (`_one_copy_right`, `_one_copy_left`), then `symtm.prove`.

Everything else here is observation of the run (heuristic) or a trusted computation, as marked in `status.json`. Nothing proved here decides halting.

## Evidence and how to reproduce

```sh
./tmrun 1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA--- 1000000000 records 100000      # tapes at each new cell
./tokrun 1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA--- 1000000000 a=10,b=110 L 100000 # the tape as words at the left end (R for the right)
python3 -m bbtools.ctl 1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA--- 5                # (from tools/py) the closed language and its halts
```

## For later

Find why the outermost wall pattern is frozen: it suggests the left wall is a fixed gadget that is pushed out by one period when a defect arrives.

## First look

Growth class **power/sqrt** (left: power, exponent 0.244; right: sqrt,
exponent 0.516). After 1,000,000,000 steps: 36,150 cells visited (2,956 left of the
start, 23,839 right), 18,189 ones.

- left, step 946,977,913: `C>0 0^4 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0^2 1 0 1 0 1 0 1 0 1^2 0 1 0^2 1 0 1 0^4 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0^2 1 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0^2 1 0 1 0^4 1 0 1 0^4 1 0 1 0^2 1 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 `
- left, step 997,868,940: `C>0 0^2 1 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0^2 1 0 1 0^4 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0^2 1 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0^2 1 0 1 0^4 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0^4 1 0 1 0^4 1 0 1 0^4 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 `
- right, step 970,811,908: `1^4 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0^2 1 0 1 0 1^2 0 1 0 1 0 1 0^2 1 0 1^4 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0^2 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0^2 1 0 1^4 0 1 0 1^4 0 1 0 1 0^2 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1^`
- right, step 986,443,316: `1^4 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0^2 1 0 1 0 1^2 0 1 0 1 0 1 0^2 1 0 1^4 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0^2 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0^2 1 0 1^4 0 1 0 1^4 0 1 0 1 0^2 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1^`

## Pages

- [`pages/holdouts/1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF`](../1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF/README.md): rename A→F, B→A, C→B, D→C, E→D, F→E and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
