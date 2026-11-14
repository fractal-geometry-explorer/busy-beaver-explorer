# 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF

bbchallenge id 50436, group G10 (one side grows like √t, the other like a smaller power). Family: **bouncer with a sorted list of blocks 1^(6j+1)**. Halting from blank tape: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1RC | 0RF |
| C | 0LD | --- |
| D | 1LE | 1LD |
| E | 1RA | 0LB |
| F | 0RE | 0RF |

## What it does

Left of the start: `(110 10 10 10)` repeated, a √t bouncer (proved shift rules). Right of it, on the slow side (394 cells after 10^9 steps), a list of blocks of 1s separated by `00` whose settled lengths are 6j + 1, sorted, with 6j + 5 blocks at group boundaries, e.g. at step 945,073,674: `41 : 43 : 43 : 43 : 43 : 43 : 43 : 43 : 43 : 43 : 7 : 1 : 47 : 49 : 49 : 11 : 1 : 53 : 55 : 59 : 5 : 1 : 1 : 3 : 1` (run lengths, `:` = 00).

The first records coincide with those of 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD--- (same block lists, different step counts: the two machines share the mechanism with different costs per pass); after a while the two runs diverge but keep the same structure.

## Halting

C reading 1 halts. The 5-cell closed language allows that with `11100`/`11111` on the left and any right window starting with 1.

Closed tape language with 5-cell windows (`python3 -m bbtools.ctl M 5`, trusted Python check): a halt (C reading 1) needs `11100` or `11111` to the left; any right side starting with 1.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- `lean/Sweeps.lean`: 8 shift rules, kernel-checked: A crosses `110101010` rightward writing `001111111`, D crosses it leftward writing `111011101` (eight proved rules over its rotations) (`sweep_rA_110101010`, `sweep_rB_110101010`, `sweep_lD_110101010_1`, `sweep_rA_101010110`, `sweep_lE_101010110_1`, `sweep_rA_011010101`, `sweep_lD_011010101_0`, `sweep_rE_011010101`). Found by trying every state and direction on one copy of each background word with `bbtools.symtm` (`_one_copy_right`, `_one_copy_left`), then `symtm.prove`.

Everything else here is observation of the run (heuristic) or a trusted computation, as marked in `status.json`. Nothing proved here decides halting.

## Evidence and how to reproduce

```sh
./tmrun 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF 1000000000 records 100000      # tapes at each new cell
./tokrun 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF 1000000000 a=10,b=110 L 100000 # the tape as words at the left end (R for the right)
python3 -m bbtools.ctl 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF 5                # (from tools/py) the closed language and its halts
```

## For later

As for the twin: the rule of one wall visit on the block list.

## First look

Growth class **power/sqrt** (left: sqrt, exponent 0.506; right: power,
exponent 0.15). After 1,000,000,000 steps: 32,838 cells visited (23,688 left of the
start, 394 right), 25,123 ones.

- left, step 939,617,740: `B>0 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 `
- left, step 991,180,601: `E>0 1^2 0 1 0^2 1^2 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 `
- right, step 759,411,477: `1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 `
- right, step 945,073,674: `1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 `

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 8.29x10^13 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.01x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 7,944 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF 400
```

## Pages

- [`pages/holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/explainer.html`](../../pages/holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/explainer.html)
- [`pages/holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/proof-status.html`](../../pages/holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF`](../1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B
- [`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF`](../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF`](../1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---`](../1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---/README.md): 8,004,077 configurations, the last at step 10,000,000 here and step 8,004,076 there
- [`1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---`](../1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---/README.md): 8,004,077 configurations, the last at step 10,000,000 here and step 8,004,076 there

<!-- end of related machines -->
