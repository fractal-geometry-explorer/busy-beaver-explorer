# 1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB

bbchallenge id 138104, group G10 (one side grows like √t, the other like a smaller power). Family: **bouncer over a 10 background with a defect gas**. Halting from blank tape: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1LC | 0RD |
| C | 0LD | 0LB |
| D | 1RA | 0LE |
| E | 1LF | --- |
| F | 0RD | 1LB |

## What it does

Same architecture as the other `10`-background machines of this batch: a bouncer whose passes shift the background by one cell (proved shift rules), with the left end growing like √t.

The right end grows slowly (exponent about 0.16, 843 cells after 10^9 steps). Near it the tape holds defects: `000` gaps, double gaps and runs of three 1s, e.g. at step 309,148,624 the last runs are `1 : 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 _3 1 : 1 . 1 . 1 . 1 . 1 _3 1 . 2 . 1 . 1 . 1 :`. In the middle of the tape groups such as `1^3 0^4` and `1^3 0 1 0 1 0^2` recur, but not periodically.

## Halting

E reading 1 halts; in the 5-cell closed language only with `10010`/`10011` to the right.

Closed tape language with 5-cell windows (`python3 -m bbtools.ctl M 5`, trusted Python check): a halt (E reading 1) needs `10010` or `10011` to the right; any left side.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- `lean/Sweeps.lean`: 8 shift rules, kernel-checked: A, B and D shift `1010`↔`0101` rightward, B and C cross the background leftward unchanged (`sweep_lC_10_1`, `sweep_lB_01_0`, `sweep_rA_1010`, `sweep_rB_1010`, `sweep_lC_1010_1`, `sweep_rA_0101`, `sweep_lB_0101_0`, `sweep_rD_0101`). Found by trying every state and direction on one copy of each background word with `bbtools.symtm` (`_one_copy_right`, `_one_copy_left`), then `symtm.prove`.

Everything else here is observation of the run (heuristic) or a trusted computation, as marked in `status.json`. Nothing proved here decides halting.

## Evidence and how to reproduce

```sh
./tmrun 1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB 1000000000 records 100000      # tapes at each new cell
./tokrun 1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB 1000000000 a=10,b=110 L 100000 # the tape as words at the left end (R for the right)
python3 -m bbtools.ctl 1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB 5                # (from tools/py) the closed language and its halts
```

## For later

Track the defect list at the right wall from one visit to the next and try to find the rule of one visit.

## First look

Growth class **power/sqrt** (left: sqrt, exponent 0.508; right: power,
exponent 0.162). After 1,000,000,000 steps: 40,191 cells visited (28,639 left of the
start, 843 right), 20,094 ones.

- left, step 970,195,282: `C>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- left, step 985,905,846: `C>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 962,655,678: `1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 984,726,167: `1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB/explainer.html`](../../pages/holdouts/1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB/explainer.html)
- [`pages/holdouts/1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB/proof-status.html`](../../pages/holdouts/1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RD1LB/lean/check.sh
```
