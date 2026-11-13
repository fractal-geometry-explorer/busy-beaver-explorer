# 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---

bbchallenge id 178401, group G10 (one side grows like √t, the other like a smaller power). Family: **bouncer with a sorted list of blocks 1^(6j+1)**. Halting from blank tape: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0RE |
| C | 1LD | 1LC |
| D | 1RA | 0LB |
| E | 0RD | 0RF |
| F | 0RD | --- |

## What it does

Left of the start the tape is `(110 10 10 10)` repeated (tokens `b a^3` with `b=110, a=10`), the background of a bouncer growing like √t.

Right of it, on the slow side (395 cells right of the start after 10^9 steps, exponent about 0.16), the tape is a list of blocks of 1s separated by `00`. The settled blocks have lengths 6j + 1 and are sorted: `… 1^25 0^2 1^25 0^2 1^29 0^2 1^31 0^2 … 1^31 0^2 1^35 0^2 1^37 … 1^41 0^2 1^43 … 1^47 0^2 1^49 0^2 1^49 0^2 1^9 0^2 1 0^2 1 0^2 1^59 0 1 0^2 1^5 0^2 1^11 0^2 1^2 B>0` (step 246,254,433). Blocks of length 6j + 5 (29, 35, 41, 47, 53) sit at the boundaries between groups, and the last few blocks near the right end are in the middle of being rewritten.

Over time the groups move up: near the right end the 1^25 group is gone by step 6·10^8 and the visible list runs from 1^31 to 1^63 at 9.5·10^8. It looks like a sorted counter whose digits are block lengths, incremented by 6 when a wave passes; we have not written its rule.

## Halting

F reading 1 halts. The 5-cell closed language allows that with `0011x` on the left and any right window starting with 1.

Closed tape language with 5-cell windows (`python3 -m bbtools.ctl M 5`, trusted Python check): a halt (F reading 1) needs `00110` or `00111` to the left; any right side starting with 1.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- `lean/Sweeps.lean`: 8 shift rules, kernel-checked: A crosses `110101010` rightward writing `001111111`, C crosses it leftward writing `111011101` (eight proved rules over its rotations) (`sweep_rA_110101010`, `sweep_rB_110101010`, `sweep_lC_110101010_1`, `sweep_rA_101010110`, `sweep_lD_101010110_1`, `sweep_rA_011010101`, `sweep_lC_011010101_0`, `sweep_rD_011010101`). Found by trying every state and direction on one copy of each background word with `bbtools.symtm` (`_one_copy_right`, `_one_copy_left`), then `symtm.prove`.

Everything else here is observation of the run (heuristic) or a trusted computation, as marked in `status.json`. Nothing proved here decides halting.

## Evidence and how to reproduce

```sh
./tmrun 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD--- 1000000000 records 100000      # tapes at each new cell
./tokrun 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD--- 1000000000 a=10,b=110 L 100000 # the tape as words at the left end (R for the right)
python3 -m bbtools.ctl 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD--- 5                # (from tools/py) the closed language and its halts
```

## For later

Write the rule of one visit of the head to the right wall on the block list, check it against the run, and compare with 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF, which agrees with this machine on the first records and then diverges.

## First look

Growth class **power/sqrt** (left: sqrt, exponent 0.503; right: power,
exponent 0.162). After 1,000,000,000 steps: 37,151 cells visited (26,993 left of the
start, 395 right), 22,314 ones.

- left, step 918,328,167: `B>0 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 `
- left, step 934,001,783: `B>0 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 `
- right, step 756,097,861: `1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 `
- right, step 948,962,626: `1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 `

## Pages

- [`pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---/explainer.html`](../../pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---/lean/check.sh
```
