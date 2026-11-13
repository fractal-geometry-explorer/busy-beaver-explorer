# 1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA

bbchallenge id 100124, group G10 (one side grows like √t, the other like a smaller power). Family: **bouncer over a 11100 background, chaotic slow side**. Halting from blank tape: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 1RC | 1RD |
| C | 0LA | 0LD |
| D | 1RE | 1LC |
| E | 0RF | 0LF |
| F | --- | 0RA |

## What it does

The right part of the tape is the word `11100` repeated (right end at step 2.7·10^8: `3 : 3 : 3 : … 3 : 2 .` in run notation), growing like √t: a bouncer whose leftward passes rewrite each copy (eight proved shift rules) and whose rightward passes restore it.

The left side (3,507 cells after 10^9 steps, exponent about 0.16) is different: runs of one to six 1s with gaps of one or two 0s and no visible order, e.g. `. 3 . 1 . 1 . 1 . 1 . 1 . 1 . 1 . 2 . 1 . 1 . 1 . 1 . 2 . 1 …`. Between 5.80·10^8 and 5.80·10^8+70,000 steps the left wall advances 120 cells in a burst, and only 30 more in the next 4.5·10^7 steps: the slow side grows in bursts.

## Halting

F reading 0 halts. The 5-cell closed language puts `01110` to the left of the head; the right side is unconstrained (it allows blank tape after the head).

Closed tape language with 5-cell windows (`python3 -m bbtools.ctl M 5`, trusted Python check): a halt (F reading 0) needs `01110` to the left; the right side is unconstrained.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- `lean/Sweeps.lean`: 8 shift rules, kernel-checked: A, C and D cross rotations of `11100` leftward, rewriting them (e.g. D: `11100` → `01010`) (`sweep_lD_11100_1`, `sweep_lD_01110_1`, `sweep_lC_00111_0`, `sweep_lC_00111_1`, `sweep_lA_10011_1`, `sweep_lD_10011_1`, `sweep_lA_11001_1`, `sweep_lC_11001_1`). Found by trying every state and direction on one copy of each background word with `bbtools.symtm` (`_one_copy_right`, `_one_copy_left`), then `symtm.prove`.

Everything else here is observation of the run (heuristic) or a trusted computation, as marked in `status.json`. Nothing proved here decides halting.

## Evidence and how to reproduce

```sh
./tmrun 1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA 1000000000 records 100000      # tapes at each new cell
./tokrun 1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA 1000000000 a=10,b=110 L 100000 # the tape as words at the left end (R for the right)
python3 -m bbtools.ctl 1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA 5                # (from tools/py) the closed language and its halts
```

## For later

Look at the boundary between the 11100 region and the chaotic region: which words cross it per pass.

## First look

Growth class **power/sqrt** (left: power, exponent 0.163; right: sqrt,
exponent 0.572). After 1,000,000,000 steps: 24,723 cells visited (3,507 left of the
start, 14,986 right), 15,052 ones.

- left, step 625,962,203: `D>0 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^2 1^3 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0^2 1^4 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1 0 1 0^2 1 0 1 0 1^2 0 1 0 1 0 1^4 0 1 0 1 `
- left, step 918,317,465: `A>0 1^5 0 1 0 1^2 0 1 0 1 0 1 0 1 0^2 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1^3 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1^4 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0^2 1 0 1 0 1 0 1^5 `
- right, step 972,247,123: `1 0 1 0 1 0 1 0^2 1^3 0 1 0 1 0 1^4 0 1^8 0^2 1^3 0 1^3 0 1 0 1 0 1 0^2 1^3 0 1 0 1 0 1^4 0^2 1^3 0 1^4 0^2 1^3 0 1 0 1 0 1^2 0^2 1^3 0^2 1^3 0 1^5 0^2 1^7 0 1 0 1 0 1 0 1 0^2 1^3 0 1^4 0 1 0^2 1^3 0 1 0 1 0 1^4 0^2 1^3 0 1^7 0 1^8 0^2 1^3 0 1^4 0^2 1^3 0^2 1^6 0 1 0 1 0^2 1^3 0 1^5 0^2 1^3 0 1^3 0 `
- right, step 987,901,100: `1 0 1 0 1 0 1 0^2 1^3 0 1 0 1 0 1^4 0 1^8 0^2 1^3 0 1^3 0 1 0 1 0 1 0^2 1^3 0 1 0 1 0 1^4 0^2 1^3 0 1^4 0^2 1^3 0 1 0 1 0 1^2 0^2 1^3 0^2 1^3 0 1^5 0^2 1^7 0 1 0 1 0 1 0 1 0^2 1^3 0 1^4 0 1 0^2 1^3 0 1 0 1 0 1^4 0^2 1^3 0 1^7 0 1^8 0^2 1^3 0 1^4 0^2 1^3 0^2 1^6 0 1 0 1 0^2 1^3 0 1^5 0^2 1^3 0 1^3 0 `

## Pages

- [`pages/holdouts/1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA/explainer.html`](../../pages/holdouts/1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA/explainer.html)
- [`pages/holdouts/1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA/proof-status.html`](../../pages/holdouts/1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA/lean/check.sh
```
