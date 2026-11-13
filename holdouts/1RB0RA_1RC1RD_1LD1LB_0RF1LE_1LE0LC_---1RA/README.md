# 1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA

bbchallenge id 60575. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly). Analysed by hand from the generated folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1RC | 1RD |
| C | 1LD | 1LB |
| D | 0RF | 1LE |
| E | 1LE | 0LC |
| F | --- | 1RA |

## What it does

The left part of the tape is domains of the pairs `01` (written `(0111)^m` after a rightward sweep) separated by
short defects `(10)^4 111`; the right part is a period-10 comb and a periodic tail. Two end turns:

```
step 110,994,700  right end  (0111)^50 010110100110 111 01 (0110111010)^1399 0 (1101)^3 00 (1101)^3 0110 111 0100 (1101)^3 0110 ...
step 142,116,130  left end   0 (01)^103 1 (10)^4 111 (01)^4480 1010 111 (01)^342 (10)^4 111 (01)^1050 (10)^4 111
                             (01)^120 (10)^4 111 (01)^52 (10)^4 111 01 (1010111010)^221 1011010 111 (01)^6 (10)^4 111 ...
```

The domains are few and uneven (at step 1,041,927,495: 3312, 168, 11072, 176, 50; the comb has 891 copies). The
leftward sweeps over all three backgrounds are proved shift rules.

## Halting

F0 is the only halting transition, reached as `D>0 0`. It cannot happen inside a domain or the comb; whether a
defect or the tail ever produces it is open.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (from `py/rules.py`, kernel): the four leftward sweep rules (`e_left4`, `e_left2`, `c_left2`, `e_left10`).
- Computed (`tools/c/triage.c`): no halt in 10^9 steps.

Everything else on this page is heuristic: read off runs of up to 2·10^9 steps (`tools/c/tokrun.c`), not proved.

## For later

- Prove the rightward sweeps too, then write each defect type as a rule for a full sweep; the domain lengths would
  then become a small dynamical system to iterate.

## Reproduce

```sh
python3 holdouts/1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA/py/rules.py | diff - holdouts/1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA/lean/Rules.lean   # the rules file is current
gcc -O2 -o tokrun tools/c/tokrun.c
./tokrun 1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA 400000000 x=0 LR 2000 | tail -4   # the tape each time the head extends it (x is a 0)
```

## Pages

- [`pages/holdouts/1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA/explainer.html`](../../pages/holdouts/1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA/explainer.html)
- [`pages/holdouts/1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA/proof-status.html`](../../pages/holdouts/1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA/lean/check.sh
```
