# 1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD

bbchallenge id 78071. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly). Analysed by hand from the generated folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1RC | --- |
| C | 1LD | 1LC |
| D | 1RE | 0LC |
| E | 1RF | 0RE |
| F | 1RA | 0RD |

## What it does

The background is the pair `10`; the leftward sweep over it is a proved shift rule. Short walls split it into
domains. The right end at step 397,048,236 (width 23,150):

```
10 (01)^14 0 (01)^5316 0 (01)^4 0 (01)^8 0 (01)^1315 (10)^12 (01)^1312 0 (01)^6 0 (01)^18 0000 (10)^655 1 (10)^8
(01)^44 (10)^347 (01)^16 0 (01)^36 (10)^10 1 (10)^159 (01)^42 0000 (10)^124 000 (10)^51 1 (10)^77 ...
```

The domain lengths near the left end nearly halve (5316, 1315, 1312, 655, 347, 159, ... pairs here; 16674, 4137,
4135, 2065, 1065, 501 cells at 2·10^9 steps), like the digits of a binary counter. `1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF`
(same batch) looks similar.

## Halting

B1 is the only halting transition, reached as `A>0 1`. It cannot happen inside a domain; whether a wall ever
produces it is open.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (from `py/rules.py`, kernel): the leftward sweep over `10` in both phases (`d_left`, `c_left`).
- Computed (`tools/c/triage.c`): no halt in 10^9 steps.

Everything else on this page is heuristic: read off runs of up to 2·10^9 steps (`tools/c/tokrun.c`), not proved.

## For later

- Classify the wall types and write a sweep across each as a rule; the halving suggests a counter whose digits are
  the domains, and the carry would be the rule to find.

## Reproduce

```sh
python3 holdouts/1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD/py/rules.py | diff - holdouts/1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD/lean/Rules.lean   # the rules file is current
gcc -O2 -o tokrun tools/c/tokrun.c
./tokrun 1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD 400000000 x=0 LR 2000 | tail -4   # the tape each time the head extends it (x is a 0)
```

## Pages

- [`pages/holdouts/1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD/explainer.html`](../../pages/holdouts/1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD/explainer.html)
- [`pages/holdouts/1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD/proof-status.html`](../../pages/holdouts/1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE`](../1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE/README.md): rename A→C, B→D, C→E, D→F, E→A, F→B; it is this table started in state E

<!-- end of related machines -->
