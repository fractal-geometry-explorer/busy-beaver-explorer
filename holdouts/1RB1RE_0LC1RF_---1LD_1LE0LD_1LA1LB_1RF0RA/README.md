# 1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA

bbchallenge id 154700. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly). Analysed by hand from the generated folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 0LC | 1RF |
| C | --- | 1LD |
| D | 1LE | 0LD |
| E | 1LA | 1LB |
| F | 1RF | 0RA |

## What it does

Two end turns:

```
step 223,660,819  right end  (10)^4 1 (10)^6 111 (01)^4 (10)^6 111 (01)^4 (10)^6 ... 111 0101 (1010101110)^160 10110
                             111 (01)^4 (10)^52 111 (01)^4 (10)^122 111 0101 (10)^1050 111 (01)^4 (10)^3092 111 0101 (10)^4840 0
step 353,376,315  left end   010 111 0110 (1011)^3 0010 111 0110 (1011)^3 0010 ... 00 (1011)^3 (0010111011)^2319 10110010110 (1011)^820 10
```

The left part repeats a word of about 20 cells, then comes a period-10 comb, then long domains of `10` separated by
`111 0101` or `111 (01)^4`. The domains grow fast and split (142, 2512, 12108, 282, 286 pairs at step
1,036,291,430). The rightward sweeps over `10` and `1011` are proved shift rules.

## Halting

C0 is the only halting transition, reached as `0 B>0`. It never happens inside a domain; whether a defect ever
produces it is open.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (from `py/rules.py`, kernel): the three rightward sweep rules (`a_right4`, `a_right2`, `e_right2`).
- Computed (`tools/c/triage.c`): no halt in 10^9 steps.

Everything else on this page is heuristic: read off runs of up to 2·10^9 steps (`tools/c/tokrun.c`), not proved.

## For later

- Prove the leftward sweeps, then write a sweep across each defect type as a rule, and follow the domain lengths
  as a dynamical system.

## Reproduce

```sh
python3 holdouts/1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA/py/rules.py | diff - holdouts/1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA/lean/Rules.lean   # the rules file is current
gcc -O2 -o tokrun tools/c/tokrun.c
./tokrun 1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA 400000000 x=0 LR 2000 | tail -4   # the tape each time the head extends it (x is a 0)
```

## Pages

- [`pages/holdouts/1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA/explainer.html`](../../pages/holdouts/1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA/explainer.html)
- [`pages/holdouts/1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA/proof-status.html`](../../pages/holdouts/1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA`](../1RB0RA_1RC1RD_1LD1LB_0RF1LE_1LE0LC_---1RA/README.md): rename A→C, B→D, C→F, D→A, E→B, F→E and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
