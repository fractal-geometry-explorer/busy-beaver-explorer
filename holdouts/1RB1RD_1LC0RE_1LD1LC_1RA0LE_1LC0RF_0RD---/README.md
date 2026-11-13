# 1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---

bbchallenge id 139727. A bouncer on the left; on the right a list of runs of 1s separated by 00 whose lengths are 13, 19, 25, 31, ... (13 + 6i), sorted, with multiplicities that fall off from one length to the next (616, 188, 121, 37, 22, 7, 4, 1 at 10^9 steps).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0RE |
| C | 1LD | 1LC |
| D | 1RA | 0LE |
| E | 1LC | 0RF |
| F | 0RD | --- |

## What it does

The left side grows like √t (a bouncer); the right side like t^0.16. At the last right extension before 10⁹
steps (step 948,962,681) the tape reads

    (100)^3061 1^5 (001111111)^932 1100 1^13 00 1^13 00 … (616 runs of 1^13) … 1^19 00 … (188 runs) …
    1^25 … (121) … 1^31 … (37) … 1^37 … (22) … 1^43 … (7) … 1^49 … (4) … 1^53 00 1^17 00 1^59 00 1^63 00 …

The right part is a **sorted list of runs of 1s**, separated by `00`, of lengths 13, 19, 25, 31, 37, 43, 49, …
(13 + 6i), with multiplicities 616, 188, 121, 37, 22, 7, 4, 1, 1, 1 that fall off from each length to the next.
A few short runs (7, 13, 17, 21, 27, 35, 40, 47) sit between the groups: places where a run is being rebuilt. Over
time new, longer runs appear at the right end (the longest was 59 at step 7.6·10⁸, 63 at 9.5·10⁸).

In plain words: a counter whose digits are runs of 1s, sorted by size, with a bouncer on the left feeding it.

The machine 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD--- (another batch) has the same run: the two differ in D1 and
E0, and their tapes agree whenever the head is not in that spot.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the shift rules: D crosses `(01)^n` rightward turning it into `(11)^n`, C crosses a run of 1s leftward (`shift_r_D_01`, `shift_l_C_1`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The sorted list and its counter-like growth are measured. Halting needs E reading 1 with a 1
to its right. The same run, up to the moments the head is where the tables differ, is
1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD--- in another batch: a proof for one should carry over.

## For later

More than a day. Next: (1) watch how a new run is made at the right end and how runs grow from 13 + 6i to
19 + 6i (a carry); (2) write the list as multiplicities (m0, m1, …) of the lengths 13 + 6i and find the map per
left visit; (3) share with the batch that has 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---/lean/check.sh
python3 holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Pages

- [`pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---/explainer.html`](../../pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same run as [`1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---`](../1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---/README.md) (observed, not proved).** At every one of the first 10^7 steps from blank tape the two machines have the same tape and the head on the same cell. Their tables differ, and no renaming of the states turns one into the other. While they run, the states pair up as A–A, B–B, C–C, D–D, E–B, E–E, F–E, F–F (this machine first), which is not one to one. Transitions not used in these steps: this machine never uses F1 and the other never uses F1. Lean proves (`lean/Twin.lean` in the other machine's folder, `lock_or_break`, `not_halts_of_noBreak`) that the two runs have the same tape, the same head position and paired states up to the first break, a configuration where the paired states act differently, and that neither machine halts if no break ever comes. A halt of either machine is itself a break, and the halting transitions of the two do not correspond, so the two are not known to halt together.

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA---`](../1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA---/README.md): rename A→B, B→C, C→D, D→A, E→E, F→F; it is this table started in state D
- [`1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---`](../1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF`](../1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/README.md): 8,004,077 configurations, the last at step 8,004,076 here and step 10,000,000 there

<!-- end of related machines -->
