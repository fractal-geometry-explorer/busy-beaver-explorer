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
