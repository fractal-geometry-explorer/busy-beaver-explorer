# 1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD

bbchallenge id 167030. Like its neighbour 1RB0RF_1LC1RD in this batch, every sweep rewrites the whole tape between two codes for a list of numbers: at the right end it is runs 1^(3k+2) separated by single 0s, at the left end runs 1^(3a+1) separated by 0^(3b+2); the numbers look irregular.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1RC | 0RF |
| C | 1LD | 1RA |
| D | 1LB | 1LD |
| E | 1RC | 0RC |
| F | --- | 0LD |

## What it does

The right side grows almost linearly (t^0.89), the left like t^0.30. Every sweep rewrites the whole tape. With
the head at the right end, the tape is a list of runs of 1s separated by single 0s,

    step 911,093,030:  1^9 0110 1^8 (011)^3 1^3 (011111)^2 1^6 (011)^6 1^12 0110 1^14 …    (0110 = 0 1^2 0)

and 11,715 of its 11,717 runs have length 3k + 2. With the head at the left end, the tape is runs of 1s of length
3a + 1 separated by runs of 0s of length 3b + 2:

    step 989,746,492:  B>0 1^13 0^5 1^4 0^5 1^4 0^5 1^4 0^2 1^12 0^4 1^16 (001111)^2 1^6 …

(6,115 of 6,128 runs of 1s, 6,124 of the runs of 0s). So the tape is one list of numbers written in two codes, and
each sweep translates it: the leftward sweeps in D and B erase runs of 1s cell by cell (`shift_l_D_1`,
`shift_l_B_1`, proved). The numbers themselves show no order. The same two codes are used by
1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC in this batch.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the leftward sweeps in D and B turning a run of 1s into 0s (`shift_l_D_1`, `shift_l_B_1`) (`shift_l_D_1`, `shift_l_B_1`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The two codes are measured; the map on the list is not known, and the list looks
irregular. Halting needs B reading 1 with a 0 to its right. Same family as 1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC
in this batch (the same two codes).

## For later

More than a day. Next: (1) write the right-end tape as the list k1, k2, … (runs 1^(3k+2)) and the left-end tape
as pairs (a, b), and find the transducer that maps one to the other (a finite-state rewriting would show up as a
rule on short windows of the list); (2) compare with 1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC, which uses the
same codes.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/lean/check.sh
python3 holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Pages

- [`pages/holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/explainer.html`](../../pages/holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/explainer.html)
- [`pages/holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/proof-status.html`](../../pages/holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/proof-status.html)
