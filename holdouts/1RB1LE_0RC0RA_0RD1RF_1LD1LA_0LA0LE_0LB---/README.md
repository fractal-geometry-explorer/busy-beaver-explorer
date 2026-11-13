# 1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---

bbchallenge id 103399. Every sweep rewrites the tape between two codes: at the left end the numbers are long runs of 0s between short groups of 1s, at the right end they are long runs of 1s between short groups of 0s; the numbers look irregular.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 0RC | 0RA |
| C | 0RD | 1RF |
| D | 1LD | 1LA |
| E | 0LA | 0LE |
| F | 0LB | --- |

## What it does

The right side grows like √t, the left like t^0.15. Every sweep rewrites the tape between two forms. With the
head at the left end, long runs of 0s (up to 52) sit between short groups of 1s (runs of 1s at most 7):

    step 832,384,202:  A>0 0 1 0 1^3 (01)^4 1^6 0^9 (10)^3 1^3 (01)^3 (11010101)^2 1 0^8 1010 1^3 0^8 (10)^3 11 0^4 …

With the head at the right end it is the other way round: long runs of 1s (up to 46) between `00` or `0 (01)^k`
(runs of 0s at most 2):

    step 996,208,311:  1^12 00 1^23 00 1^8 0 (01)^6 1^14 0 (01)^8 1^11 0 (01)^12 1^9 0 (01)^9 1^9 …

So the tape is a list of numbers that each sweep translates between the two codes; the shift rules proved in
`lean/Rules.lean` show the sweeps flipping the phase of the `10`/`01` blocks as they cross them. The numbers show
no order that has been found.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the shift rules by which the sweeps cross `(10)^n` and `(01)^n` blocks (states A, B, E), each one flipping the phase of the block (`shift_l_A_10`, `shift_r_B_10`, `shift_l_E_01`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The two forms are measured; the sweep map is not known. Halting needs C reading 1 with a 1
to its right.

## For later

More than a day. Next: (1) write both forms as lists of numbers (lengths of the long runs and the short groups
between them) and look for the transducer between them; (2) check whether the groups `(10)^3 1 1`,
`(10)^3 1^3 (01)^3 1` are a finite alphabet, which would make the sweep a rewriting of words.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---/lean/check.sh
python3 holdouts/1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 0 under the head, 1 right, 1 two right.

## Pages

- [`pages/holdouts/1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---/explainer.html`](../../pages/holdouts/1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---/explainer.html)
- [`pages/holdouts/1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---/proof-status.html`](../../pages/holdouts/1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---/proof-status.html)
