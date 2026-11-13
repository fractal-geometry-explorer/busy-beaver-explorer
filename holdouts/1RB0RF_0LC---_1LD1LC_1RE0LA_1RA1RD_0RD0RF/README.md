# 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF

bbchallenge id 117546. A bouncer of runs at growing levels: level k is a run of (6k+3)-cell words, dense 100 1^(6k) on one side of the head and sparse 011 (01)^(3k) on the other; D going right makes them dense, C going left makes them sparse, and new levels appear slowly on the right.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 0LC | --- |
| C | 1LD | 1LC |
| D | 1RE | 0LA |
| E | 1RA | 1RD |
| F | 0RD | 0RF |

## What it does

Runs of words of length 6k+3, one run per level k. Step 4·10^9 (periods of the runs, counts):

    (100)^8078 (9-cell)^662 (100)^3 (15-cell)^1624 ... (21-cell)^135 (27-cell)^323 ... (33-cell)^17 (111)^4 ...

Each level-k word is either dense `100 1^(6k)` or sparse `011 (01)^(3k)`; left of the head dense, right of it sparse.
The head bounces over the whole structure and the number of levels grows slowly (5 at 4·10^9 steps).

**Proved** (`lean/Rules.lean`): `D> (011(01)^3k)^n -> (100 1^6k)^n D>` for k = 1, 2, 3 ((6k+5)n steps);
`(0 1^(6k+1) 0)^n C> 1 -> C> 1 (011(01)^3k)^n` for k = 1, 2; the 3-cell shifts `d_c`, `d_left`, `e_right`.
(The k = 3 C rule is a 77-step segment that hits Lean's recursion limit; it was checked by `symtm` only.)

Cousin: `1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC` builds the same level words and right-hand staircase with a
different table.

## Halting

Only B1 halts; B is entered only from A0 (1RB): halts iff `A> 0 1`. CTL K = 3..6: halts remain; n-gram CPS fails;
no invariant mod 2..12; no halt in 10^9 steps (C).

## Notes for later

- Prove the conversions for every k at once (a hand-written Lean lemma by induction on k).
- Sample at the boundaries between levels and derive how the counts move per sweep; that gives a counter-like
  macro machine whose levels are digits.

## Pages

- [`pages/holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/explainer.html`](../../pages/holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/explainer.html)
- [`pages/holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/proof-status.html`](../../pages/holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/lean/check.sh
```
