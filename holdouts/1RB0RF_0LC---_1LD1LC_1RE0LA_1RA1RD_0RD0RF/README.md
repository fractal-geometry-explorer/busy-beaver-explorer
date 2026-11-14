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

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 7.35x10^13 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.05x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 7,816 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF 400
```

## Pages

- [`pages/holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/explainer.html`](../../pages/holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/explainer.html)
- [`pages/holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/proof-status.html`](../../pages/holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF`](../1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E
- [`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF`](../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF`](../1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---`](../1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC1LF_0RA---/README.md) (in a mirror): 8,003,899 configurations, the last at step 9,999,998 here and step 8,007,428 there
- [`1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---`](../1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---/README.md) (in a mirror): 8,003,899 configurations, the last at step 9,999,998 here and step 8,003,898 there

<!-- end of related machines -->
