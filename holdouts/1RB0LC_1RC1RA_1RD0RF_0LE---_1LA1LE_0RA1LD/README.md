# 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD

bbchallenge id 126068. A bouncer at the left end grows two blocks at fixed rates ((011) by 1 and (01) by 3 per two left visits) for an ever longer epoch; then a long pass empties them into an irregular region on the right, which grows from epoch to epoch.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 1RA |
| C | 1RD | 0RF |
| D | 0LE | --- |
| E | 1LA | 1LE |
| F | 0RA | 1LD |

## What it does

The run is a sequence of **epochs**. At the head's visits to the left end (state C) the tape starts

    step 403,575,993:  C>0 (011)^1131 (101)^3 (01)^221 (101)^3 0 …
    step 414,251,793:  C>0 (011)^1331 (101)^3 (01)^821 (101)^3 0 …       (400 visits later)
    …
    step 857,064,593:  C>0 (011)^4531 (101)^3 (01)^10421 (101)^3 0 …

Within an epoch every 400 visits add 200 to the `(011)` block and 600 to the `(01)` block, and the rest of the
tape, an **irregular region** of short blocks and walls on the right, does not change (1,581 compressed words).
An epoch ends with a long pass that empties the two blocks into the irregular region; then a new epoch starts
with small blocks and a larger region (5,017 words after the epoch that ends between 8.6·10⁸ and 1.7·10⁹ steps). Epochs grow
longer: they end between 1.1 and 1.6·10⁸, between 3.1 and 4.0·10⁸ and between 8.6·10⁸ and 1.7·10⁹ steps, and none ends
between 1.7·10⁹ and 2·10⁹.

So the left side, where the blocks grow, grows like √t, and the right side, which grows only at epoch ends, grows
like t^0.31.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the shift rules: A crosses `(100)^n` leftward (into `(110)^n`) and `(01)^n` rightward (into `(11)^n`) (`shift_l_A_100`, `shift_r_A_01`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The epochs are measured; the dumps at their ends and the irregular region they build are
not understood.

## For later

More than a day. Next: (1) prove the one-visit rule inside an epoch (a, b) → (a, b) + (1/2, 3/2) per visit
(two visits per cycle) with `symtm.prove`; (2) find the condition that ends an epoch (a and b at the end:
(1867, 5602), (4531, 10421)); (3) follow one dump in detail and see whether the irregular region is a list of
counts processed by a fixed rule.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/lean/check.sh
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Pages

- [`pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/explainer.html`](../../pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/explainer.html)
- [`pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/proof-status.html`](../../pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE`](../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC`](../1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B

<!-- end of related machines -->
