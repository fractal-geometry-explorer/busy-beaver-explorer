# 1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC

bbchallenge id 73584. Every sweep rewrites the whole tape between two codes for a list of numbers: at the right end it is runs 1^(3k+2) separated by single 0s, at the left end runs 1^(3a+1) separated by 0^(3b+2); the numbers look irregular.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 1LC | 1RD |
| C | 1LA | 1LC |
| D | 1RA | 1RE |
| E | 0RB | 0LD |
| F | --- | 0LC |

## What it does

The right side grows like √t, the left like t^0.19. Every sweep rewrites the whole tape. With the head at the
right end, the tape is a list of runs of 1s separated by single 0s,

    step 999,951,866:  1^9 0110 1^20 0 1^11 (011111)^2 0110 1^8 (011)^3 1^9 0 1^8 …    (0110 = 0 1^2 0)

and 9,832 of its 9,834 runs have length 3k + 2. With the head at the left end, the tape is runs of 1s of length
3a + 1 separated by runs of 0s of length 3b + 2:

    step 536,523,607:  A>0 1^13 0^5 1^10 0^5 1^4 0^5 1^16 0^8 1^4 0^5 1^4 0^11 1^7 …

(2,882 of 2,884 runs of 1s and all 2,883 runs of 0s). So the tape is one list of numbers written in two codes, and
each sweep translates it: the leftward sweep in C erases runs of 1s cell by cell (`shift_l_C_1`, proved). The
numbers themselves (k up to 13, a up to 13, b up to 11) show no order. The same two codes are used by
1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD in this batch.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the leftward sweep in C turning a run of 1s into 0s (`shift_l_C_1`) (`shift_l_C_1`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The two codes are measured; the map on the list is not known, and the list looks
irregular. Halting needs A reading 1 with a 0 to its right. Same family as 1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD
in this batch (the same two codes).

## For later

More than a day. Next: (1) write the right-end tape as the list k1, k2, … (runs 1^(3k+2)) and the left-end tape
as pairs (a, b), and find the transducer that maps one to the other (a finite-state rewriting would show up as a
rule on short windows of the list); (2) compare with 1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD, which uses the
same codes.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/lean/check.sh
python3 holdouts/1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: D with 0 under the head, 1 right, 0 two right.

## Pages

- [`pages/holdouts/1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/explainer.html`](../../pages/holdouts/1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/explainer.html)
- [`pages/holdouts/1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/proof-status.html`](../../pages/holdouts/1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA`](../1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
