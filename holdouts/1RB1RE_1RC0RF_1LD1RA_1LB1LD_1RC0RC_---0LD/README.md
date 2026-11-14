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

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 22, history 2 up to width 13, history 3 up to width 14, LRU history up to width 3 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: A with 0 under the head, 1 right, 0 two right.

## Pages

- [`pages/holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/explainer.html`](../../pages/holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/explainer.html)
- [`pages/holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/proof-status.html`](../../pages/holdouts/1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LC0LC_---0RA`](../1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LC0LC_---0RA/README.md): rename A→D, B→B, C→C, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0RF_1LC1RD_1LA1LC_1RA1RE_1RB0RB_---0LC`](../1RB0RF_1LC1RD_1LA1LC_1RA1RE_1RB0RB_---0LC/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
