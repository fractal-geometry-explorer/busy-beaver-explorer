# 1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF

bbchallenge id 121862. A slower twin of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF: the same running-parity (Sierpinski) word in 4-cell letters 1110/1111, with the same epochs; at the epoch starts the two machines have identical tapes, head position and state.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1RC | 0RC |
| C | 1LD | --- |
| D | 0LB | 1LE |
| E | 1RF | 0LD |
| F | 1RA | 1RF |

## What it does

The twin of `1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`: at 12 of the 13 epoch starts up to 1.7·10^9 steps the two
machines have **identical configurations** (tape, head position, state), this one about 1.5 times later
(`c/dump.c`):

| this machine | twin |
|---:|---:|
| 3,350 | 2,284 |
| 8,689 | 5,873 |
| 72,335 | 47,799 |
| 734,951 | 487,979 |
| 6,420,857 | 4,277,179 |
| 60,731,203 | 40,483,837 |
| 1,744,002,084 | 1,162,585,978 |

(all 12 listed in `status.json`; the epoch near 2·10^7 was sampled at different turns). So it computes the same
thing: a word in `u = 1110`, `v = 1111` replaced by its running XOR on each leftward sweep, epochs x1.75.

**Proved** (`lean/Rules.lean`): eleven shift rules over `1111`, `0101`, `1010`.

## Halting

Only C1 halts; C is entered only from B (moving right): halts iff `B> x 1`. CTL K = 3..6: halts remain; n-gram CPS
3..7 fails; no halt in 3·10^9 steps.

## Notes for later

- Prove the agreement with the twin as a simulation (a map from this machine's sweep configurations to the twin's).

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 18, history 1 up to width 18, history 2 up to width 16, history 3 up to width 16, LRU history up to width 3 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 16, p = 3 up to width 16, p = 4 up to width 16, p = 6 up to width 16.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..9; n = 10 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: A with 0 under the head, 1 two right.

## Pages

- [`pages/holdouts/1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/explainer.html`](../../pages/holdouts/1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/explainer.html)
- [`pages/holdouts/1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/proof-status.html`](../../pages/holdouts/1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**A slowed-down copy of [`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`](../1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/README.md) (observed, not proved).** Read this machine's states A as A, B as B, D as C, E as E, F as F of the other machine. Then 4,995,966 of this machine's first 10^7 configurations (tape, head position and state) are configurations of the other machine, in the same order. The last one is step 9,999,982 here and step 6,664,008 there, so this machine takes about 1.5 times as many steps. At most 229 steps pass here between two such configurations. The tables are not renamings of each other. Lean proves (`lean/Twin.lean` here, `sim_or_break`, `not_halts_of_noBreak`) that each step of the faster machine is matched by one or three steps of the slower one up to the first break, a configuration where the paired states act differently, and that neither machine halts if no break ever comes. A halt of either machine is itself a break, and the halting transitions of the two do not correspond, so the two are not known to halt together.

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD`](../1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD/README.md): rename A→F, B→C, C→A, D→B, E→D, F→E and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD`](../1RB0RB_1LC---_0LA1LD_1RE0LC_1RF1RE_1RA0RD/README.md): rename A→F, B→A, C→B, D→C, E→D, F→E; it is this table started in state B
- [`1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA`](../1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA/README.md): rename A→C, B→D, C→E, D→F, E→A, F→B; it is this table started in state E
- [`1RB1RA_1RC0RF_1RD0RD_1LE---_0LC1LF_1RA0LE`](../1RB1RA_1RC0RF_1RD0RD_1LE---_0LC1LF_1RA0LE/README.md): rename A→B, B→C, C→D, D→E, E→F, F→A; it is this table started in state F

<!-- end of related machines -->
