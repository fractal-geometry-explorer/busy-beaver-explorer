# 1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---

A bouncer whose left sweep rewrites the tape two cells at a time (`01` to `11`, `11` to `10`). The content drifts right and is
eaten by the right end; places where the sweep lands on a 0 (defects) start nested inner bounces, which gives zones of
growing pattern and irregular resets. It halts only if a left sweep meets `1 0 0 0` (proved in Lean); that has not happened in
6.1·10^10 steps. Halting is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 0LC | 0RA |
| C | 1LF | 0LD |
| D | 1LE | 0RC |
| E | 1LB | 1LD |
| F | 1RB | --- |

## What it does

**The tape** is blocks of ones separated by single 0s; almost all blocks have odd length (1, 3, 5, 7). Written as block
lengths, when state E steps off the left end (an *event*; 4 new cells each time) at 9.3·10^8 steps:

    3 (1 3 1 5 5)^29 1 3 1 5 1 5 (3 3 1 3 1 3 5 5 3 5 5 3 1 3 1)^254 … (3)^8 5 (3)^12 5 (3)^7 1 … (3)^26 5 (3)^31 1

Zones from left to right: the 5-block word `1 3 1 5 5` (20 cells), a 15-block word (60 cells), a 45-block word (180 cells,
seen 10 times at 5.2·10^8 steps), then runs `(3)^k` separated by a 1 or a 5, k larger the further right.

**Right sweep (state A).** Every 0 moves one cell right (`a_zero`). Two 0s: the head steps over the first (`a_z2`).
Three 0s, the right end: `1 1 A>000` becomes `1 E>1 1 00`, the turn (`a_turn`).

**Left sweep (states E, D), two cells at a time**, E on the right cell of a pair and D on the left one:

| pair(s) | becomes | then | Lean |
|---|---|---|---|
| `01` | `11` | next pair | `e_pair`, `sweep` |
| `11` | `10` | next pair | `e_pair`, `sweep` |
| `10` | `01` | head turns right (inner bounce) | `e_bounce` |
| `01 00` | `10 01` | next pair | `e_z2_pass` |
| `11 00` | `10 10` | head turns right | `e_z2_bounce` |
| `00 00` | `10 10` | head turns right (the left end) | `e_end` |
| `10 00` | | **halt** after 3 steps | `e_prehalt`, `prehalt` |

**Regular round trip.** With every block odd, every 0 is on the left cell of its pair, only the first two rows fire, and the
left sweep leaves the 0s on right cells; the next right sweep moves them back to left cells. Together: the pairs are
complemented and shifted by one pair, so the content moves 2 cells right per round trip. The right end stands still and
consumes it. The left end adds 4 cells per event (= 3 round trips) and one word `1 3 1 5 5` per two events
(`py/turns.py 656860 667120 8` shows two events; the zone reads `1 1 4 (1 3 1 5 5)^n`, `1 00 (3 1 5 5 1)^n`,
`0 (5 5 1 3 1)^n` in turn).

**Defects.** An even block or two 0s put the following 0s on right cells, so the left sweep lands on a 0, row 3: the head
turns right there. It then bounces between that place and the right end; each bounce moves the defect one block left, and
the right end keeps consuming. What is left to the right of the defect is content of the next kind (3 words `1 3 1 5 5`
give one 15-block word, and so on). A defect can arise inside the stretch of another one, so the zones nest. Steps
between two events range from about 7 tape lengths (three round trips) to 7.4·10^9 steps at 6.2·10^10.

**Resets.** A defect that reaches the left end rebuilds the left zone as 15-block words (7, 33, 66, 65, 254 copies at the
resets up to 10^9). Resets (tape starts `1 00 11` at the event): steps 6,443; 52,596; 65,233; 1,072,500; 42,678,053;
106,638,874; 201,754,341; 921,618,056; 18,930,310,428; 61,568,762,133 (`c/resets.c`). No regular spacing.

## Halting

Proved (kernel, `lean/Sweep.lean`): three steps before any halt the machine is in state E on a 0 with `1 0 0` to its left
(`prehalt`); from that pattern it halts (`halts_of_1000`); if the run from blank tape never shows it, the machine never
halts (`nonhalting_of_no_1000`).

Measured (`c/resets.c`, plain simulation to step 61,568,762,133): no halt. E read a 0 with another 0 on its left, inside
the tape, 285 times; after step 3.6·10^7 always in the surrounding `1 0 1 1 1 0 [0] 1 0` (row `11 00`, the two 0s
disappear). The surrounding `1 0 0 [0]` never occurred. Two 0s in a row arise inside the tape only by row 3 on the 0
behind a block of length 1 (`0 1 0` becomes `0 0 1`).

First test of the closed-set method, "do neighbours halt?" (`c/pert.c`, `c/rnd.c`, `py/small.py`): **yes for tapes
of blocks in general, rarely; no for the 3,600 perturbed real tapes tried.**

| tapes | count | steps each | halts |
|---|---|---|---|
| real tape at events 200, 700, 1500 with one cell flipped / deleted / a 0 inserted / a 1 inserted / two cells flipped / a 1 next to a 0 cleared | 3 × 6 × 200 | 2·10^6 | 0 |
| 30 random blocks of lengths 1,3,5 / mostly 3 / 1,3,5,7 / 1..5, single 0s, A at the left end | 4 × 300 | 3·10^6 | 0 |
| n random blocks of odd lengths 1,3,5,7, single 0s, A at the left end; n = 2, 3, 4, 6, 8, 12, 20, 30 | 2000 each | 3·10^6 | 0, 29, 0, 3, 3, 0, 0, 0 |
| the same with lengths 1..5 (even blocks allowed) | 2000 each | 3·10^6 | 62, 14, 0, 4, 2, 0, 1, 1 |
| random bits (60 or 200 cells, random head and state; `c/rnd2.c`) | 6000 | 2·10^5 | 2655, all within 10^5 steps |

So blocks separated by single 0s are **not** a safe shape. Smallest example: blocks 3, 2 (cells `111011`), A on the first
cell, halts after 655 steps (`py/small.py`). How: the left zone becomes `1 00 1 1`, row 3 acts on the 0 behind the single
1 next to the two 0s and leaves `1 000 1`, and the next left sweep that arrives in step with it halts. The first table
of 1,200 tapes of 30 blocks showed no halt only because the rate at that size is about 1 in 2,000 or less.
An earlier version of this file said "neighbours do not halt"; that was wrong for random block tapes.

What protects the real run, as far as observed (`c/leftzone.c`, 10^10 steps): near the left end E reads a 0 in only a
few situations. The first 10 or 12 cells are `1010101111` (E 3 cells in), `111010111010` (E one cell left of the tape) or
`101110111110` (E 1 cell in) in the regular cycle, and `100…` with E 6, 8, 2 cells in or one cell outside at resets.
The fatal precursor, E on the last 0 of `1 0 0 1 0`, never occurs. In terms of blocks: a halt needs E to land on the 0
left of an even block that has two empty blocks (three 0s) before it. Not proved.

## What did not work

- **Product domain** (`py/rlectl2.py`): the run window near the head, plus the first J runs at the far end, plus the number
  of even blocks (capped) and a parity. Small parameters reach a halting abstract configuration (for example K = 5,
  caps 3/2, J = 6); larger ones (K = 4 or 5, caps 5/3, J = 4 to 8) pass 3·10^6 abstract configurations without closing.
  `py/realabs2.py` shows why: the abstraction cannot tell the long real tape from short block tapes, and those do halt.

- **Closed set of nodes (the method of ids 65826 and 11019).** It needs checkpoints `zone | w^N | T | u^M | tail` with a
  bounded zone and one or two free counts. Here the number of zones grows with the run and the long events have no bound,
  so there is no finite list of nodes; and the run shows no exact growth cycle up to 6·10^10 steps.
- **Finite-automata reduction** (`py/far.py`): DFA on one side = (parity, last k cells), k ≤ 6, either side. The blank start
  is accepted as possibly halting.
- **Closed tape language over windows of runs** (`py/rlectl.py`): states are the first K runs on each side, lengths exact up to
  a cap, then only their parity. K = 2, 3, 4 reach a halting abstract configuration; K = 5 passes 3·10^6 abstract
  configurations. `py/realabs.py 4,5,3 3e6`: the real run visits 4,821 abstract configurations, the closure 406,469;
  the first step the real run does not make glues a window of the left-end zone to an inner one.
- The shared window tool `bbtools.ctl` (K = 4, 6 cells) also keeps halting configurations.

## For later

An invariant that excludes `1 0 0 E>0`. Facts it can use: the grid of pairs is fixed by the right end (E starts one cell
left of the last 1); a right turn that lengthens the last block shifts the grid by one cell, which is what makes defects;
two 0s arise only behind a block of length 1 and are removed at the next visit unless the pair to their left is `10`. The
zone words have 20, 60, 180 cells; whether the deeper zones are periodic with 20·3^j cells is not checked. A faster
simulator would work on pairs and jump over regular round trips.

## Files

| path | what it is |
|---|---|
| `lean/Rules.lean` | 17 rules: sweeps over words and the single events, generated by `py/rules.py` (kernel) |
| `lean/Sweep.lean` | the left sweep over any pairs, and the halting pattern (kernel, hand-written) |
| `py/rules.py` | writes `lean/Rules.lean` with `tools/py/bbtools/symtm.py` |
| `py/blocks.py`, `c/dump.c` | the tape at every event as block lengths with repeated words bracketed |
| `py/turns.py`, `py/micro.py` | the tape at every reversal of the head; step-by-step trace |
| `c/resets.c` | resets, long events, and every time E reads a 0 with a 0 on its left inside the tape |
| `c/pert.c`, `c/rnd.c`, `c/rnd2.c` | halting tests on perturbed real tapes, random block tapes, random bit tapes |
| `py/small.py` | all small block tapes that halt; the example `111011` |
| `c/leftzone.c` | what the left end looks like each time E reads a 0 there |
| `py/far.py`, `py/rlectl.py`, `py/realabs.py`, `py/rlectl2.py`, `py/realabs2.py` | the certificate searches that failed, and why |
| `py/observe.py`, `c/prehalt.c` | first observations (turn tapes, entries into the halting state) |

## Status

Open. Lean, kernel only (`lean/check.sh`, 22 s): the halting configurations (`step_none_iff`), no halt in 10,000 steps
(10,000,000 by `native_decide`), 17 rules, the regular left sweep for any pairs, and "halt only from `1 0 0 E>0`".
C: no halt in 61,568,762,133 steps (`c/resets.c`, 560 s). Notes of the closed-set attempt: project file
`g09-resets/notes.md`.

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.405; right: sqrt,
exponent 0.479). After 1,000,000,000 steps: 18,938 cells visited (8,418 left of the
start, 5,248 right), 14,202 ones.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 16, history 1 up to width 16, history 2 up to width 16, history 3 up to width 18, LRU history up to width 14 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 16, p = 3 up to width 16, p = 4 up to width 12, p = 6 up to width 12.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 1 two left, 0 left, 0 under the head.

## Pages

- [`pages/holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/explainer.html`](../../pages/holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/explainer.html)
- [`pages/holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/proof-status.html`](../../pages/holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RF_0RC0LE_1RD0RF_1LB---_1LB1LE_1RA0LC`](../1RB1RF_0RC0LE_1RD0RF_1LB---_1LB1LE_1RA0LC/README.md): rename A→E, B→B, C→C, D→F, E→A, F→D and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0RE_1LC---_0RA0LD_1LC1LD_1RF0LA_1RC1RE`](../1RB0RE_1LC---_0RA0LD_1LC1LD_1RF0LA_1RC1RE/README.md): rename A→D, B→C, C→A, D→E, E→F, F→B and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
