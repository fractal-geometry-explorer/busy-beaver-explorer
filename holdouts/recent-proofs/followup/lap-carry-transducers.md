# Sweep carries as look-ahead transducers: a screen of all 608 and a closure checker (26 November 2026)

This follows up proposal C of [`../technique-survey-nov26.md`](../technique-survey-nov26.md): learn the carry of a
sweep as a transducer with look-ahead, then check closure. Everything below is computed, not proved. **No machine
was decided.** The tools are [`../tools/lapcs.c`](../tools/lapcs.c) (screen) and
[`../tools/lapclose.py`](../tools/lapclose.py) (closure checker). The screen's table is
[`lap-carry-screen.tsv`](lap-carry-screen.tsv).

## The idea, made exact

The survey asked for a learned carry. For a Turing machine nothing has to be learned: the carry is the
**crossing sequence**.

- **Lap.** Pick a home end of the tape. A lap starts each time the head stands on the outermost visited cell of that
  end and steps away from it. Two lap rules are used: *each return* (every such moment starts a lap) and *full sweep*
  (a lap ends only after the head has also reached the far end).
- **Carry.** For each boundary between two cells, the carry of a lap is the list of (state, direction) with which the
  head crosses that boundary during the lap. A cell's new content is a function of its old content and the two
  carries beside it. That function is the machine itself, so it is exact.
- **Look-ahead.** The carry at a boundary depends on the tape on both sides. A sweep whose carries come from a
  finite set is therefore a finite two-sided transducer (a bimachine), with no approximation.
- **What the screen measures.** Whether the set of carries stops growing, how long the longest one is, how many
  distinct windows of 1 to 4 annotated cells occur, and how well a carry is predicted by the neighbouring carry plus
  0, 2, 6 or 16 cells of tape, in each direction.

**The PR 593 artefact.** That false positive was a carry read off by a residue at a wall. Here a carry counts only
if the whole lap is covered by a finite set of crossing sequences, so a value that is one step of a zigzag through
copied tape is not a carry at all. For that machine, 1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE, the screen shows a
carry set that keeps growing from the left end (1,335 at 10^7 steps, 1,654 at 2·10^7) and carries thousands of
entries long from the right end. It is not a candidate.

## Screen results (2·10^7 steps, both ends, both lap rules)

**The survey's first target does not have a finite carry.** For 1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE the
number of distinct carries grows from 15,311 (10^7 steps) to 21,660 (2·10^7 steps) from the left end and from 13,895
to 17,846 from the right end; the longest has 266 entries. Its siblings 1RB1LB_1LC0LD_---1LD_1RE0LA_0RF1RD_1RA1RE and
1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA behave the same. This agrees with the left-end study of that machine
(nested sweeps, PR 597). The technique does not apply to this table at cell level.

**The other named targets.**

| machine | result |
|---|---|
| 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC and 1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD--- | carries grow, longest over 1,200 entries: no |
| 1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---, 1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---, 1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD--- | carries grow from both ends: no |
| 1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE | 78 carries from the right end with each-return laps; grows with full sweeps |
| 1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA--- | 18 carries from the right end with each-return laps; it makes no full sweeps in 2·10^7 steps |
| 1RB0LD_1LC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB | 20 carries from the right end with each-return laps; grows with full sweeps |
| 1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF, 1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB | 38 and 77 carries from the left end with each-return laps; grows with full sweeps |
| 1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC | about 200 carries, still creeping up at 4·10^8 steps (182 to 206) |
| 1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA | finite with full sweeps: 3,282 and 2,631 carries, fixed from 10^8 to 4·10^8 steps |
| 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---, 1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC | no growth between 5·10^6 and 2·10^7 steps, but thousands of carries, up to 2,425 entries long |
| **1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA** | **19 carries (left home) and 37 (right home), at most 6 entries, fixed from 10^8 to 4·10^8 steps** |
| **1RB0LF_0LC1LB_0RD1LA_1RE0RA_---1RD_1RC1LF** | **42 and 27 carries, at most 10 entries, fixed from 10^8 to 4·10^8 steps** |

**All 608.** A carry set that did not grow between 5·10^6 and 2·10^7 steps was found for 234 machines (212 of them
open), almost all with each-return laps only. With full sweeps it holds for 6 open machines: the five in the last
four rows of the table above, and 1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB--- (about 4,900 carries, up to 2,831 entries long). The table file lists every case with its counts.

Two cautions.
- Saturation at 2·10^7 steps can be premature. 1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA showed 879 carries there and
  3,282 later.
- With each-return laps most laps are short, and the cells a short lap does not reach carry no annotation. A finite
  carry set then says little about the far part of the tape. That is the situation of busycoq PR 114's machine
  1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---: 71 carries with each-return laps, but its sweeps turn back at varying
  depths, and with full sweeps its carries grow.

So the bimachine picture is exact for the two machines in bold, both from the survey's list of eight chaotic
bouncers. For them one lap is a fixed finite transducer, and the halting question is whether iterating that
transducer from the start row ever leaves its domain.

## The closure checker

`lapclose.py` looks for an invariant of this form: *the row has some annotation whose windows of k cells all lie in
a finite set G*. A letter is (cell, head mark, carry of the coming lap); with J > 1 it also holds the carries of the
next J laps, and with P > 1 the cell's distance from the start cell modulo P. It checks

1. every window of G is locally consistent with the machine, cell by cell. By the usual crossing-sequence argument
   a finite, locally consistent annotation is the real lap, so the lap ends without a halt;
2. the first row is covered;
3. for every annotated row over G, the row after the lap has an annotation over G. This is an inclusion of two
   finite automata, checked by a subset construction.

If all three hold the machine never halts. When 3 fails, the counterexample row is run for one lap and its windows
are added to G. If that lap halts, the abstraction contains a halting row and the attempt ends ("leak"). The checker
is not verified. It closes a plain two-state bouncer (`1LB1RA_1RA1LB`) for several k, J and P.

**Results.**

- Neither bold machine closes. Tried: k from 2 to 24, J from 1 to 3, P up to 16, from both ends, with the first
  10^6 or 2·10^6 steps skipped. Every attempt leaks within 20 rounds.
- The decided machine 1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF (finite carries with full sweeps, 91 and 139) leaks
  too, so a leak says nothing about halting.
- A grid over every saturating case of the screen (330 machine, end and lap-rule combinations; (J, k) = (1, 3),
  (1, 6), (2, 3), (2, 6), (3, 4); 10^6 seed steps; 60 s each): 1,650 runs, **none closes**. 1,487 leak, in 45 a
  counterexample row's lap runs over its step cap, and 118 were still adding windows at 60 s.
- Long runs (110 minutes, 400 counterexamples per round) on four cases that did not leak in the grid:
  1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD (left, k=6) and 1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD--- (right, k=6)
  were still growing after 366 and 364 rounds, at about 108,000 windows each;
  1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE (left, J=3, k=4) leaks in round 19; and
  1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD (right, k=3) ran out of memory. The first two neither leak nor
  converge, so for them the window language is the wrong shape rather than too coarse.

## Why the cleanest candidate does not close: 1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA

Measured over the first 2·10^7 steps (2,080 laps, home at the left):

- At a lap start the tape is a chaotic part (runs of 1s of odd length separated by single 0s) followed by a periodic
  block `(01111101)^n` that reaches the right end.
- The tape grows by exactly 4 cells per lap, all at the far end of the periodic block.
- The chaotic part changes by between −8 and +16 cells per lap, +1.75 on average over laps 1,040 to 2,080. The
  periodic block's share of the tape falls from 0.81 (lap 52) to 0.63 (lap 2,080); at these rates it would level off
  near 0.56.
- Splicing does no harm when the block stays long: 400 rows made by deleting a stretch of a late row between two
  equal 16-cell contexts, and 282 rows made by joining the head of one late row to the tail of another, all run 40
  more laps without a halt. Cutting the block by a multiple of 8 cells is also harmless (200 to 1,400 cells
  tested); a cut that is not a multiple of 8 halts.
- Every leak the checker finds is a short row in which the chaotic part sits next to the end of the tape.

So for this machine a halt needs the chaotic part to catch up with the far end, which recedes 4 cells per lap while
the chaotic part advances 1.75 on average and at most 16. No regular set of rows separates "the block is still long
enough" from the rest, which is why every window size leaks. A proof would need a bound on how fast the chaotic part
can grow over many laps, a statement about the chaos itself. That is the survey's shape N3 (track one inequality),
and it is the open item this work leaves for the machine.

## What this means for proposal C

- The carry does not need learning. Where a sweep has a finite carry, the crossing sequences give the exact
  transducer, and `lapcs.c` finds those machines in seconds.
- Full-sweep finite carries are rare: 6 open machines, 2 of them small.
- For those two the obstacle is not the carry. It is the set of rows: the reachable rows are not described by any
  window language we tried, and the measured mechanism for one of them is a race between two growth rates.
- Next steps that this suggests: (a) for 1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA, look for a potential that bounds
  the chaotic part's growth per lap, using the exact 19-carry transducer; (b) do the same measurement for
  1RB0LF_0LC1LB_0RD1LA_1RE0RA_---1RD_1RC1LF, whose irregular zone sits at the right end; (c) for the machines with
  varying sweep depth, replace the lap by a recursive call, as busycoq PR 114 does, since a flat lap cannot express it.

## Reproduce

    gcc -O2 -o lapcs lapcs.c
    ./lapcs MACHINE 20000000 L 0 0     # each-return laps, home at the left
    ./lapcs MACHINE 20000000 R 0 1     # full sweeps, home at the right
    python3 lapclose.py MACHINE L 9 1 2500000 400 1 1000000   # k=9, J=1, full sweeps, skip 10^6 steps

`lapcs` prints one `CK` line per checkpoint: laps, distinct carries (`cs`), the longest (`maxlen`), distinct windows
`g1` to `g4`, then for look-ahead 0, 2, 6 and 16 cells outward (`o0` to `o3`) and inward (`i0` to `i3`) the numbers
keys / keys with two answers / wrong predictions / predictions.
