# R02: clock and word (15 machines)

Family R02 of [`../FAMILIES.md`](../FAMILIES.md). A block at one end grows by 2, 3 or 4 cells per tick, and tick k
applies one word map P (one trip of the head into the word beside the block) 2^k times. A *phase* lasts while every
trip comes back; it ends when a trip runs off its region, the block is taken apart, and a new phase starts. A halt
can only come at a phase end.

All 15 are open. This folder holds the tools and results of the attack of 21 November 2026.

## Which machines have the clock

12 of the 15 machines run on six tables with the clock, and for all 12 it is now proved in Lean. The other three
(`1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB`, `1RB1LD_1LC0RE_1LA1RC_0LC0LA_0RF0RC_---0RB`,
`1RB1RF_1LC0RE_1LE1LD_1RE0LC_1RA1RA_1RD---`) are counters of another shape and are not treated here.

| table | machine | clock | accelerated run, no halt to |
|---|---|---|---|
| T20 | `1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---` | left end, +2 (before) | 5.79·10^176 (before) |
| T20 | `1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---` | left end, +2 (before) | 3.63·10^18 (before) |
| T20 | `1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---` | right end, +2 (**new**) | **2.72·10^177** (31 phases) |
| T20 | `1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---` | right end, +2 (**new**) | **3.91·10^162** (28 phases) |
| T45 | `1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE` | left end, +2 (before) | 2.36·10^194 (before) |
| T45 | `1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---` | right end, +2 (**new**) | **1.43·10^199** (27 phases) |
| T45 | `1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---` | right end, +2 (**new**) | **3.64·10^202** (30 phases) |
| T14 | `1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF` | right end, +4 (before) | 2.39·10^248 (before) |
| T14 | `1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD` | right end, +4 (before; simulator **new**) | see `out/` |
| T14 | `1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---` | right end, +4 (**new**) | see `out/` |
| T65 | `1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---` | left end, +3 (before) | see `out/` |
| T88 | `1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB` | left end, +3 (before) | 6.04·10^187 (before) |

("before": proved or run in the machine's own folder earlier.) The six machines marked new share a table with a
machine whose clock was already known, started in another state, mostly in a mirror. `py/clockx.py` finds the
renaming of states (and of left and right) and registers them in the exact accelerated simulator
`holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py`.

- **Checked against plain simulation:** `python3 py/runx.py M tmcheck 2e9` compares time, block and word at every
  visit of the clock end with `tools/c/tmrun.c` for the first 2·10^9 steps: all six agree (113, 90, 124, 132, 56 and
  84 visits). `out/tmcheck.txt`.
- **Lean:** `py/gen_clockx.py` writes, with `gen_clock.py` of the first clock batch, the clock theorem (`tick`, every
  level k, every word, for each tick whose 2^k trips all return, with the exact step count) for five of them
  (`1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD` already had its own, in another form): `lean/MirrorMachine.lean`,
  `MirrorRules.lean`, `MirrorClock.lean`, `MirrorBridge.lean` in each machine's folder, checked by its `check.sh`.
- **Runs:** `py/runall.sh M...` (phase lines in `out/run_M.txt`; a run stops at its memory or time limit, no run
  has halted). Each line `phase start T1 L=.. end T2 L=..` is one finished phase.

## Why "close the word map alone" does not work as planned

The plan from the regrouping was a regular language of words that P maps into itself, combined with the clock
lemma. But P fails at every phase end (that is what ends a phase), and phases end again and again (27 to 31 times
by 10^200 steps on T20 and T45). So a P-closed language has to contain the failing words, and what happens after a
failure reads the recursion stack left of the word and the word itself. The question is then again one about the
whole tape.

What can be separated is the word's *content*. `py/phase_probe.py` runs one phase from an arbitrary word
(`X>0 1 0 W`, blank to the left), exactly and accelerated. Over all words of up to 4 blocks of lengths 1 to 5
(781 words, `py/halt_words.py`, `out/halt_words_summary.txt`), the phase halts for

| table | machine | phases that halt |
|---|---|---|
| T45 | `1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE` | 328 of 781 |
| T20 | `1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---` | 87 of 781 |
| T20 | `1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---` | 87 of 781 (27 of 400 random words of odd blocks ending `1 1`, the shape the run's words have) |
| T65 | `1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---` | 29 of 781 |
| T14 | `1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF` | 0 of 781; 3 of 2,000 random words with random blocks |
| T88 | `1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB` | **0 of 781, 0 of 2,000 random words** |

So on four tables the words the run builds are special: generic words make a phase end halt. A proof there must
say which words occur, which is the counter arithmetic that defeated the earlier automaton searches.

**T88 is different.** For `1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB` no probe halted: not 2,000 phases from random
words and blocks (`py/rand_probe.py`), not 20,000 P-steps from random words (`py/pstep_probe.py`: every trip
returns or leaves its region in one of five ways), not 3,000 runs from random recursion stacks
`[1 1 1 0^(3c)]* 0^3 1 1 A> W` (`py/stack_probe.py`), not 5,000 phase ends from random stacks, exits and words
(`py/cleanup_probe.py`). From random tapes the machine halts a third of the time, so the protection is in the
block and the stack, not in the word. If "no phase from any word halts" is true, a proof does not need to know the
words at all.

## Invariants that forget the word

`tools/py/satctl_forget.py` searches for such a proof: two automata as in `satctl.py`, but each cell carries an
analysis label (structure, visited word cell, unvisited word cell whose content is unknown), and at any moment the
invariant may replace everything right of the head by "unknown". Its projection is a closed set of the machine's
configurations. Results for T88, started at the visit `E>0 1^4 0` at step 471 with the word unknown:

| sizes (left x right) | result |
|---|---|
| 3x3 to 6x6 | UNSAT |
| 8x4, 10x4, 12x4 | UNSAT |
| larger | running (`out/forget_M88.txt`) |

and for the half-tape P-step alone (`--left 00011 --wall`): UNSAT to 6x6, 7x7 timed out. For the four tables whose
generic words halt, small sizes are UNSAT as expected (`py/forget_sweep.py`).

The P-step of T88 can itself contain whole inner clocks (the word holds blocks), so the invariant likely needs the
recursion inside the word as well; the next step is to find the five exits and the phase end as rules with an
arbitrary word (Lean, `bbtools.symtm`), which would cut the problem to the trips alone.

## Files

- `py/clockx.py`, `py/runx.py`, `py/runall.sh`, `py/gen_clockx.py`: the six new clock registrations, checks, runs, Lean.
- `py/phase_words.py`: the words at the start and end of every phase of a run.
- `py/phase_probe.py`, `py/halt_words.py`, `py/rand_probe.py`: one phase from given or random words.
- `py/pstep_probe.py`, `py/stack_probe.py`, `py/cleanup_probe.py`: T88 trips, stacks and phase ends from random input.
- `py/forget_sweep.py`, `../../tools/py/satctl_forget.py`: the forgetting invariant search.
