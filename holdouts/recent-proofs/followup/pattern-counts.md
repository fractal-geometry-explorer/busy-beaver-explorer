# pattern-counts: counter programs made from pattern counts (27 November 2026)

Technique C of [`../technique-brainstorm-2-nov27.md`](../technique-brainstorm-2-nov27.md). **Result: negative. The
technique's own first test fails on every control, no open machine is decided, and the reason is structural.**
Evidence level: computed. Nothing here is a proof and no machine's status changes. Tools: `tools/patcount/`.

## What was built

The counter program that exists for every machine without understanding it. A tape is the head state, an exact
window of radius R around the head, and for each side the number of occurrences of every n-cell pattern beyond the
window (optionally separated by position mod m). A step shifts the window: one pattern is added to one side, one
is removed from the other, and the removed pattern's last cell enters the window. Which pattern is removed is not
known. The program tries every pattern whose count is positive and for which the rest can still be the counts of a
half tape (the Euler-trail conditions on the n-gram graph: degree balance and connectedness). With that guard the
step function is the best possible for this description: it produces a successor exactly when some tape with these
counts makes that step.

Two ways to analyse it:

1. **`patcount`** explores the program with each count kept exactly up to a cap K and as "big" above it. If the
   explored set closes without a halting state, it is a finite certificate. If a halting state is reached on a path
   on which no count met the cap, that path is a path of the program itself, so no solver of any kind (Spacer,
   polyhedra, templates) can prove the program safe.
2. **The rearrangement test** (`shuffle_test.py`) asks the question a solver cannot avoid, without a solver.
   Take a real configuration, rearrange each half tape beyond the window so that every pattern count stays the
   same, and run the machine. The rearranged tape has the same description as the real one. If it halts, every
   invariant written in these counts contains a halting configuration. Iterating (rearrange, run, rearrange)
   samples what the program reaches from real configurations late in the run.

## Controls

The brainstorm's first test: the machines of busycoq pull requests 97, 110 (two machines) and 113, and the
machine of cryptids pull request 37, all proved elsewhere never to halt, must come out.

| control | from blank tape, `patcount` | rearrangement, 4-cell patterns | 6 cells | 8 cells |
|---|---|---|---|---|
| 1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD (PR 97) | halt reached, exact path | 18 of 24 chains halt | 0 | 0 |
| 1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF (PR 110) | halt reached, exact path | 23 | 16 | 6 |
| 1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC (PR 110) | halt reached, exact path | 23 | 18 | 7 |
| 1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC--- (PR 113) | halt reached, exact path | 19 | 1 | 0 |
| 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- (cryptids 37) | halt reached, exact path | 23 | 0 | 0 |

"Exact path": at n = 4 with a window of radius 8 (K = 12) all five reach the halt on a path where no count met
the cap, after 228 to 342 steps from the blank tape, so the program itself reaches the halt. The same holds at
n = 3 for four of the five and with positions mod 4 (n = 2) for all five. `patcount` was run on the controls at
n = 2 to 8, m = 1 to 4, K = 1 to 12 and R up to 13: 200 runs, none safe.

Starting late does not help. From the real configuration after 10^6 steps, with 8-cell patterns, the control of
PR 97 still reaches a halting state (K = 20, 524 steps). The path shows the reason: the left counter (15 blocks
`1100`) is spent in 15 real bounces against the right wall, and after each bounce the program may take the next
right-hand pattern in any order the counts allow. The proof of PR 97 is exactly a statement about that order (the
wall answers m bounces), and the counts do not contain it. This run met the cap, so it is evidence and not a
refutation; the rearrangement test found no halt for this control at 8 cells in 100 chains.

Four more machines on the target list have outside proofs of non-halting (busycoq pull requests 116, 117, 119 and
cryptids pull request 42) and serve as controls too. All four fail: rearranged tapes halt at 4, 6 and 8 cells.

## The 39 targets, the reservoir counters, and all open machines

- **`patcount` from the blank tape**, ten settings (n = 2 to 6, m = 1 to 4, R up to 10): the 39 machines of F08, the
  9 open reservoir counters of R08 and 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---. 490 runs: a halting state is
  reached in 459 and the state limit (6 million) in 31. No run is safe. For 47 of the 49 the program reaches the
  halt on an exact path at 4 cells with a window of radius 8, and for one more in another setting.
- **Rearrangement test** (24 chains of 150 rounds, random and adversarial Euler trails, configurations from the
  first 3·10^6 steps, window radius 8) on all 469 machines marked open in `holdouts/FAMILIES.md`:

  | outcome | machines |
  |---|---|
  | a rearranged tape halts at 6 cells or wider (so at every smaller width too) | 355 |
  | a rearranged tape halts at 4 cells, none seen at 6 | 68 |
  | no halt seen at 4 or 6 cells | 46 |

  Of the 49 targets, 48 are refuted at 4 cells. The 49th, 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD, shows no
  halt in 120 chains of 400 rounds, for a reason that gives no hope: its halt can only come from the junk behind a
  chain of 230 counters mod 4, which the machine reaches once in about (4/3)^230 visits. No test of this size
  touches it, and its map on the junk is as order-dependent as the others.
- **The 46 without a halt** are not candidates either. `patcount` from the blank tape reaches the halt on an exact
  path for 39 of them (small tapes early in the run), and reaches the halt or the state limit for the other 7.
  A harder attack (48 chains of 300 rounds, up to 3·10^5 steps per round, 4-cell patterns) refutes 11 of the 42
  it finished (4 ran out of time). The 31 left are mostly in the families whose tape is a few long blocks: 12 in
  R15 (Collatz-like maps), 7 in F01, 6 in F10. Six were looked at, among them
  1RB0LA_0RC---_0RD0RF_1LD0LE_0LA1LE_0RA0LA (`E>0 1^2584 0 1^1236`): the halt depends on the block lengths through
  a Collatz-like map. A rearrangement moves cells from one block to another. That changes the orbit of the map,
  but a halt, if there is one, is as far away as on the real orbit. For these the counter program is the exact
  map with its residues thrown away, which is the opposite of what a solver needs. Lists: `tools/patcount/results/`.

## Why it fails

The brainstorm said the program "forgets the order of the patterns and keeps their numbers". The order is what the
proofs are about.

1. **Small tapes are already ambiguous.** At step 13 the PR 97 control has the right half `0110100`. The word
   `0101100` has the same 3-cell pattern counts, and the program's path to the halt goes through it. Wider
   patterns and a wider exact window move the first ambiguity later (a halting path of 30 steps at n = 3, R = 2;
   90 to 404 steps on the controls at n = 3, R = 10 and 13) but do not remove it.
2. **Late tapes are a regular body with a few defects, and counts cannot place a defect.** A body `X^a 0 X^b 0 X^c`
   has the same counts for every a, b, c with the same sum. The known proofs for these machines are statements
   about where the defects are: a wall that answers m bounces (PR 97), run-length digits read in order with a carry
   (PRs 113 to 119), the first few digits of the tail (cryptids 37). An adversarial rearrangement puts all defects
   next to the head, and the machine halts.
3. **Run-length tokens do not repair this.** Counting n-grams of unary digits or of runs was tested with the
   rearrangement test on the five controls (200 rounds, 30 or 40 chains). Digit 2-grams and run 2-grams: at least
   five chains in six halt on every control. Run 3-grams: halts on every control (1 to 17 chains). Digit 3-grams:
   halts on every control under at least one of the two digit conventions. The
   quantities in the proofs ("k ≥ 42", "c ≤ G", "2p ≤ 3g + 3") are not pattern counts: k is the length of one named
   run at one named place, and p and g are read off a stream of gaps column by column.
4. **Where no rearranged tape halts, the machines looked at are Collatz-like**, and the counter program is a
   blurred copy of an exact map (see the 46 above).

So there is no setting between "too coarse" (the program reaches the halt) and "too fine" (the counts determine
the tape, and the program is the machine). The same was seen from the other side in
[`horn-solvers.md`](horn-solvers.md): solvers work when the program is loose in the right place, and what is loose
here is the order of the tape, which is the wrong place.

## What could be kept

- **The rearrangement test as a filter for any proposed abstraction.** It takes seconds per machine and answers
  "can an invariant in this vocabulary exist at all?" before anyone writes a solver. It works for any vocabulary
  that has a "same description, different tape" sampler. It would have saved building the cap-and-explore engine.
- **A robustness figure per machine.** How often a rearranged tape halts measures how much of the tape's order the
  machine depends on. Three machines of one table (1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE,
  1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA, 1RB1RD_1LC---_1RF0LD_0RE1LC_1RA1RF_1RE0LF) halt from every
  rearranged tape even at 12-cell patterns. That is the property halt hunts by perturbation need
  (technique B of the brainstorm), and the table in `results/` ranks all 469 machines by it.

## Not done

- No Spacer or polyhedra run on the program without a cap. For every control and 48 of 49 targets an exact halting
  path exists from the blank tape, so the answer from the blank tape is known to be "unsafe". From a late start
  the question is open in principle for machines where neither an exact path nor a halting rearrangement was
  found (31 machines, `results/no_halt_after_heavy.txt`), and the ones looked at are Collatz-like.
- The second form of the brainstorm (named long runs as counters plus counts of short runs) was tested only
  through the rearrangement test on digit and run n-grams, not built.
- No Lean: nothing closed.
