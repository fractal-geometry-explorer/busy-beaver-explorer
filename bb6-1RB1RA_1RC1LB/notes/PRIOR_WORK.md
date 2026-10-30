# Prior work on 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB

A search of the Busy Beaver community's records and the related literature, done on 30 October 2026, for what was
known about this machine before and alongside the work in this folder.

## In short

- **It is not a named cryptid, and it has no wiki page.** The bbchallenge wiki's
  [Cryptids](https://wiki.bbchallenge.org/wiki/Cryptid) and [BB(6)](https://wiki.bbchallenge.org/wiki/BB(6)) pages
  do not mention it, and no wiki page for it turned up in searches.
- **It is still an open BB(6) holdout.** It is on @mxdys's holdout lists of 16 October 2026
  ([663 machines](https://wiki.bbchallenge.org/w/images/6/69/BB6_holdouts_663.txt)) and 24 October 2026
  ([623 machines](https://wiki.bbchallenge.org/w/images/4/4c/BB6_holdouts_623.txt), the latest on the
  [Holdouts lists](https://wiki.bbchallenge.org/wiki/Holdouts_lists) page). The community's annotated holdout ledger
  sorts it into the large "Cubic Mess" class, with no status, notes or names against it (snapshot of 26 September
  2026, row 734).
- **One other group has studied it, and only at the level of a block map.** Google DeepMind's
  [cryptids](https://github.com/google-deepmind/cryptids) repository added it on 27 October 2026 as one of 20 "open
  BB(6) acceleration problems" ([PR #18](https://github.com/google-deepmind/cryptids/pull/18), Tom Zahavy). It proves
  in Lean, with Mathlib, that the machine halts iff an explicit map on two stacks of block lengths halts, and gives a
  higher-level map with one stack removed. It does not reduce halting to a single number. As far as this search
  found, the criterion proved here (halting iff N = 10 + Σ p_l·2^(m−l) is ever a power of two) is new.
- **One equivalent machine is known.** The ledger records that
  `1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB` was "merged into another equivalence class in April 2026" (mxdys, -d).
  It runs through the same tapes as this machine (checked below), so this machine is presumably the class it was
  merged into, and everything here applies to it too.
- **Its Collatz-like map is not Antihydra's or Hydra's.** Those iterate one integer under n → ⌊3n/2⌋ and halt when a
  parity count goes negative. This machine's map acts on a list of numbers, a carry wave of halvings, and the next N is
  not a function of N (below). Its halting question is of the same "probviously non-halting" kind, though.
- **No better bounds are published.** The community has simulated every BB(6) holdout to 10^13 steps. The bounds
  here go far beyond it: no halt in 1.4·10^16 steps (Lean kernel), 4.4·10^37 (Lean with `native_decide`) and
  2.7·10^49 (the tabulated search); see the folder README for what each rests on.

## The holdout lists and the ledger

The current holdout lists are @mxdys's, linked from the wiki's [Holdouts lists](https://wiki.bbchallenge.org/wiki/Holdouts_lists)
page; the [BB(6)](https://wiki.bbchallenge.org/wiki/BB(6)) page (last edited 24 October 2026) counts 623 machines up
to equivalence and 1,336 without. This machine is on the 663 and 623 lists. The same machine appears in the 1,003
machine list of 30 August 2026 and the 815 class list of 24 September 2026 (copies in the third-party repositories
[CyclingCycloid/bb6-holdout-research](https://github.com/CyclingCycloid/bb6-holdout-research) and
[skm12323/bb6-holdout-analysis](https://github.com/skm12323/bb6-holdout-analysis), neither of which analyses this
machine).

The annotated ledger is a Google Sheet linked from the BB(6) page. Its live view did not load for this search, so
this note uses the snapshot of 26 September 2026 in `data/ledger-2026-09-26.csv` of CyclingCycloid's repository. In
it, row 734 is this machine: class "Cubic Mess", every other column empty. Three neighbours share its first three
states (`1RB1RA_1RC1LB_1LD0RA`):

| machine | ledger | |
|---|---|---|
| `1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB` | row 681, EQUIVALENCE, "Merged into another equivalence class in April 2026", mxdys, -d | the same run as this machine (below) |
| `1RB1RA_1RC1LB_1LD0RA_1LB0LE_1LF1LD_---0LD` | row 737, Cubic Mess, no notes | a different run (145 new left cells in 3·10^6 steps against this machine's 15); not on the 623 list |
| `1RB1RA_1RC1LB_1LD0RA_1LA0LE_---0LF_0RC0LB` | row 738, Cubic Mess, no notes | a different run (123 new left cells in 3·10^6 steps); not on the 623 list |

Why the last two left the list was not checked.

## The equivalent machine

`1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB` has the same states A, B and C and differs in D, E and F, the states
of the left-end and halting paths. Evidence that it is this machine (`py/sibling.py`):

- the tape at every time A stands on the right end is the same, event for event: 13,244 events in the first 3·10^8
  steps, compared with `tools/c/tmrun` (`python3 py/sibling.py events 2000000` checks the first 951 in Python);
  the sibling is a few steps faster per event (15,134 steps ahead after 3·10^8);
- the tapes at its first 15 new left cells are those of this machine, a little earlier (at step 2,046,845 against
  2,047,931), and its 16th comes at step 26,618,858,884 with the first block 1^110037, where this machine's comes at
  step 26,618,972,322 with the same block, as the wave model predicts (a direct run of the sibling to 2.7·10^10 steps
  with `tools/c/tmrun ... records`);
- from 4,992 macro configurations X(ls, n, cs) of `lean/Macro.lean` (up to three left blocks of length 1 to 5, n up
  to 7, four right parts), the two machines halt within 20,000 steps in exactly the same 738 cases
  (`python3 py/sibling.py halts`).

That is strong evidence, not a proof; a proof would be a simulation of each macro rule of one machine by the other.

## DeepMind's cryptids repository

[google-deepmind/cryptids](https://github.com/google-deepmind/cryptids), file
`BusyBeaver/BB6/Accelerations/M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean`, section 1.6 of
`BusyBeaver/BB6/Accelerations/README.md` (merged 27 October 2026, commit `e5f59ed`):

- states C(a, L, R), with L the blocks to the left written as `1^(x+1) 0` and R the blocks to the right written as
  `1^(d+1) 00`; the run from blank tape reaches C(3, [0], []) after 19 steps;
- six rules: a = 0 with L empty halts; otherwise the head transfers a block, or for a = 2k + 1 bumps the top of L k
  times, or for a = 2k + 2 pushes onto R, each followed by a full transfer sweep `transferB` of R onto L;
- theorems `is_valid_acceleration` and `isHalt_iff_acceleration` (the machine halts iff the map does), and the
  higher-level map on the section R = [] with `isHalt_iff_highLevel_acceleration` and
  `acceleration_iff_highLevel_acceleration`; the file has no `sorry`;
- listed as "Stacked", one of seven open stack-family problems; the repository describes the family as "local
  Collatz-like residue branching at the head with arbitrarily deep historical memory".

This is the same level as the macro step proved here (`lean/Macro.lean`, `halts_iff`), with a different cut: this
folder starts from X([1], 2, []) after 15 steps. Nothing in the repository corresponds to the super step or to the
number N. DeepMind's map was public two days before the macro step here was merged (29 October); this folder's work
did not use it, so it has priority for the block-level reduction, and the super step and the N criterion go beyond it.

## Comparison with Antihydra and Hydra

[Antihydra](https://wiki.bbchallenge.org/wiki/Antihydra) (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) iterates
H(n) = ⌊3n/2⌋ from 8 with a counter that gains 2 for each even value and loses 1 for each odd value; it halts if the
counter reaches −1. [Hydra](https://wiki.bbchallenge.org/wiki/Hydra), a BB(2,5) machine, iterates the same map with
another start and stop. Their state is one integer plus a counter, and the open question is about the parities of
⌊K·(3/2)^n⌋ (Mahler's 3/2 problem).

This machine is different in kind:

- its state is a list (p_1, …, p_m) that grows, not one number: a super step sends a wave of halvings left from the
  right end (d_l = p_l + d_(l+1)/2), turns at the first odd d, and rewrites only the blocks it passed;
- the deciding number N = 10 + Σ p_l·2^(m−l) does not determine its successor: on the orbit from (1, 6), N = 398 and
  N = 470 both have m = 6 and v_2(N) = 1, and go to N + 72 and N + 61;
- halting is an orbit hitting a power of two, not a random walk going negative. No multiplication by 3/2 appears; the
  growth comes from the wave depositing (d_i + 5)/2 and (d_i − 1)/2 where it turns.

What it shares with them is the shape of the problem: a deterministic orbit that a coin-flip model says should never
halt, with no invariant to prove it. The wiki's other power-of-two cryptids (the Erdős and Sloane ternary conjectures,
about base-3 digits of 2^n) ask a different question. Among the community's informal classes it sits in "Cubic Mess";
among DeepMind's, in the stacked family.

## Where this search did not reach

- The bbchallenge Discord is not publicly searchable, so a passing mention there cannot be ruled out. The forum
  (discuss.bbchallenge.org) and web searches for the machine's code found nothing.
- The wiki's own full-text search is behind a bot wall; searches through web search engines found no page.
- The ledger's live sheet did not load; the 26 September snapshot was used.
