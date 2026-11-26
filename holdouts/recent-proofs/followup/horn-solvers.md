# horn-solvers: invariant solvers on the counter programs Lean already proves (26 November 2026)

Technique A of `../technique-survey-nov26.md`. **Result: no invariant found, on any machine tried, and the reason is
structural.** The tools work: on three control problems they find in seconds the invariants our Lean files prove by
hand. Evidence level: computed (solver runs); nothing here is a proof and no machine's status changes.
Tools: `tools/chc/` (see its README).

## What was run

Z3 5.4.1, 4 cores. Two searches per program:

- **Spacer** (constrained Horn clauses, linear integer arithmetic with div/mod), 300 s per program.
- **Template search** (`absint.py`): every variable abstracted to "exact if small, else sign and residue mod M",
  M up to 36, threshold up to 32, with a difference term where the halting test compares two counters; 600 s.

| program (Lean file under `holdouts/<machine>/lean/`) | bad state | Spacer | template search |
|---|---|---|---|
| 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC, counter-stack model `Model.lean`, orbit from K(2), N = 48 | a count fails, or N < 5 | no answer in 600 s | not applicable (unbounded stack) |
| the same, free parities from the wall 1 | a count fails | no answer in 600 s | not applicable |
| 1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA, `Map.lean` `mapc` | halt | timeout | none |
| 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB, `Map.lean` `f` | halt | timeout | none |
| 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC, `Map.lean` `f` | halt | timeout | none |
| 1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA, `Map.lean` `next` | halt | timeout | none |
| 1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---, `DeepMindMap.lean` `next` | halt | timeout | none |
| 1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB, `DMMap.lean` `next` | halt | timeout | none |
| 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE, `Round.lean` `next` | halt | timeout | none |
| 1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC, `Round.lean` `next` | halt | timeout | none |
| control: `orbit_dom` of 1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA | `small` | **found in 11 s**: a even, a ≥ 4, c ≥ 6 (the statement of `orbit_dom`) | found (M = 2) |
| control: `Good` of 1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA | `stuck` | **found in under 1 s** | found (M = 1) |
| control: `Valid` of 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE | invalid state | **found in under 1 s** | found (M = 1) |

Each transcription was checked by running it 300 steps from the start (one rule applies at each step, no halt).
Not transcribed: the other 37 maps of `holdouts/reductions.json`. Their summaries describe the same kind of halting
set (see below), so the same outcome is expected; that is a prediction, not a run.

## Why nothing is found

The survey's premise was that the rule tables are over-approximations in which an inequality could be inductive, as
in busycoq PRs 97, 110 and 113. The maps we have in Lean are the opposite: **exact** reductions (`halts_iff`), made
after the machine was understood, and all 45 in `reductions.json` are Collatz-like. Their halting sets are thin and
arithmetic: a difference in a window of width 4 after tripling (c − a = 10 or 12), "p + 3 is a power of two", a
counter with upward drift hitting 0 on one residue (the Antihydra shape). An invariant excluding such a set must
describe the orbit's residues to every modulus, which no linear-plus-congruence invariant does; for
1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA Lean even proves that no congruence up to 10,000 works. So a timeout
here is the expected answer, not a weakness of the solver: the controls show that where a linear or congruence
invariant exists, both tools find it at once.

For the first target, 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC, the folder already contains the obstruction in
Lean: every set of walls closed under both parities contains the family 1 K(0) K(9i + 7), whose safety depends on
the binary digits of a 2-adic number (`closed_family`), and the 5× ratio bound is not inductive
(`ratio5_not_enough`). Spacer on the list-datatype encoding does not get past this.

The survey's other targets were read with the same question (is the missing statement linear or congruence
arithmetic on finitely many counters?). It is not, for any of them:

- 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF and 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---: what is missing is
  that each round's defect dies, a statement about the digits of an unbounded counter.
- 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: the rebuild map is r′ = 2^k′ − 2^(m−3J+2) + 2⌊r/8^J⌋ − 1 + e(w), with J read
  off the low bits of r by a 7-state automaton and e(w) about 2^(4.5J): a queue of bits with an addition, not a
  counter program.
- 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- and 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---: the equation
  m + 1 = (2D + 1)·2^s is between bit strings of unbounded length.
- The four odometers and 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---: the state is an unbounded list of blocks; no
  counter program exists yet.

## What this says about the technique

Solvers are cheap and do work on the right input, but the input has to be an **over-approximate** counter program
of a machine whose halt needs one quantity to be small (survey shape N3), and making that program is the hard
step. Two places where it could still pay:

1. As the back end of technique B (summary certificates with an abstract tail): once excursions are summarised as
   guarded affine updates with unknown tails, the closure question is a Horn problem of the kind the controls show
   Spacer solves instantly. `spacer.py` takes such rules as they are.
2. As a routine replacement for the hand-written "never stuck" lemmas (`Good`, `Valid`, `orbit_dom`) when a new map
   is put in Lean: ask Spacer for the domain invariant, then check it with `omega`.
