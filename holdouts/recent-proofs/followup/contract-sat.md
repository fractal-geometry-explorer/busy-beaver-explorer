# Contract tables found by a SAT solver: first test (27 November 2026)

This is technique A of [`../technique-brainstorm-2-nov27.md`](../technique-brainstorm-2-nov27.md). The proof object
is the one stated at the end of [`write-only-test.md`](write-only-test.md): classes of half tapes, a map φ that reads
a half tape from its far end, and for each class and entry state the set of (return state, class afterwards). Here
the classes are not learned. A SAT solver is asked for any table that is closed and from which no halt can be
derived, so it is free to merge tapes that behave differently.

**Result: the encoding works, it is exact, and it found nothing. No machine was decided. The first test of the
brainstorm note (recover a table for the machine DeepMind proved) did not succeed, so by that note's own rule the
technique stops here in this form.** Everything below is computed. The "no table" statements are UNSAT answers of
the solver and were not checked by a second tool; the tables it does find (on control machines) pass an independent
checker.

Tools and raw results: [`../tools/contractsat/`](../tools/contractsat/).

## The short version

- **The search is exact and fast for small tables.** With up to 8 classes over raw cells, one direction of one
  machine takes about 3 seconds. Positive controls work: non-trivial 4-state machines get tables with 3 to 6 classes.
- **No open holdout has a small table.** For all 1,002 directions of the 501 open holdouts there is no table with
  8 classes and an exact window of 12 cells at the other end (`screen-n8-w12.tsv`; 54 minutes of processor time).
  A smaller table or window is a special case, so this covers everything up to that size.
- **The four targets have none with 10 to 13 classes over raw cells (window 12), and none in larger structured
  families**: classes of the form (automaton state, length
  of the leading run), with up to 5 automaton states and runs up to 4 (27 classes), runs of zeros or of ones,
  windows 8 and 16.
- **The proved machine 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE was not recovered.** Over raw cells there is no
  table with 8 classes (window 12) or 10 classes (window 1). With the proof's tokens built in (automaton state
  times a run of 0 to 3 zeros) there is none with 5 or 6 automaton states and a window of 24 cells, nor with 6 and a window of 32, inside the
  window situations of a real run. The run with 7 states did not finish in 110 minutes.
  Each further automaton state costs about a factor 12 in solver time (36 s, then 446 s), so 7 is at the edge.
- **Why it does not scale, in one sentence each.** A wrong table with a narrow window is refuted at once, because
  the whole problem is in front of the solver. With the wide window the proof needs (its end words are up to 45
  cells long), a wrong table reaches a halt only after a very long path, more than 200,000 window situations away,
  so the solver gets almost no information per round. Restricting the window to the end words of a real run makes
  the problem finite again, but the solver time then grows about twelvefold with each automaton state.

## The proof object as constraints

Mirror the machine if needed so that the abstract side is on the right.

- **Classes.** n classes of half tapes; class 0 is the blank one. φ(c, q) is the class of "cell c followed by a half
  tape of class q", and φ(0, 0) = 0.
- **Contracts.** R(q, s, s', q'): the head enters a half tape of class q in state s on its first cell, and comes
  back out in state s' leaving a half tape of class q'. An auxiliary T(c, q, s, s', p') says the same for the head
  standing on a cell c in front of a half tape of class q.
- **Closure**, for every cell c, class q and state s:
  - if the machine moves left on (s, c), writing w and going to s3: T(c, q, s, s3, φ(w, q));
  - if it moves right: R(q, s3, s4, q2) and T(w, q2, s4, s', p') give T(c, q, s, s', p');
  - T(c, q, s, s', p') gives R(φ(c, q), s, s', p').
- **Reachable calls.** C(c, q, s) marks the situations inside calls that can occur. A call on φ(c, q) marks
  (c, q, s); a right move marks the call it makes and every situation its returns lead to. No marked situation
  may be a halting one.
- **The top level.** A window of W exact cells starts at the left frontier of the tape (blank to its left). Beyond
  it the tape is known only by its class. A step out of the right end of the window is a call answered by R. When
  the head moves the frontier, the window slides left and the cell that drops out on its right is absorbed by φ.
  No window situation may halt.

The table need not be the least one: any closed table without a halt is a certificate. Soundness is the budget
induction of the hand proofs (a call that returns within k steps returns as R says, because the calls inside it are
shorter).

Two things about this object that the earlier SAT search (16 November, closed regular languages of whole tapes) did
not have: the left context of a call is not described at all, because it comes back untouched; and the window keeps
the regular end exact without spending automaton states on it.

**The window is encoded lazily.** A window situation gets a variable and its clauses only when a model reaches it.
After each model, the program computes the least table for the model's φ and searches the window graph breadth
first for a halt; the shortest path to one becomes clauses. An UNSAT answer is still exact for the given n and W.
Symmetry between classes is broken by numbering them in breadth-first order of φ.

**Structured classes** (`--runs b,Z,D`). A class is a pair (d, z): an automaton state d and z leading cells equal
to b, with z at most Z. φ on a cell b only counts; φ on the other cell is the unknown and always lands on z = 0.
One extra class is a sink. This is the shape of the proved machine's proof (tokens `1`, `01`, `001`, `0001`, a
7-state automaton) and leaves only D·(Z+1) unknown entries.

**Real-run restriction** (`--keys`). `keys.c` lists the window situations of a real run. With this option any other
window situation counts as a failure, and the whole window graph is given to the solver at the start. A table found
this way is a full certificate. "No table" then only means: none whose window graph stays inside what the real run
shows.

## Checks

- `check.py` verifies a certificate without using the encoder: closure of R and T, no halt among marked situations,
  and the window graph. Every table found below passed it.
- `sanity.py`: random 3-state machines that run 2,000 steps; all tables found pass the checker and none of the
  machines halts within 300,000 steps.
- `controls.py`: random 4-state machines starting `1RB` that spread over at least 12 cells and are not decided with
  2 classes. 17 of 18 get a table with 3 classes and window 4, and one needs 6 classes and window 8
  (1RB0RC_1LD0LA_1RA---_0LC0LB: 13 window situations, 29 contract facts).

## Results

### All open holdouts, 8 classes, window 12

`screen.py` on the 1,002 directions of `../tools/writeonly/calltest-screen-nov27.tsv`. Every one is UNSAT. The
median run takes about 2 seconds, the longest 144 seconds, the total is 54 minutes on one core. Since a table with
fewer classes or a narrower window can be padded to this size, no open holdout has a contract table with at most 8
classes and a window of at most 12 cells, in either direction.

### The four targets

| machine | abstract side | raw cells, window 12 | structured (b, Z, D), windows 8 and 16 |
|---|---|---|---|
| 1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA | left | none with up to 11 classes | none for b = 0 or 1, Z = 2 or 4, D = 2 to 5 |
| 1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA | left | none with up to 13 classes | none, same settings |
| 1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA--- | left | none with up to 11 classes | none, same settings |
| 1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA | left | none with up to 13 classes | none, same settings |

The learner of the write-only note predicted the return *states* of these four with 5, 11, 26 and 76 classes. A
contract table also has to say which class comes back, without a derivable halt, and that needs more than 10 to 13
classes if it exists at all. The time per run grows quickly here too: for the first machine 5 s, 29 s and 392 s
for 9, 10 and 11 classes.

### The proved machine 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE (abstract side: right)

| classes | window | restriction | answer | time |
|---|---|---|---|---|
| 8, raw cells | 12 | none | no table | 65 s |
| 9, raw cells | 12 | none | not finished | stopped after 400 s |
| 10, raw cells | 1 | none | no table | under 5 minutes |
| D = 7, Z = 3 (30 classes) | 48 | none | did not converge: every model's window graph passes 200,000 situations without a halt | stopped after 100 rounds |
| D = 5, Z = 3 (22 classes) | 24 | real-run keys (350) | no table | 36 s |
| D = 6, Z = 3 (26 classes) | 24 | real-run keys (350) | no table | 446 s |
| D = 7, Z = 3 (30 classes) | 24 | real-run keys (350) | not finished | stopped after 110 minutes (longrun job `…-contractsat-D7-W24`) |
| D = 6, Z = 3 (26 classes) | 32 | real-run keys (1,316) | no table | 2,967 s (longrun job `…-contractsat-D6-W32`) |

The window situations of a real run of 10^9 steps: 101 for W = 16, 350 for W = 24 (both complete after the first
quarter of the run), 1,316 for W = 32 (complete after the third quarter), 15,190 for W = 48 (still growing).

Why the proof's "7 classes" is not what this object needs: the 7-state automaton of the proof is only the
invariant of the right list. The contract of the proof (`callRA_advances`) is stated for one kind of call, with a
parity of ones that straddles the boundary and a return set of three shapes, and the proof handles the tape
between two such calls by exact macro steps. A table that is closed at *every* cell boundary has to carry all of
that in its classes, so it is larger than 7 by an unknown factor.

## What this says about the technique

1. Stating the proof object as constraints is easy and the solver handles the "merge freely" part well. For up to
   about 10 unstructured classes the answer comes in seconds to minutes, and it is exact.
2. At that size nothing exists, for any open holdout. This is a real negative result: contract tables are strictly
   stronger than the closed regular languages of the 16 November search (a call's left context is unconstrained and
   comes back intact), and they still do not reach these machines when small.
3. The one known proof of this kind needs a table that is closed only at chosen call points and exact in between.
   Our object, closed at every cell, is the simplest one to encode and it is too fine. The next version should let
   calls start only at token boundaries chosen per machine (the turn points), which is what the two sibling
   attempts (end-word classes, tokens first) explore by learning.
4. The lazy window is the bottleneck for wide windows, and the real-run restriction is the right fix for it. What
   remains hard is the number of classes.

## Reproduce

```sh
cd holdouts/recent-proofs/tools/contractsat
pip install python-sat
python3 contractsat.py 1RB0RC_1LD0LA_1RA---_0LC0LB L 6 8 --sym --out c.json && python3 check.py c.json   # a control
python3 screen.py ../writeonly/calltest-screen-nov27.tsv 8 12 0 1 out.tsv                                 # the screen
gcc -O2 -o keys keys.c
./keys 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE L 24 1e9 > keys_24.txt
python3 contractsat.py 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE L 0 24 --runs 0,3,5 --keys keys_24.txt
./targets.sh targets.txt                                                                                    # structured runs
```
