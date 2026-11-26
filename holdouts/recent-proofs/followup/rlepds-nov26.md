# Summary certificates with an abstract tail: a finite-state attempt (26 November 2026)

This is the follow-up to technique B of `../technique-survey-nov26.md`: build, automatically, the kind of
certificate that cryptids PR 37 uses for 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---. **It decides no machine.** It
gives a tool (`tools/c/rlepds.cpp`), a soundness record, and a precise reason why the finite-state version of the
idea stops short of PR 37.

## What was built

`tools/c/rlepds.cpp` is a different design from `tools/py/lemcert` (PR 601). That tool carries symbolic linear
counts and lost them at lemma boundaries ("bound decay"). This one has no symbolic counts at all, so nothing can
decay:

- One side of the tape is the **stack of a pushdown system, kept exactly**.
- The other side is **abstract**: its K nearest items, then a tail that is BLANK or ANY. An item is a run of one
  symbol or a repeated pattern of runs such as `[0^2 1]^n`. A count is exact below a threshold E, and above it a
  lower bound with a residue ("at least c, and c mod M"), capped at T.
- The reachable set is computed with **procedure summaries**. An entry is "this cell was pushed in this control
  state"; its exits are the control states in which the cell is popped again. A summary reads: from this context,
  whatever lies deeper on the stack and for every tape the abstract side stands for, the excursion never returns
  or returns in one of these states. That is the statement of a PR 37 certificate node, and the untouched deeper
  stack is its frame.
- Inside one path set, a state is dropped when a weaker one (same shape, smaller lower bounds) is present.
- `start=N` analyses from the real configuration at step N; `forget` replaces the abstract side by ANY; `ctx=D`
  lists the ways an excursion leaves the D nearest stack cells (a tail-excursion summary on its own).
- `tools/py/rlepds_replay.py` replays an abstract path to a halt on a concrete tape and reports the first place
  where the abstraction had lost a fact. Every refinement below came from that report.

## Checks

- None of the 35 holdouts proved halting is claimed, in any setting tried (plain and mirrored).
- `selftest=N` follows the real run and checks that every real configuration lies in the reached set; it passes on
  the small machines tried, with and without subsumption.
- Power: it proves **none of the 64 holdouts already proved non-halting** from blank tape. So a negative result
  on an open machine says little.

## Sweeps of the 509 open holdouts

Ten sweeps, each over all 509 open holdouts, with a limit of 4 to 8 million path edges and 25 to 40 seconds a
machine. "Halt reached" means the abstraction reaches a halting transition, which says nothing about the machine.
The four sweeps from blank tape used the first version of the count classes (exact below T, then mod M).

| start | side kept exactly | K, P, slack | run lengths | repetition counts | halt reached | limit or timeout | proved |
|---|---|---|---|---|---|---|---|
| blank tape | left | 4, 2, 0 | exact below 4, mod 2 | exact below 4, mod 2 | 497 | 12 | 0 |
| blank tape | right | 4, 2, 0 | exact below 4, mod 2 | exact below 4, mod 2 | 502 | 7 | 0 |
| blank tape | left | 5, 2, 3 | exact below 6, mod 3 | exact below 12, mod 3 | 422 | 87 | 0 |
| blank tape | right | 5, 2, 3 | exact below 6, mod 3 | exact below 12, mod 3 | 409 | 100 | 0 |
| last right record before step 10^6 | left | 4, 2, 0 | exact below 4, mod 2 | exact below 3, bounds to 6, mod 2 | 491 | 18 | 0 |
| last right record before step 10^6 | left | 5, 2, 3 | exact below 9, mod 3 | exact below 4, bounds to 16, mod 3 | 392 | 117 | 0 |
| last right record before step 10^6 | left | 6, 3, 5 | exact below 6, mod 2 | exact below 3, bounds to 8, mod 2 | 397 | 112 | 0 |
| last left record before step 10^6 | right | 4, 2, 0 | exact below 4, mod 2 | exact below 3, bounds to 6, mod 2 | 503 | 6 | 0 |
| last left record before step 10^6 | right | 5, 2, 3 | exact below 9, mod 3 | exact below 4, bounds to 16, mod 3 | 406 | 103 | 0 |
| last left record before step 10^6 | right | 6, 3, 5 | exact below 6, mod 2 | exact below 3, bounds to 8, mod 2 | 406 | 103 | 0 |

At a record moment the whole tape lies on the exact side and the abstract side is blank, so these starts lose
nothing; they only skip the early part of the run. The three right-record sweeps ran without subsumption.

## Why 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- does not close

Started at step 85,284 (state A at the right edge of the counter, right tape replaced by ANY), the replay tool
showed four separate losses, each fixed in turn:

1. **Truncation before a pattern forms.** Four single runs must sit side by side before `[0^2 1]^2` exists, so
   K = 3 or 4 drops the far end first. The `slack` option fixes it.
2. **Exact counts below a large threshold multiply.** With "exact below 64", three runs give 64^3 values. Counts
   became lower bounds, and subsumption removes about 80% of the states.
3. **Lower bounds on single runs are too loose.** A zero-run of length 4 turned into "4, 7, 10, ...". Run lengths
   need PR 37's own classes (exact below 9, then mod 3); only repetition counts are lower bounds.
4. **What remains is the real obstacle.** During a round the counter is split three ways: the `110` blocks on the
   stack and two runs, `[0^2 1]^a` and `[0 1]^b`, on the abstract side. The round is safe only because a weighted
   sum of the three stays large (PR 37's "k >= 42"). A finite domain can hold thresholds on each count but not the
   sum, so it must enumerate the pairs (a, b), and every "the run was exactly as long as its bound" branch adds a
   cousin tape. With T = 64 the search passed 10^7 path edges and 2 * 10^6 abstract values without converging
   and without reaching a halt; with T small it reaches a halt, as it should, because small counters do decay.

So the finite-state part of PR 37 is the tail excursion (its nodes 576 and 577), and the round itself needs one
relation between unbounded counts, which PR 37 proves by hand (`loop_safe`). This matches the lemcert write-up
from the other direction: lemcert kept the relation and lost the bound at lemma boundaries; rlepds keeps every
bound and cannot express the relation.

## What this suggests

- A machine is in reach of this tool when the side that carries the unbounded counter can be the stack for the
  whole run, and the other side needs only thresholds. None of the 509 open holdouts passed in the settings
  tried, which agrees with the earlier negative results of `pdfar` and the regular-language deciders.
- The useful combination is: a symbolic round lemma with exact linear counts (lemcert's engine, or a hand proof as
  in PR 37), and this tool for the excursion into the unknown tail, called with `ctx=D forget`. On the PR 37
  machine that call did not finish within 2 * 10^7 path edges with the generic item window, so the abstract side
  also needs PR 37's coarser domain (one digit or one run of equal digits, then ANY) rather than K items.
- The over-approximate rules this tool explores (counts as lower bounds with residues) are the kind of input
  the Horn-clause back end of PR 603 can take; exporting one round of a machine as such clauses would let a
  solver look for the weighted-sum invariant that the finite domain cannot hold.

## Reproduce

```sh
g++ -O2 -std=c++17 -o rlepds tools/c/rlepds.cpp
./rlepds 1RB0LB_1LA0RA 4 2 3 6 2 3 6 2 selftest=100000                 # a small non-halter, with the self-test
M=1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---
./rlepds $M 5 2 9 9 3 4 64 3 slack=3 forget start=85284 limit=10000000  # LIMIT: no halt, no closure
ulimit -s unlimited; RLEPDS_SHOW=100000000 ./rlepds $M 5 2 9 9 3 4 4 3 forget start=85284 > path.txt   # small T: reaches a halt
python3 tools/py/rlepds_replay.py $M path.txt T2=4 E1=9                # first fact the abstraction lost
```

## Addendum: the hybrid, tried the same day

The combination suggested above was tried on 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---. One part works and one
does not. Still no machine is decided.

**Works: tail-excursion summaries.** `rlepds MACHINE 2 1 9 9 3 3 3 1 enter=Qh` starts in state Q on a cell h with
*every* tape to the right and nothing assumed on the left, and lists every way the head can come back to the cell
on the left. With an abstract side of two runs and no patterns (close to PR 37's own domain) the answer is small
and immediate:

| entry | result | ways back |
|---|---|---|
| A0, B0, C1, F0 | never halts inside | 13, 16, 13, 17 |
| A1, B1, C0, D0, D1, E1 | never halts inside | 1 or 2 (the first step turns back) |
| E0, F1 | a halt is reachable | these are the machine's two-step halting pattern itself |

Each way back is a state and the first cells of the rewritten tail, for example `D | 0^5 1 ANY` or
`A | 0^(>=9, = 1 mod 3) 1 ANY`. These play the role of PR 37's nodes 576 and 577, found in under a second. They
are computed by the tool and not checked independently.

**Does not work yet: the round as a counter program for Spacer.** `tools/py/roundchc.py` turns the machine into
guarded affine updates between tape *shapes* (single cells and repeated words `(w)^n` with integer counts), calls
the summaries when the head enters the unknown tail, and writes one Horn predicate per shape. The program is
faithful: `--check` follows the real run and the counter program side by side for 300,000 steps on two machines.
But:

- Without numbers the shape graph does not stay small, because every "this block has just one copy left" branch
  is explored and leads into the small-counter regime, which is the chaotic part. Budgets on the left side give
  9,283 shapes (2,512 predicates after merging chains) to more than 10^5.
- A walk on numbers (`--guide`, counters started at 48, 49, 50 and 133, every summary exit followed) cuts this
  down but does not close: 13,459 shapes after 3 * 10^6 numeric states, 1,918 predicates.
- Z3's Spacer ran out of memory (9 GB) on both the 9,283-predicate and the 1,918-predicate versions, with no
  answer.

What is missing is loop acceleration before the solver: a sweep across `(w)^n` is hundreds of shapes here and
should be one rule, which would leave a few dozen predicates. That is what lemcert's engine (PR 601) has, so the
practical next step is to give that engine the `enter=` summaries as its tail lemmas, in place of its own lemma
search, and keep its exact linear counts for the round.

```sh
./rlepds 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- 2 1 9 9 3 3 3 1 enter=A0      # 13 ways back, no halt
pip install z3-solver
python3 tools/py/roundchc.py 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- 85284 --keep-right --kr 100000 --check 300000
python3 tools/py/roundchc.py 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- 85284 --llit 14 --kr 3 --lpat 3 --lmax 3 \
        --guide 400000 --guidek 48,49,50 --no-solve                              # sizes only
```

## Second addendum: the summaries as tail lemmas of lemcert's engine

Done the same day, in `tools/py/lemcert/run_tail.py` (details in that directory's README). Still no machine is
decided.

- `rlepds` has a new option `lctx=BITS` for `enter=Qh`: the cells left of the entered cell. The exits are then the
  ways the head leaves that context to the left. With it, a walk of any length into the unknown tail is one
  summary, since the tape above the context is the pushdown stack. The calls stay small (about 400 path edges).
- lemcert's engine runs a whole round of 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- with exact linear counts and
  calls a summary whenever the head faces the bare unknown tail. The bound decay of the first lemcert attempt is
  gone, and the node shapes are a few dozen.
- It does not close. A two-run summary forgets what the excursion wrote, so in the abstraction a tail can take the
  counter down one unit per excursion for ever (41 nodes in a row, from 41 down to 1, and a spurious halt after
  602 nodes of 56 shapes). On the real machine the
  same step works once or twice and then stops. The missing piece is an exit that keeps `(001)^c` as one item.
- 12,800 sampled excursions of the real machine on random tails are all covered by the 64 summaries used.
- Digit-level exits were tried next (`digits` option of rlepds; `--sumargs` of `run_tail.py`). With one digit or
  digit run remembered the same spurious halt appears (541 nodes). With two, there is no verdict after 28 minutes
  and about 850 nodes, and the one-unit step is still present. A richer exit alone does not close the set; the
  node itself has to know that the cells right of the head were written by the machine.
