# Write-only tails: a direct test on the 12 end-controller candidates, and on all 501 (27 November 2026)

This is follow-up 2 of [`../cryptids-pr42-nov27.md`](../cryptids-pr42-nov27.md). DeepMind's proof of
1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE works because one side of the tape is *write-only*: a trip into it
returns one bit, and that bit is known when the trip starts. The note's screen picked 12 open holdouts whose one
end shows few end records. Here the property itself is tested. Everything below is computed, not proved.
**No machine was decided, and none of the 12 has the structure of the proved machine.**

Tools and raw tables are in [`../tools/writeonly/`](../tools/writeonly/).

## The short version

- **The test works.** On the proved machine it passes at the left end and fails at the right end, as the proof says.
- **Of the 12 candidates, 5 fail**: the state in which the head comes back depends on the far part of the tape.
  One fails on a single end word. **6 pass, all for a reason that gives no proof**: five are block maps we
  already have in Lean, where the head always comes back in the same state and the open question is arithmetic
  (which block sizes occur), and one is a plain sweeper.
- **The end records of the earlier screen were the wrong thing to count.** A wall that a bouncer hits always the
  same way has few end records too. What the proved machine has in addition is that its trips are long and
  irregular (a trip of depth d takes about 460 d steps, not 2 d) and still return a known state.
- **A sharper test at every boundary of the tape** (not only at an end) separates both machines of cryptids pull
  request 42 from their own mirror images. 41 of the 1,002 directions of the 501 open holdouts pass it. Most are
  counters and Collatz-like maps we know; about ten are machines we call chaotic.
- **The return states can be learned.** An automaton with 13 states, reading the far side from its far end,
  predicts the return state of all 1.5 million trips in 3·10^6 steps of the first proved machine; 184 states do
  it for the second, and 5 to 76 for four open holdouts. This does not yet give a proof (last section but one).
- **Passing is not a proof, and the obvious automatic proof does not work.** A decider that describes the far
  side by its first K cells (`sumdec.py`) fails on *both* proved machines for every K tried, up to 64. Their proofs need
  classes of far sides that look ahead without bound (a parity of a long run, a grammar nonterminal). The last
  section says what a decider with such classes has to look like.

## The test at one end (`wotest.c`)

Mirror the machine if needed so that the tested end is the left end, and let E be the leftmost 1. For a window
width W, a **trip** starts when the head steps from cell E+W to E+W+1 and ends when it steps back. During a trip
the cells E..E+W cannot change and cannot be read. For each trip the program records

- the **key**: the state at the start and the cells E..E+W;
- the first K cells beyond the window at the start, for K = 0, 1, 2, 4, 8, 16, 32, 64;
- the depth (how far beyond the window the head went), the duration, and the state on return.

It then answers four questions.

1. Is the set of keys finite (the count after each quarter of the run)?
2. On deep trips, is the return state a function of the key and K cells? A trip counts as *ambiguous for K* if
   another trip with the same key and the same K cells came back in a different state.
3. Is the next key a function of the key and the return state? (It was, in every run: 0 conflicts.)
4. How long is a trip compared with its depth? A plain sweep takes about 2 steps per cell of depth.

### Controls

10^9 steps, W = 24, deep = more than 1,000 cells beyond the window.

| machine | end | tape | deep trips | steps per cell of depth | keys | return states | ambiguous, K = 0 | K = 8 | K = 64 |
|---|---|---|---|---|---|---|---|---|---|
| 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE | left | 31,385 | 282 | 459 | 181 | A D E F | 98 | 0 | 0 |
| 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE | right | 31,385 | 270 | 484 | 380 | A B E | 30 | 23 | 0 |

At the left end the return state is not fixed by the end word alone (98 of 282 trips), but it is fixed by the end
word and 8 more cells. This is the parity of the proof. At the right end 8 cells do not fix it; 64 cells do only
because a 64-cell context almost never repeats.

### The 12 candidates

Same settings. The last column is the verdict.

| machine | end | tape | deep trips | steps per cell | keys | return states | K = 0 | K = 8 | K = 64 | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC | left | 30,224 | 9,006 | 8.4 | 44 | A B C | 8,854 | 8,834 | 8,653 | fails |
| 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF | right | 35,695 | 10,673 | 7.1 | 43 | A B D | 10,555 | 10,531 | 10,387 | fails |
| 1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA--- | left | 73,886 | 3,169 | 7.5 | 30 | A D E | 3,115 | 2,904 | 2,034 | fails |
| 1RB0RE_1LC---_0RA0LD_1LC1LD_1RF0LA_1RC1RE | right | 22,364 | 9,700 | 6.6 | 33 | C E F | 6,445 | 6,439 | 6,405 | fails |
| 1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB | left | 29,676 | 3,302 | 18.4 | 70 | B D | 1,376 | 1,247 | 13 | fails |
| 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF | left | 42,921 | 6,329 | 8.8 | 17 | A C E | 570 | 570 | 570 | fails on one end word |
| 1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA | left | 55,260 | 7,112 | 5.1 | 96 | A C F | 2 | 0 | 0 | passes: plain sweeps |
| 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA | left | 3,611 | 5,241 | 100 | 62 | E | 0 | 0 | 0 | passes: one return state |
| 1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB | left | 6,720 | 1,769 | 228 | 48 | A | 0 | 0 | 0 | passes: one return state |
| 1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB | left | 6,578 | 1,335 | 317 | 111 | A | 0 | 0 | 0 | passes: one return state |
| 1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA | right | 4,708 | 2,596 | 188 | 41 | A B | 0 | 0 | 0 | passes: fixed by the end word |
| 1RB0LE_0RC0RD_1LC0RB_0RE1RD_1LF1LE_0LA--- | right | 5,348 | 2,819 | 168 | 39 | D E | 0 | 0 | 0 | passes: fixed by the end word |

**The five that fail.** For the first four, most deep trips are ambiguous whatever K is: the head brings a
bit back from the far side, and that bit is the content of the bulk. Their trips are short for their depth (7 to
8 steps per cell): these are sweepers, and each sweep reads the bulk it crosses.
1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB behaves like the *right* end of the proved machine: the return state
needs 64 cells.

**The one that fails on one end word.** 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF has 8 end words on deep
trips. Seven always give the same return state. The eighth (570 trips) gives two, and no K up to 64 separates
them.

**The six that pass.**

- Five are machines whose folders already hold a Lean reduction to a map on lists of block lengths:
  1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA (`halts_iff_8`), 1RB0LE_0RC0RD_1LC0RB_0RE1RD_1LF1LE_0LA---
  (`halts_iff`), 1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB and its sibling
  1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB, and 1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA. The head comes back
  to the tested end in one state, or in a state the end word fixes, so the end is a finite machine that runs by
  itself. But in these machines nothing is decided at that end. What decides the halt is the *length* of a block
  of 1s, which no window and no return state carries. For 1RB0LE_0RC0RD_1LC0RB_0RE1RD_1LF1LE_0LA--- the halt even
  happens at the tested end, when a carry that arrives there is a power of 2. The finite controller is real and
  proves nothing new.
- 1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA is a sweeper: at this stage of its run three full sweeps and four
  short trips repeat at the left end, with the same seven keys, and the tape grows by 22 cells per repeat. The
  return states are known because the left end is periodic. The halt (`B> 1 1`) can only happen inside the bulk
  during a sweep, where the method says nothing.

So the question of the note, "which end is the regular one", has a clear answer for all 12, and the answer does
not lead to a proof for any of them.

### All 1,002 ends (`wotest-screen-nov27.tsv`)

The same test on both ends of the 501 open holdouts (3·10^8 steps, deep = more than 256 cells; 975 ends gave a
result; 27 filled the program's table of keys and are not in the table). 65 ends have a saturated set of keys, at least two return states, a return
state fixed by the key and at most 8 cells, and trips of more than 20 steps per cell (`analyze_wo.py` lists
them). Read against our folders, most of them are block maps, counters and Collatz-like maps, like the five
above.

## The test at every boundary (`calltest.c`)

The end test only looks at trips that leave the end zone. The proofs of pull request 42 use more: a trip into a
tail returns a known value **wherever in the tape it starts**. That is what makes the induction on the step
budget work, since a long trip is made of shorter trips.

For a boundary between cells b and b+1, a rightward trip starts when the head steps from b to b+1 and ends when
it steps back. Trips nest, so one stack holds all open trips. For every trip deeper than 256 cells the program
records (start state, first K cells right of the boundary) and the return state, for K = 0, 2, 4, 8, 16, 32, 64.
Leftward trips are handled as the mirror image. The table gives the share of deep trips whose key has more than
one return state.

| machine | direction | deep trips | steps per cell | K = 4 | K = 8 | K = 16 (keys) | K = 32 |
|---|---|---|---|---|---|---|---|
| 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE | rightward | 3,196,248 | 281 | 1.000 | 0.037 | 0.0000 (299) | 0.0000 |
| 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE | leftward | 3,204,176 | 281 | 0.457 | 0.345 | 0.1223 (693) | 0.0109 |
| 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF | rightward | 33,422,102 | 16 | 0.687 | 0.215 | 0.0074 (171) | 0.0000 |
| 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF | leftward | 33,437,951 | 16 | 0 | 0 | 0 (466) | 0 |

In the first proved machine, 3.2 million deep rightward trips fall into 299 classes by their first 16 cells, and
every class has one return state. Leftward, 12% are still ambiguous. In the second proved machine rightward
trips are the calls of the proof (`BR l m R`), and leftward trips always come back in state B (the list to the
left is the untouched frame `l`).

The 12 candidates in this test, in the direction away from the tested end: the five that fail the end test fail
here too (share of ambiguous trips at K = 16 between 0.57 and 1.00, and 0.98 for the one that failed on one end
word). The six that pass have share 0 at K = 8 and at K = 16, with 19 to 236 classes.

**All 501** (`calltest-screen-nov27.tsv`, 3·10^8 steps): 41 of 1,002 directions have at least two return
states, more than 2% of deep trips ambiguous at K = 4, at most 0.1% at K = 16 with at most 2,000 classes, and at
least 8 steps per cell. The ones we do not already understand as counters or maps:

| machine | direction | steps per cell | K = 8 | K = 16 (keys) | our folder says |
|---|---|---|---|---|---|
| 1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA | leftward | 49 | 0.057 | 0.0000 (623) | alternating background with disordered defects |
| 1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA | leftward | 16 | 0.000 | 0.0000 (343) | chaotic two-sided bouncer, short runs |
| 1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE | leftward | 13 | 0.313 | 0.0009 (167) | conveyor with an irregular zone |
| 1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA--- | leftward | 12 | 0.000 | 0.0000 (110) | block list with carries (unclassified) |
| 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA | rightward | 12 | 0.500 | 0.0002 (97) | two-sided bouncer, a few counters in epochs |
| 1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA | leftward | 11 | 0.000 | 0.0000 (95) | bouncer over an irregular 10/01 domain gas |
| 1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD--- | leftward | 10 | 0.249 | 0.0003 (430) | few-block counter with defects |
| 1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD | leftward | 10 | 0.500 | 0.0001 (158) | two-sided bouncer, phases that roughly triple |
| 1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF | rightward | 9 | 0.249 | 0.0003 (469) | bouncer over 0111 blocks (chaotic) |
| 1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE--- | leftward | 9 | 0.248 | 0.0002 (454) | period-4/8 bouncer with a few drifting defects |

1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA was also on the run-grammar list of the note (strict form B, right
end). `analyze_call.py` prints all 41.

A warning about what this table means. A bouncer over a periodic background passes too: the state in which a
sweep comes back across a boundary depends on the phase of the background there, which a few cells show. The
"steps per cell" column removes plain sweeps (about 2) but not counters. The test is necessary for a
recursive-sweep proof and far from sufficient.

## An automatic proof attempt, and why it fails (`sumdec.py`)

If a call's return depends on K cells, the natural decider is this one. Describe the tape right of any boundary by
its first K cells, plus the promise that all its windows of K+1 cells lie in a set G. Every step to the right is a
call. A call (state, K cells) has a **summary**: the set of (state, K cells) with which the head can come back.
A summary is computed by running one cell exactly and using the summaries of the calls it makes, one cell further
right. The top level is the left frontier of the tape, with blank to its left. Summaries, G and the top-level
configurations grow together to a least fixed point. If no halting transition is reachable in it, the machine does
not halt (the argument is the budget induction of the proofs: a summary holds for a run of n steps because it
holds for the shorter runs inside it).

**It fails on both proved machines.** For 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF it finds a reachable halt
for every K tried from 4 to 64. For 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE it finds one for every K tried
from 2 to 32, and for K = 40, 48 and 56 it passes 2 million summaries without closing. The reason is in the
proofs:

- In 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE the bulk automaton (`dfaStep`) alternates between two states
  along a run of `01` tokens of any length. The class of a tail depends on the parity of that run, however long
  it is. And the near end has 132 exact words of up to 45 cells.
- In 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF the class of a tail is a grammar nonterminal, and
  `RareTail := {6, 8}* ValidR` looks through any number of runs of 6 or 8 ones.

A prefix of K cells cannot hold either. In our run the return *state* is fixed by 16 cells because long runs are
rare, but a proof has to cover every tape the description allows.

## What a decider for this class of proofs has to look like

Looking at one boundary at a time gives a compact statement of the method. Take the half tape right of a
boundary. It starts blank. It changes only during trips into it, and a trip is: the head enters in a state s,
and comes back in a state s' (or never comes back, or halts inside). So the half tape is a deterministic
**input/output machine**: inputs are entry states, outputs are return states, and its internal state is its
content. Every boundary of the tape holds a copy of the same machine, started from blank, fed with different
inputs. And the machine is self-similar: the half tape right of b is one cell followed by the half tape right of
b+1.

A recursive-sweep proof is then a finite object:

- a finite set Q of classes of half tapes, with a class q0 for the blank one;
- a function φ(c, q): the class of "cell c followed by a half tape of class q", with φ(0, q0) = q0. This makes
  the classes the states of an automaton that reads the half tape from its far end, which is how `evalR` reads the
  right list in the proof of 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE;
- for each class and entry state, the set of (return state, class afterwards);
- the check: for every class q and cell c, run the cell from each entry state, answering its calls from the table
  of q; every outcome (s', c', q') must be in the table of φ(c, q) as (s', φ(c', q'));
- the top level: the left frontier against the class of the rest of the tape, a finite graph with no halt.

Given Q and φ, the tables are a least fixed point, so nothing has to be guessed there; `sumdec.py` is the special
case where Q is the set of K-cell prefixes. The whole difficulty is Q and φ. In the two proofs they have 7
states over 4 tokens, and 5 nonterminals over 10 run lengths; our SAT searches for closed tape languages looked
for automata on raw cells with up to 8 states and a different acceptance condition (the whole tape, not a half
tape with a contract).

Two ways to get Q and φ that look feasible:

1. **Learn them from the run.** Every boundary gives a trace of the same input/output machine from the same
   start, so one run gives thousands of traces. Tails that answer the same way to the next few entries are
   candidates for one class; φ has to respect the merge (state merging on the tails read from the far end, as in
   the classical learners of finite automata). The check above then accepts or rejects, so a wrong guess costs
   nothing.
2. **Take tokens from the turns.** Cut the tape where the machine turns, as both proofs do, and run the K-prefix
   decider on tokens with run lengths capped and reduced mod 2. This gives the parity class of the first proof
   for free, but not the `{6, 8}*` look-ahead of the second.

A reflected checker for such a table (Q, φ, tables, top-level graph) would be the generic version of the proof's
`checkSym`: sound by one induction on fuel, then run by the kernel. It only becomes useful once a table exists,
so the learner comes first.

## Learning the classes: what works and what does not (same day)

Three programs test the plan above on the two proved machines.

**Return states are learnable, with very few classes** (`learncls.cpp`). A class is a row of an observation
table: the outcomes of a list of experiments "put the cells w in front, enter in state s" on a representative
tape. The real run is the teacher. When a trip comes back in a state its class did not predict, the tail is cut at
the first place where replacing its far part by the class representative changes the outcome, and the near part
becomes a new experiment (the counterexample rule of Rivest and Schapire). Over 3·10^6 steps, checking every trip
shorter than 10^6 steps:

| machine | direction of the trips | experiments | classes | trips in the run | fixed point: contracts, facts | real run: contracts, facts |
|---|---|---|---|---|---|---|
| 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE | rightward | 5 | 13 | 1,498,942 | 39, 76 | 38, 72 |
| 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF | rightward | 21 | 184 | 1,497,334 | 349, 989 | 195, 402 |
| 1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA | leftward | 5 | 11 | 1,499,161 | 43, 80 | 28, 37 |
| 1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA | leftward | 3 | 5 | 1,498,781 | 15, 30 | 14, 22 |
| 1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA--- | leftward | 5 | 26 | 1,498,277 | 50, 96 | 40, 59 |
| 1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA | leftward | 11 | 76 | 1,499,012 | 398, 2,746 | 220, 373 |

So an automaton with 13 states, reading the half tape from its far end, predicts the return state of every one
of 1.5 million trips of the first proved machine (the last wrong prediction is at step 32). For the second, 184
states do it, and the same 184 still do over 3·10^7 steps when only trips shorter than 10^4 steps are checked.
The last four rows are open holdouts from the table above.

**These classes do not yet give a proof.** In every row the summary fixed point derives a halt. For the first
machine the fixed point has only 4 facts more than the real run shows, and still a halt is derivable. The
classes predict the return *state*; the proof also needs the class of the tape that comes back to be precise
where it matters (near the left end, 132 exact words) and loose where it cannot be precise (the bulk, "one of
three shapes").

**Refining by counterexamples splits classes without end.** `lsum_cegar.cpp` replays the derivation of the halt
on concrete tapes; where the replay leaves the derivation, two tapes of one class behave differently and a new
experiment separates them. In a first variant, with representative tapes as witnesses, the first machine has
14,174 classes after 60 rounds. With tapes of the real run as witnesses, and the abstraction limited to compositions the real run shows,
it has 21,560 classes after 1,740 rounds, 15,408 of them used by a run of only 300,000 steps: the refinement is
drifting towards one class per tape. That is what one should expect. Any two different tapes of an irregular
bulk behave differently sooner or later, so a rule that separates every such pair never stops. The proofs stop
because they accept "returns in one of three shapes" as an answer.

What is still missing is therefore one specific thing: a refinement rule that splits a class only when the
difference decides the halt. Two candidates: split only classes whose tapes are short (the end words), and keep
the 13 or 184 learned classes for the rest; or cut the tape into the proof's kind of tokens first, so that the
bulk needs no splitting at all.

## Reproduce

```sh
cd holdouts/recent-proofs/tools/writeonly
gcc -O2 -o wotest wotest.c && gcc -O2 -o calltest calltest.c
./wotest 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE L 1000000000 1000      # end test, about 15 s
./calltest 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE 300000000 256         # every boundary, about 5 s
python3 sumdec.py 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE L 8,16,24      # the K-prefix summary decider
python3 triptrace.py 1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA L 3e6 2.6e6 4 40   # the trips at one end, one per line
python3 analyze_wo.py wotest-screen-nov27.tsv ; python3 analyze_call.py calltest-screen-nov27.tsv
g++ -O2 -std=c++17 -o learncls learncls.cpp && g++ -O2 -std=c++17 -o lsum_cegar lsum_cegar.cpp
LEARN=3000000 ./learncls 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE L 0 100 300000 2000000 200000   # 13 classes
./lsum_cegar 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE L 300000 20000 3000 30000              # diverges, stop it by hand
```
