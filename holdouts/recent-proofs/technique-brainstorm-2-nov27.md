# Second round of technique ideas (27 November 2026)

Round one is [`technique-survey-nov26.md`](technique-survey-nov26.md). Its eight proposals were all tried within a
day and decided nothing, and the two follow-ups to cryptids pull request 42
([`followup/write-only-test.md`](followup/write-only-test.md), [`followup/return-shape.md`](followup/return-shape.md))
decided nothing either. This note proposes nine further techniques, ranked, with target machines and a cheap first
test for each. **Nothing in it is computed or proved. Every odds figure is a judgement.**

## What the first round taught, in four lines

1. **Learning from behaviour over-refines.** Classes that predict what a trip returns are few (5 to 184), but
   counterexample refinement splits them without end, because any two irregular tapes differ sooner or later. The
   proofs stop because they accept "returns in one of three shapes".
2. **Our counter programs are exact, and exact maps are Collatz-like.** Solvers find inequalities at once on
   over-approximate programs (the three controls of [`followup/horn-solvers.md`](followup/horn-solvers.md)) and
   nothing on exact ones. Nobody has made an over-approximate program by machine.
3. **Forward searches do not know where the halt is.** Every search that failed computed forward and checked for the
   halt at the end.
4. **Screens of all 501 by a signature find regular ends, not proofs.** The signature is common and the proof is rare.

The proposals below each answer one of these lines.

## Ranking

| rank | technique | answers line | cost | odds of a decision | targets |
|---|---|---|---|---|---|
| 1 | A. Contract tables found by a solver | 1, 3 | small to medium | medium | about ten "chaotic" machines |
| 2 | B. Contrast the copies that halt with the copies that merge | 2 | small | low to medium | 2 to 8 machines with proved maps |
| 3 | C. Counter programs made from pattern counts | 2 | small to medium | low to medium, but broad | all 501 as a screen; F08, R08 first |
| 4 | D. Read the big counters as digit strings | 2 | small for the look | low, but 45 machines at once | R01, R04, R11, the four odometers |
| 5 | E. Return shapes over counted tokens | 1 | medium | low to medium | 2 named machines, then the 105 stopped by limits |
| 6 | F. Three cheap screens of the 45 proved maps | 2 | small | low | the maps of `reductions.json` |
| 7 | G. Particle tables for sweep maps | 4 | medium | unknown | F11 (46 machines), R05, R14 |
| 8 | H. Backward search that always stops | 3 | medium | low | N3-like machines |
| 9 | I. Invariants with exponential weights | 2 | medium | low | R04, R07, R12, F03 |

## A. Contract tables found by a solver, with "no halt" as a constraint

**Idea.** The last section of the write-only note states the proof object exactly: a finite set Q of classes of half
tapes, a function φ(cell, class) that reads the half tape from its far end, and for each class and entry state a
set of (return state, class afterwards). It then tries to *learn* Q from the run, and the learner over-refines
(line 1). Do not learn it. Ask a solver for it. For a fixed size n, the conditions "φ and the tables are closed
under one cell, and no halt is derivable from the start" are a propositional formula in the unknowns φ and the
table bits. The tables need not be least: any closed table without a halt is a certificate. A SAT solver or a
finite model finder (the first-order statement "there is a model of these Horn clauses of size n" is what Paradox,
Mace4 and Vampire's finite model builder search for) then picks whichever classes make the halt unreachable. It is
free to merge tapes that behave differently, which is what the hand proofs do and what a behaviour learner
cannot.

**Why it is not a repeat.** The SAT search of 16 November looked for a closed language of *whole tapes* on raw
cells. This one looks for contracts on half tapes, which is the format in which the two DeepMind proofs are small
(7 classes over 4 tokens; 5 nonterminals over 10 run lengths) and in which the same invariant as a tape language
needs about a hundred states.

**The known obstacle and the way round it.** The first DeepMind machine needs 132 exact words at its regular end,
too many for a model of small size. So make it two-sided and lazy: the regular end is explored exactly by a
program in the style of `checkSym`, and only the far side is abstract. The solver proposes (φ, tables) that agree
with every trip recorded in a real run. The explorer runs the near end against them. If it derives a halt, the
derivation becomes one clause ("these table entries cannot all hold") and the solver is asked again. For fixed n
this loop ends, with a certificate or with "no table of size n".

**First test.** It must return a 7-class table for 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE over the proof's tokens,
and a table of modest size for 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF. If it cannot, stop.

**Targets.** The four open machines whose return states were learned with few classes:
1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA (5 classes), 1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA (11),
1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA--- (26) and 1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA (76). Then the other
"chaotic" directions among the 41 that passed the test at every boundary.

**Cost.** A few days: an encoder, the explorer (parts exist in `tools/writeonly/`), solver time. A Lean checker only
if a table is found.

## B. Contrast the copies that halt with the copies that merge

**Idea.** The halt-hunt note found something it did not use. For 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE the
estimate predicted about 340 halts among 1,000 perturbed copies and 49 happened; 400 copies ended on only 3 orbits
and not one halted after visit 2^19. So the orbits everything merges into carry a property that fresh
perturbations lack, and that property keeps them away from the halt. Find it. The ensemble gives labelled data
for free: states that halt soon, and states on the merged orbits. Fit the simplest predicate that separates them
(a shallow decision tree over residues, differences and ratios of the counts, and low digits), test it on fresh
copies, then try to prove that it is preserved by the map and excludes the halting case.

**Why it is not a repeat.** The residue and solver searches looked for an invariant of the map from the blank-tape
orbit alone. A single orbit cannot say which of its features matter. The contrast with near misses can.

**First test.** One afternoon with `tools/segreplay`: does any predicate of depth 3 separate the two sets on
held-out copies with fewer than 1% errors? If not, stop.

**Targets.** 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE first (the gap between estimate and count is largest), then
1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD (2.9 hits expected so far, none seen), then the five machines of that
note whose rate drops when parities are kept: 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE,
1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE, 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD,
1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE and 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE.

**Risk.** Merging may be a fact about the perturbation (small moves die out in the high digits) and not about the
halt. The first test shows which.

## C. Counter programs made from pattern counts

**Idea.** The Horn solvers need an over-approximate counter program and we have only exact ones (line 2). Here is
one that exists for every machine without understanding it. Describe a tape by the head state, a small exact
window around the head, and two vectors of numbers: how often each n-cell pattern occurs left of the window and
right of it. One machine step changes the window and moves one pattern from one vector to the other; which pattern
arrives is any one whose count is positive and that overlaps the window correctly. That is a counter program with
nondeterminism. It forgets the order of the patterns and keeps their numbers, so it is strictly finer than n-gram
CPS, which keeps only which patterns occur. Hand it to Spacer and to a polyhedra-with-congruences analyser, and
check any invariant they return in Lean with `omega`.

A second form works on run-length tokens: the counters are the lengths of the few longest runs on each side, and
the counts of short runs. Proofs such as "c ≤ G" (busycoq PR 113) and "2p ≤ 3g + 3" (PR 110) are statements in
this vocabulary.

**First test.** The machines of busycoq PRs 97, 110 and 113 and 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- (where
the fact is "k ≥ 42 for any tail") must come out. If none does, the abstraction is too coarse and the idea is dead.

**Targets.** As a screen, all 501. First by hand: the 39 "counter beside a chaotic edge" machines of F08, the ten
reservoir counters of R08, and 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB--- (frozen blocks and one block growing about
1.4 times per sweep).

**Cost.** An exporter in C++ and solver time. The number of counters grows as 2^n per side, so n stays at 3 to 5,
or the token form is used.

## D. Read the big counters as digit strings

**Idea.** In the base-5 family R01 (45 machines, 23 questions) a halt needs a drift b(i+1) − 5·b(i) within a few
hundred of 0, where the blocks have hundreds of digits. We treated the block sizes as numbers and concluded that
the drifts "behave like differences of unrelated large numbers". They are not unrelated: every block is made from
earlier blocks by multiplying by 5 and adding. Written in base 5, multiplying by 5 is a shift and adding two
numbers of very different size is close to gluing two strings together. So the digit strings of the blocks may
have a simple description (a few rewriting rules on strings), and "the drift is small" becomes "the digit string of
the drift is all zeros, or all fours, above its last four digits". That is a statement about strings, where a
regular invariant ("some digit in the top third differs") may hold when no congruence and no ratio bound does.

**Why it is not a repeat.** The automatic-streams attempt treated the *stream of carry lengths* as an automatic
sequence. The level grammars described the *tape*. Neither looked at the digits of the block sizes.

**First test.** Half a day: print the 599 drifts of 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA--- in base 5 next to the
blocks they come from and look for shared substrings. If the strings look random, stop.

**Targets.** R01; the four odometers that ran far without halting (1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---,
1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD, 1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---,
1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD---); the base-4 counters of R04 and the ternary ones of R11 in bases 4 and 3.

## E. Return shapes over counted tokens

**Idea.** The return-shape learner failed on its best candidate, 1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA, because
that tape has blocks of period 16 whose repeat counts grow, and the learner's tokens are single runs. Give it
tokens of the form w^n with a count that is "exact if small, else at least c and a residue", as the accelerated
simulators have. A call that crosses w^n is then one step with a parametric result, and a contract can say "returns
with n + 1". This joins the two proof shapes that have worked separately: recursive sweeps (shape N4 of the survey)
and laps on linear forms (shape N2).

**Targets.** 1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA and 1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD (stretches of
`(1 0)^n` whose counts change). It should be built together with the port to C++ that the return-shape note already
asks for, so that the 105 machines stopped by limits get an answer.

## F. Three cheap screens of the 45 proved maps

The maps in `reductions.json` are parked as Collatz-like after tests on about a dozen of them. Three tests that take
minutes per map would sort all 45:

1. **Backward tree.** Compute the states that reach the halting set in 1, 2, 3, … map steps, as parametric
   families. If the tree dies, or leaves the set of states the proved domain invariant allows, the machine is
   decided. For maps that multiply by 3/2 every state has predecessors, so this fails; for maps with a growing level
   or two coupled counters nobody has looked.
2. **Forbidden branch words.** List which sequences of branches of length up to 12 are possible at all (a
   congruence check). For 3/2 maps every sequence is possible. If some map forbids sequences, weight each branch
   by its effect on the quantity that must be small for a halt and compute the worst average over the allowed
   sequences. A positive worst case is a proof plan.
3. **Equality halts with closed forms.** Several maps halt only on an equation between two counters:
   1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE (i = j or i + 1 = j), 1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD
   (u = v or u = v + 1), 1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE (r = p + 1),
   1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC (c = 0 and 2u = v) and 1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA
   (c − a = 10 or 12). Where both counters have closed forms in powers of fixed bases over long stretches, the
   equation is an exponential Diophantine equation, and those have finitely many solutions that lattice reduction
   can list. This needs the branch path to be regular, which must be checked per map.

The most likely outcome is that all 45 stay parked, but then for a recorded reason on each.

## G. Particle tables for sweep maps

**Idea.** F11 (46 machines, "defect gases, particle seas") has no technique at all. The crossing-sequence work
showed that one sweep is an exact finite transducer when the carries are bounded. For such a machine the
sweep-to-sweep map is a cellular automaton in all but name, and the standard way to understand one is to find its
background patterns and the particles (defects between backgrounds) with their speeds and their collision table.
A halt is then one collision outcome, and non-halting can follow from an order argument: particles sorted by speed
never meet again, or a count of one particle type has fixed parity.

**First test.** Take the three machines on table T27 (1RB---_0RC1RC_1RD0LE_1RE0RB_1LF0RA_1LC1LF,
1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---, 1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---): filter out the most
frequent background from tapes at successive turns and see whether what remains is a finite set of moving
objects. If more than a few dozen objects appear, the picture is wrong for that table.

**Targets.** F11, the non-additive members of R05, R14.

## H. Backward search that always stops

**Idea.** Search backward from the halt (line 3) in a setting where the search must end. Order configurations of
the macro machine by "same shape, each count at least as large and equal modulo p". Under this order every
infinite set has two comparable members, so the backward search, which keeps only minimal elements and adds the
upward closure of each predecessor, ends after finitely many rounds. The result is a superset of the states that
can halt. If the start is outside, the machine never halts. Precision is set by p and the threshold, and each
setting ends, unlike class refinement. For tapes without counts the same works with the order "obtained by
inserting blocks of L cells", which is also well behaved.

**First test.** The controls of C. A proof like "the halt needs the count below 42 and the count never drops"
is exactly a backward search that stops after a few rounds.

**Risk.** The upward closure assumes that more of the same is harmless. For Collatz-like machines it is not, and
the search will swallow the start. Expect this to work only where shape N3 works.

## I. Invariants with exponential weights

The community's weighted automata (WFAR) give each tape a number by *adding* weights along it, which expresses a
difference of two counts. They cannot express the value of a binary counter, or "this counter is at least five
times that one", because those need weights that multiply. Matrix interpretations, the main tool of automatic
termination provers, do: each cell and the head become small matrices of natural numbers, a tape is their
product, and a rule is safe when the matrix of its left side is entrywise at most that of its right side. Finding
matrices of dimension 2 to 4 is a routine SMT problem. The invariant would be "the value of the tape never falls
below its start, and every halting configuration inside the regular frame has a smaller value".

**Targets.** Counters with timers (R04), two counters with rebuilds (R07), two-word sweepers (R12), binary counters
with markers (F03). **Risk.** A halt is a local pattern, and a value of the whole tape rarely excludes a local
pattern without a second, regular invariant beside it.

## One change of method

Every screen of all 501 machines has returned zero decisions, and every DeepMind proof was a close reading of one
machine. Technique A is the only item above that tries to automate that reading. Beside it, it would be worth
giving two or three threads one machine each from the "41 passing directions" list with the instruction to write
the contracts by hand in the vocabulary of pull request 42 (tokens cut at the turns, what a call returns, which
side decides), with a fast falsifier that tests a proposed contract against 10^9 steps of the run.

## Suggested order

1. B and F at once: both are a day or less and need no new tool.
2. A, with its first test on the two DeepMind machines.
3. D's half-day look, then C with its controls.
4. E when the return-shape tool is ported. G, H and I as side experiments.
