# Which proof techniques have decided holdouts, and what to try next (26 November 2026)

This note surveys every technique that has decided one of the 608 BB(6) holdouts, says what each one needed and
where it failed, and then proposes new techniques, ranked, with the machines each one targets. It is a reading of
what is already in this repository, in our busycoq fork and in the outside proofs we compiled. Nothing in it is a
new result. The proposals in part 3 are judgements, not findings.

Standing today: 99 of the 608 are recorded as decided here (64 never halt, 35 halt), and 509 are open. One of the
509, 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC, has a computed halt and a segmented Coq proof that is not yet in a
repository (shape H3 below). Of the outside proofs we
compiled, 38 machines are now merged in busycoq's BB6 branch.

## 1. What has worked

Every decision so far falls into one of eight shapes. The first three prove halting, the rest prove non-halting.

| # | shape | where it was used | what the machine must offer |
|---|---|---|---|
| H1 | **Verified fast simulator run to the halt.** Macro rules on run-length tapes are each proved sound; the proof assistant then evaluates the run. | busycoq PRs 59, 82, 84, 93, 100, 106, 111; ours: 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE, 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB, 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---, 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE | a halt within reach of the engine (up to a few million engine steps) |
| H2 | **Closed-form jumps.** Odometer ticks (b^k at once), countdown eras, memoised half-tape contexts, towers of walls. | PRs 81, 83, 88, 89, 91, 94, 105 | a counter whose drains have closed forms, and few distinct contexts per level |
| H3 | **Segmented replay with an untrusted guesser.** A fast program guesses the branch digits of a block of visits; a proved lemma says any guess whose formal run ends with large enough counts *is* the true run. The orbit is cut into checkpointed segments checked in parallel. | ours, not yet committed: 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC (8·10^13 visits, 400 segments); PR 60 (836 native jobs) is the same idea without the guesser | a proved visit map that is piecewise affine, and a halt too far for one evaluation |
| N1 | **Eventual regularity.** After an exact transient the run becomes a translated cycler or an exact bouncer. | PRs 43, 61, 62, 63, 95, 107; ours: 1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC---, 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA | a regime change into a fixed lap, however late (step 1.8·10^15 for the second of ours) |
| N2 | **Attractor on linear forms.** One fixed lap of macro steps maps C(N, m) to C(aN + b·s(m) + cm + d, m + k); a band invariant fixes every sign and parity the lap tests. | PRs 78, 79, 80, 86 | a lap whose branch path stops changing |
| N3 | **A weaker invariant than the orbit.** Only an inequality or a parity is tracked, and the exact (often Collatz-like) map is never followed. | PR 97 (wall capacity), PR 113 (potential c ≤ G), PR 110 (2p ≤ 3g + 3), PR 90 (fuel), PRs 92, 103; DeepMind cryptids PR 37 for 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- (only "k ≥ 42", for *any* tail) | a halt that needs one quantity to be small, and growth that keeps it large |
| N4 | **Recursive sweeps with a carry (assume-guarantee contracts).** The tape is a list of tokens; one sweep is a recursive call down the list; a small carry comes back from the far end; the invariant constrains only the front of the list. | PRs 112, 114, 115 to 119; cryptids PR 37's 578-node summary DAG is the same idea with an abstract domain in place of an automaton | tokens, and a carry with few classes (one bit, a residue mod 3) |
| N5 | **Closed finite set of round-end classes or token simulators with a hub.** | PRs 85, 87, 96, 104; ours: 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA (1,144 classes), 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC | a hub map that is total, with finitely many shapes around it |

Three things stand out.

1. **Halting proofs are all the same proof.** Prove macro rules, then compute. The only variation is how far the
   halt is and therefore how the computation is organised (one evaluation, closed-form jumps, or segments).
2. **The non-halting proofs that surprised us all track less than we did.** For 1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---
   we planned to chain exact phase maps; the proof needs one monotone budget. For
   1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- we listed 90,000 tail words and never closed; the proof handles every
   tail at once. For 1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA we treated the irregular zone as bounded noise; it is the front of a
   stack and the proof leaves the rest arbitrary.
3. **Nobody writes down a closed set of tapes any more.** The recent proofs use a step budget (`Safe k`) and strong
   induction, with contracts of the form "from this context, for any rest of the tape, the excursion either never
   ends or comes back in one of these forms".

## 2. What has failed, and on what

| attempt | machines | why it failed |
|---|---|---|
| Regular tape languages over raw cells (CTL, n-gram CPS, FAR, SAT-found automata up to 11 states a side) | all 558 then open | the invariant exists for some (PR 114's is regular) but needs about a hundred states; others depend on counter arithmetic |
| Transplanting busycoq's templates (139 copies for 81 holdouts) | the shift-overflow siblings | every copy stops at the second-overflow rule, which is exactly where the holdout differs |
| Reusing the PR 115 to 119 Coq core unchanged | all 509 | no holdout matches the segment machines; the closest tables are 4 transitions away |
| Wall-carry screen (a residue mod 3 at a fixed wall) | 1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE | false positive: the residues were the steps of one zigzag through a `1^8` block, each occurring once per lap. A signature without a mechanism is not evidence |
| Learning the PR 112 invariant with regular learners (k-tails, CEGAR, call signatures) | the eight chaotic bouncers listed in part 3 (C) | the record-time tapes are in no small regular language; refinement never converged |
| PR 97's parity-only wall | 1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA | with free residues a halting chain exists, so no parity invariant can work |
| PR 78's fixed lap | 1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC | the branch path changes every era |
| Odometer halt hunts | 1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD (to 10^1572 steps) and three others | no halt reached; nothing explains why not |
| Proving two holdouts equivalent | 23 candidate pairs | the re-sync bisimulation closes for none |

The common thread of the failures: we searched for the *right exact description* (a language of tapes, an exact
orbit, an exact match to someone else's proof). The successes of part 1 point the other way.

## 3. New techniques, ranked by promise

### A. Hand the counter programs we already have to invariant solvers (highest promise per hour)

**Idea.** Many folders already hold a machine's macro rules as guarded affine updates on a few counts (the
`stepper` rule tables, proved in Lean). That is a counter program. Whether a counter program can reach a bad state
is what constrained-Horn-clause solvers (Z3's Spacer, Eldarica) and numeric abstract interpreters (polyhedra plus
congruences) are built for, and we have never run one. Every N3 proof is an invariant such a tool can state: a linear
inequality (c ≤ G, 2p ≤ 3g + 3, "each counter at least 5 times the one below"), sometimes with a residue. A
solver's answer is a candidate invariant that Lean then checks with `omega`, so the solver is not trusted.

**Why it may work where we failed.** We looked for these inequalities by eye, one machine at a time.

**Targets.**
- 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC: the wall update depends only on the wall and N mod 2, and a closed set of walls is conjectured.
- 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF and 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---: everything is in Lean except one bound, and a value that grows by exactly 1 per visit is known.
- 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: only the evolution of the small gaps after a rebuild is missing.
- 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- and 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---: a halt needs one equation between read lengths.
- The four odometers that ran far without halting (1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---, 1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD, 1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---, 1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD---): ask for an invariant that keeps "an empty block next to a block" unreachable.
- 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---: frozen blocks and one block growing about 1.4 times per sweep, the PR 113 picture.

**Cost.** Small. An exporter from the rule tables to Horn clauses, then solver time. No GitHub load.

**Tried, 26 November 2026: nothing found** (`followup/horn-solvers.md`, `tools/chc/`). Spacer and a residue-template
search time out on the stack model of the first target and on eight proved maps, and find the hand-proved domain
invariants of three controls in seconds. The proved maps are exact Collatz-like reductions, not over-approximations.

### B. Synthesise summary certificates with an abstract tail (most machines in reach)

**Idea.** Automate what cryptids PR 37 and busycoq PR 112 did by hand. Take the run-length machine (free for any
tape without `000`, as found on 26 November). Abstract each count to "exact if small, else a cap plus a residue",
and allow the value ANY. Compute, by fixpoint, summaries of the form "from left context X with tail abstraction T,
the excursion returns in one of these forms or never returns". Refine the cap and modulus only where a summary
reaches a halt. Emit the DAG of summaries and check it in Lean by kernel `decide`.

Two changes from our earlier, failed attempts:
- **Summaries of excursions, not languages of tapes.** A summary is a function contract. It can be finite when
  the set of tapes is not regular.
- **Work backwards from the halt.** Ask for the weakest fact about the tail that keeps an excursion safe. For
  1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- the answer was "nothing at all".

**Targets.** The "growing counter beside a short disordered end" machines: the 48 of the old family F04 and much of
R15 (95, parked as Collatz-like, perhaps wrongly, as PR 113 showed for its machine). First tries:
1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA, 1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD,
1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA and 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC.

**Cost.** A real tool: perhaps a week for the explorer and the Lean checker. One checker serves every machine.

### C. Lap-level regular model checking over tokens, with the carry as look-ahead

**Idea.** A sweep that rewrites a token list using a carry from the far end is a *bimachine*: one automaton reads
the list right to left and computes the carry, another rewrites left to right. Learn both from recorded sweeps
(states = carry classes), then check closure token by token, which is a finite check that prints directly as an
induction on the list. This turns "learn the carry", the open item of the recursive-sweeps note, into a standard
transducer-learning problem. It works at lap granularity over tokens, where a hundred-state cell automaton may be
a five-state one.

**Guard against the PR 593 artefact.** Reject any carry whose values all occur equally often, once per lap.

**Targets.**
- 1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE, 1RB1LB_1LC0LD_---1LD_1RE0LA_0RF1RD_1RA1RE and 1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA (one table; wall `6 4 7`, residues mod 3 stable through 3·10^8 steps).
- 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC and 1RB0LB_1RC0LD_0LA1RD_1LC1LE_1LF0RE_1LD---.
- 1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE: both sweeps are already transducers in Lean; what is missing is the closed set for the far zone.
- Finite block sets (PR 114 style): 1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA, 1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA---, 1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---, 1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---, 1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---, 1RB0LD_1LC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB.
- The eight chaotic bouncers with bounded crossings: 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---, 1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF, 1RB0LF_0LC1LB_0RD1LA_1RE0RA_---1RD_1RC1LF, 1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA, 1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB, 1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC, 1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC, 1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE.

**Cost.** Medium. B and C share the Lean checker; C is the better fit when the far end matters, B when it does not.

### D. Transfer invariants, not proof text, from the hundred proved machines

**Idea.** Two cheap screens we have not run in this form.
- **Eventually unused transitions.** For each open holdout, list the transitions its run stops using. If it stops
  using the transitions in which it differs from a proved machine, and the tape at that moment lies in the proved
  machine's invariant, the proof transfers. Transplanting the proof text failed 139 times because the text also
  covers the transient; the invariant does not care.
- **One-way simulation.** Our own halting proof of 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE rests on a lemma that a
  detour "can only add halts". The bisimulation search asked for equality in both directions. Ask instead for
  "every halt of X is a halt of Y" (for non-halting) or the reverse (for halting).

**Targets.** The 10 open neighbours of DeepMind's tables, the 81 holdouts within two transitions of a template
machine, and the open start-state siblings of the 38 merged machines. Among them
1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF and 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF, whose Coq skeleton already compiles.

**Cost.** Small: runs of 10^9 steps per machine and a table comparison.

### E. Make segmented halting replays a reusable framework, and rank halt hunts by expected hits

**Idea.** The proof for 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC does not depend on that machine. Its core lemma
(`block_ok`: any guessed digit string whose formal run ends with large counts is the true run) holds for any
piecewise-affine visit map. Package it as: a visit map, a chunk table, a guesser, and a segment driver. Beside it,
give each proved map a hit estimate (the sum over rounds of the chance of landing on the halting case). A sum that
diverges says keep running; a sum that converges fast says stop hunting and look for a non-halting argument (A).

**Targets.** The Vampire family (1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---, 1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA
and five more, a halt reported near 7·10^11 passes), 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE (tent map),
1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE, 1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---, and the doubling trio
1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE, 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE, 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE.

**Cost.** The framework is small. The runs are the big compute, so they wait for a decision to spend it.

### F. Treat the regular side as a generator of an automatic sequence

**Idea.** In PR 110 a counter of eras feeds a fixed stream of events to a messy end. When the regular side is a
base-b counter, its event stream (carry lengths, capped) is a b-automatic sequence. "Does the messy end, as a
finite transducer driven by this stream, ever reach a bad state?" is then decidable by a product construction, the
method the Walnut prover automates. This needs the messy end to be finite-state given the stream, which must be
checked per machine.

**Targets.** The clock-and-word family (15 machines, for example 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---) and the
"counter beside a chaotic edge" family (39 machines); 1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB and its siblings if
the walk lengths turn out to be a function of the counter's digits.

**Cost.** Medium, and the precondition may fail often. Try two machines before building anything.

### G. Arithmetic maps: closed sets of residues, found by search (low odds, cheap)

For machines reduced to a closed-form map, search for a finite set of (residue mod m, phase) classes that is closed
and avoids the halting values. Targets: the doubling trio of E (n → 3n − 10·2^k + 3k + 14),
1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE with its three siblings, 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA and
1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD. If the map is truly Collatz-like, no such set exists, and that is the likely outcome for most.

### H. Hierarchical invariants for nested counters (speculative)

Odometer tapes are self-similar, so a closed set might be stated over a grammar (level k is built from copies of
level k − 1) and proved by induction on the level, as PR 91's tower of 14 walls does for one machine. Targets: the
nested ternary counters, for example 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD and 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB.
No tool exists; this is a direction, not a plan.

## 4. Suggested order

1. A and D first: both are cheap, need no new theory, and can run this week without pushing anything.
2. B next, with C sharing its checker. This is the investment most likely to decide many machines.
3. E's framework, then spend compute on the hunts its estimates favour.
4. F, G and H only as side experiments.
