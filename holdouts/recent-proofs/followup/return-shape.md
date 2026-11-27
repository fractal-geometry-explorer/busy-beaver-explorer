# Return-shape analysis: the PR 42 proof shape as an automatic search (27 November 2026)

Follow-up 1 of [`../cryptids-pr42-nov27.md`](../cryptids-pr42-nov27.md). **Result: the analysis rediscovers a closed
grammar for the PR 42 machine in about a second, and closes on none of the 501 open holdouts.** Everything here is
computed, not proved. No Lean proof was attempted because nothing new closed.

Code: [`../tools/return-shape/`](../tools/return-shape/) (`sampler.c`, `sba.py`, `sweep.py`).
Raw results: [`return-shape-sweep.txt`](return-shape-sweep.txt) (all 501 machines) and
[`return-shape-candidates.txt`](return-shape-candidates.txt) (the run-grammar candidates, more settings).

## What the analysis does

The tape is read from the regular end (mirrored if needed) as a list of tokens, where token d is the cells `1^d 0`.

- A **call** is the head entering a tail in state S. The tail is described by a nonterminal V, and the call sees a left
  context `ctx`, which is the cells back to the J-th zero. The call **returns** when the head leaves to the left of `ctx`.
- The **contract** C(S, ctx, V) is the finite set of return shapes (exit state, explicit head cells, tail nonterminal).
- No grammar is given. A return whose tail has more than L tokens is cut after L tokens, and the rest gets a new
  nonterminal named by the call (S, ctx, V truncated to nesting depth j), the exit state and the head cells. The tokens
  between the cut and the old nonterminal are stored as a chain of productions.
- Every end turn (head left of all ones, arriving by a left move) is a cut point with its own nonterminal `TOP(state, gap)`.
- The start is one real end-turn tape taken after the transient. The analysis is the least fixpoint from that seed.
  It is finite, and a halting transition met by any symbolic run is a failure.

Soundness is the argument of the PR 42 proof: strong induction on the step budget. A call that never returns needs no
contract entry, so the least fixpoint is a valid certificate when it closes without meeting a halt.

Three earlier designs were rejected. Window (k-local) token grammars learnt from samples admit halting tapes on the PR 42
machine. A reverse-trie grammar with a fold product collapses. A behaviour-row learner in the style of L* explodes.

## Validation on 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF

- With the grammar of the proof typed in by hand (5 nonterminals), a contract solver closes at L = 1, J = 2: 17 tail
  classes, 44 contracts, 170 shapes. With J below 2 it diverges, which matches the proof's use of two-frame contexts.
- With no grammar given, `sba.py` closes from a single seed tape (end turn 20 of type F, gap 0) at L = 1, J = 2, j = 2
  in 0.7 s: 1,153 nonterminals, 1,081 contracts, 3,086 shapes. It also closes in the mirrored orientation, and at
  (L, J, j) = (2, 2, 1). At j = 0 it reaches a halt, and so does a seed from the early transient (end turn 5), as expected.
- The learnt grammar is far larger than the hand proof (5 nonterminals, 3 and 9 return shapes). It is a certificate of
  the same kind, not the same grammar. No minimisation was done.

Reproduce:

```
gcc -O2 -o sampler sampler.c
./sampler 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF 0 1e8 100000 0 > m0.txt
python3 sba.py 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF m0.txt --only F,0,1 -j 2
```

## The run-grammar candidates

Seed = end turn 100 of the most frequent type, 18 settings each (L in 1..2, J in 1..3, j in 0..2), 45 s limit per setting.

| machine | outcome |
|---|---|
| `1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA` | no closure: 9 word-length blow-ups, 1 halt, 1 nonterminal limit, 7 over time |
| `1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD` | abstract halt at all 18 settings, in under a second each |
| `1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA` | over time at every setting; nonterminal limit (30,000) at (1, 3, 2) |
| `1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE` | 17 halts, 1 nonterminal limit |
| `1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA` | 4 halts, 4 blow-ups, 2 other limits, 8 over time |
| `1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---` | 17 halts, 1 blow-up |
| `1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC` | 6 halts, 11 blow-ups |
| `1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD` | nonterminal limit at all 18 settings |
| `1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF` | 15 halts, 2 blow-ups, 1 nonterminal limit |

`1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA` was only run in the sweep below (no closure).

An abstract halt does not mean the machine halts. It means the over-approximation contains a halting configuration.

Closer look at the two priority machines:

- **`1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD`**: the halt stays at deeper settings too, up to (L, J, j) = (3, 2, 3),
  (1, 3, 5) and (1, 4, 4), and for seeds 100 and 300. So it is not caused by the name truncation. Its tape has a
  constant periodic block at the far end and an irregular region next to the head, with `(1 0)^n` stretches whose
  counts change. The invariant that excludes the halt is not a regular token language over this kind of context.
- **`1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA`**: the real tape has runs of at most 3 and long blocks of period 16
  whose repeat counts grow (10 at step 2e5, 39 at step 2.9e6). At j = 0 the analysis loses the bound on run length
  (a symbolic run of over 1,400 ones appears). At j = 1 or 2 the number of nonterminals passes 30,000 without
  closing. Its sweeps cross the whole tape, so calls rarely return early and contracts do not summarise much.

## Sweep of the 501 open holdouts

`sweep.py`: both orientations, samples from 1e7 steps, seed = end turn min(100, n/2) of the most frequent type, four
settings (L, J, j) = (1, 2, 2), (1, 2, 0), (2, 2, 1), (1, 1, 1), 6 to 8 s each.

| outcome per machine | machines |
|---|---|
| closed | 0 |
| some attempt reached an abstract halt | 266 |
| only resource limits (time, word length, nonterminals, shapes, fuel) | 105 |
| not run in either orientation (fewer than 60 end turns in 1e7 steps, or seed over 400 tokens) | 130 |

## Reading

The method needs what the PR 42 machine has: short runs, a head that works near one end, and deep recursion in which
calls return after local work. The 130 machines that were not run do not have a regular end at this time scale. For
the rest, the analysis as built is too coarse (abstract halt) or too slow in Python (limits).

Not done, in order of likely value:

1. A refinement loop that splits a nonterminal when a halt is traced back to a join, instead of one global depth j.
2. Other token conventions (zeros as the run symbol, fixed-width blocks) for machines such as
   `1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD` whose tape has many double zeros.
3. A port to C++ so that the 105 machines stopped by limits get a real answer.
4. A certificate export with a Lean checker. The design is two finite automata read outward from the head, a set of
   configurations, and simulation pairs for the subsumption at calls and returns. It is only worth building once an
   open machine closes.
