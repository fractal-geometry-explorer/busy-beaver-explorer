# Tokens before classes: run tokens, learned classes, and tails named by their call (27 November 2026)

Follow-up to the last section of [`write-only-test.md`](write-only-test.md), which ended with two candidates for
a working refinement rule. This note tries the second: cut the tape into tokens first, then learn classes or
close over tokens. **Result: one of the two DeepMind machines is re-proved automatically, with a certificate that
an independent checker accepts. No open holdout was decided.** Everything else here is computed, not proved.

Tools: [`../tools/tokens/`](../tools/tokens/) (`tokgram.cpp`, `tokcheck.py`, `tokdec.cpp`).

## The short version

- **Learned classes over tokens do not close.** `tokdec.cpp` describes a half tape by its first R runs (lengths
  capped, parity kept above the cap) and a learned class of the rest. On both DeepMind machines it derives a
  false halt or fills up, for every setting tried, also with the 7-state automaton of the proof given by hand.
  A tracer that marks the first derived fact the real run does not show always points at the same step: taking
  one more run out of the class. A class says how the rest behaves, not what it starts with, so every listed
  continuation fits.
- **Naming a tail by the call that produced it closes.** `tokgram.cpp` keeps the run tokens and replaces the
  class by a grammar nonterminal named after the call (state, explicit runs, the call's own nonterminal to a fixed
  depth), the return state and the first R runs of what came back. This is the idea of
  [`return-shape.md`](return-shape.md), with runs of both symbols as tokens, capped lengths with parity, no left
  context needed, and an exact window at the left end.
  1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF closes in 0.2 s.
- **The certificate is checked independently.** `tokcheck.py` (Python, written from the definitions, shares no
  code with the search) accepts it in 3 s.
- 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE does not close with this tool (16 settings, 100 s each). The sibling
  thread closed it with an exact 32-cell frontier and an 8-cell prefix.
- The four open holdouts of the brief do not close in about 560 settings (10 s each).

## What a certificate is (`tokgram.cpp`)

The machine is mirrored if needed so that the regular end is the left end.

- **Tokens** are maximal runs of equal cells. A length below `cap` is exact; from `cap` on only "at least cap,
  even" or "at least cap, odd" is kept.
- **A half tape** (the cells right of a boundary) is a few explicit runs followed by a nonterminal of a
  right-linear grammar over runs, `N -> run N'`. The end symbol is the blank tape.
- **A call** (context, state, half tape) is the head in that state on the first cell of the half tape, with at
  most J runs of context to its left. It returns when the head leaves the context to the left. Its **facts** are
  the pairs (return state, half tape right of the left edge of the context).
- **The top level** keeps the first W cells from the leftmost 1 exactly. A step off the right end of these
  cells is a call with an empty context.
- While a call is evaluated, the head moves exactly over the context and the explicit runs. When a move to the
  right makes the context longer than J runs, the nearest J runs become the context of a nested call. With
  J = 0 every step to the right is a nested call.
- When a call returns a half tape with more than R explicit runs, the tape is cut after R runs. The rest gets a
  nonterminal named by the call, the return state and the R runs, and productions for the runs that were cut.
  The call's own nonterminal enters the name only to nesting depth `DEPTH`, which makes the set of names finite.
- The start is the real configuration after `T0` steps. From the blank tape the analysis reaches a halt on
  the machine below, because the early tapes are not in the later grammar.

The fixed point is finite. If it contains no halting transition the machine does not halt: by induction on the
number of steps, every configuration of the real run is a listed top configuration, or is inside a listed call
whose every return is listed.

`tokcheck.py` checks exactly that: the seed configuration is listed; one step from each top configuration stays
inside the list and does not halt; each call, run on its context and half tape with nested calls answered by
their facts, does not halt and returns only listed facts. "Listed" allows a listed half tape that covers the
derived one along productions of the grammar.

## 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF

Seed at step 112,980 (first time after step 100,000 that the head is in the exact window), cap 16, W = 4.

| R | J | depth | result | nonterminals | calls | facts | top configurations | search | checker |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 0 | 3 | closes | 2,888 | 11,179 | 20,811 | 106 | 0.2 s | accepts |
| 1 | 1 | 3 | closes | 2,150 | 3,831 | 4,758 | 106 | 0.1 s | accepts |
| 1 | 0 | 5 | closes | 5,455 | 13,602 | 24,416 | 133 | 0.3 s | accepts |
| 1 | 0 | 3 | halt reachable | | | | | | |
| 2 | 0, 1, 2 | 1, 2 | halt reachable | | | | | | |
| 2 or 3 | 2, 3, 4 | 3, 5, 8 | halt reachable | | | | | | |

Of 45 settings (R 1 to 3, J 0 to 4, depth 3, 5, 8), 14 close, 24 reach a halt and 7 run out of time. More left
context does not help here: with J of 2 or more and R of 2 or more every setting reaches a halt. The naming
depth is what matters; depth 1 and 2 never close. From the blank tape (T0 = 0) and in the mirrored orientation
the analysis reaches a halt.

The grammar is much larger than the proof's (5 nonterminals, 3 and 9 return shapes). It is a certificate of
the same kind, found without being told the tokens, the grammar or the call points.

## What did not work, and why

**Learned classes (`tokdec.cpp`).** Half tape = first R runs + class of the rest, where classes are the rows of
the observation table of `learncls.cpp` (13 classes for 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE, 184 for
1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF), or a given automaton (`AUTO=`). To take a run out of a class the
tool uses the set G of all abstract half tapes seen. Results:

- 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE, R = 2: G reaches all 331 possible values, against 132 in the real
  run; R = 4: 8,281 values, and the top level passes 2 million configurations.
- With the proof's own 7-state automaton as classes (`m1_proof_dfa.txt`) the result is the same. That
  automaton is an invariant of the tape right of the head at the proof's macro steps. A table that must hold at
  every cell boundary also meets the tapes in between, such as `0000 111`, which the automaton rejects. The
  sibling note on contract tables found the same thing from the other side.
- Left contexts on calls (J up to 4) do not change this. A context only splits the keys; the loss is in the
  half tape.
- `REAL=steps` runs the real machine beside the fixed point and prints the first derived configurations and
  returns that the real run does not show, with their premises. All of them are of one kind: "rest [run | class]"
  taken from G.

**The first DeepMind machine with `tokgram`.** 16 settings (W 32 and 48, R 1 to 3, J 0 and 2, depth 0 and 1,
cap 4, 100 s each) all run out of time or space; the top level grows past 5 million configurations at J = 0.
Call names do not bound what comes back to the window well enough here. Its proof needs exact end words and one
parity, which the sibling thread's exact frontier with a short prefix provides directly.

**The four open holdouts.** Both orientations, cap 4, 8, 16, J 0 and 1, depth 3 and 5, R 1 to 3, W 4 and 16,
seed after 10^6 steps, 10 s each:

| machine | settings run | halt reachable | out of time |
|---|---|---|---|
| 1RB---_1LC0RF_1RF0LD_0LE1LC_0RC0LC_1RB0RA | 144 | 105 | 39 |
| 1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA--- | 144 | 142 | 2 |
| 1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA | 131 | 2 | 129 |
| 1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA | 141 | 13 | 128 |

The scan of the last two was stopped by its time limit before the last settings. An abstract halt does not mean
the machine halts. For the last two machines nearly every setting runs out of time, so longer runs are the
obvious next test; for the first two the abstraction is too coarse at these settings.

## Checks on the tool itself

- The checker shares no code with the search and re-derives every call and top step.
- `tokgram` was run on 1,058 random machines with 3 to 5 states and random settings, and compared with direct
  simulation for 30,000 steps. It reported 582 as closed; none of them halts within the 30,000 steps. All 318
  that halt were reported as "halts in the seed run" or "halt reachable".

## Not done

1. Longer runs on 1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA and 1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA,
   and a sweep of all open holdouts with the settings that close the DeepMind machine.
2. Combining the sibling thread's exact frontier with a short cell prefix and call-named tails.
3. A Lean version of `tokcheck.py`. The certificate format is plain text and the check is three finite loops,
   so a reflected checker is feasible; it is only worth building once an open machine closes.
4. Minimising the grammar (merging nonterminals with the same productions) to get closer to the hand proof.

## Reproduce

```sh
cd holdouts/recent-proofs/tools/tokens
g++ -O2 -std=c++17 -o tokgram tokgram.cpp && g++ -O2 -std=c++17 -o tokdec tokdec.cpp
# closes in 0.2 s and writes a certificate (about 0.7 MB)
J=0 DEPTH=3 T0=100000 CERT=m2.cert ./tokgram 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF L 2 16 4
python3 tokcheck.py m2.cert
# learned classes: false halt; REAL= prints the first steps the real run does not show
REAL=3000000 LEARN=3000000 ./tokdec 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE L 2 4 24 2000000 30000
AUTO=m1_proof_dfa.txt REAL=3000000 ./tokdec 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE L 2 4 24 2000000 1000000
```
