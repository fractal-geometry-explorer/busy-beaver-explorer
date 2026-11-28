# 1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE: findings (Nov 26)

Working notes, written while trying to prove the machine never halts. The programs here are hand-written and their checks are trusted computation (C/C++/Python), not proofs in Lean. `cstar12.txt` is the 239-carry set C*; `creal8.txt` is the 31 carries seen at the 8-token boundary of the real run.

## Proved (informal, short induction)
**Lemma I1.** Strip leading blanks from the tape left of the head. That word never contains "00".
- Right moves append the written symbol. The only "write 0, move right" is F0 -> 0RA, and F is
  only entered by A1 -> 1RF or E0 -> 1RF, which both write 1. So a 0 is only appended after a 1.
- Left moves only shorten the word.

**Consequence.** Halting (D reads 0) needs C0 -> 1LD with a 0 to the left, which by I1 can only
happen at the far left end. Equivalently the machine halts iff E ever reads a 1 whose left
neighbour is the leftmost 1 of the tape (pattern 0^inf 1 [E on 1]).

## Not a recursive-sweep machine
The screen in ../../recent-proofs/recursive-sweeps-nov23-25.md matched the wall `6 4 7`,
but the tape is not in segment form. le2.c prints the tape (run-length, '.'=0, '|'=00, '#'=000,
'?'=0000+) every time E stands on the leftmost 1. Irregular tokens (1.1#1, 1.1.2.1.1?1, 5.5.5.5.7)
keep appearing, so the PR 115 segment/BigF route does not transfer.

## Automated searches that failed
- FAR/CTL (earlier): dfa_unsat up to 11 states, nfa_unsat 6.
- Pushdown (post*) abstraction, DFA on the left side: de Bruijn windows k<=12, k-testable
  observed factors, trie of left-end words + body; all reach halting.
- Mirror (exact left stack, k-testable DFA on the right part), factor-closure growth from the
  real configuration at step 3,000,000: k=12 and k=16 both reach a halt and keep growing
  (k=16: 14k -> 57k states over 40 rounds without closing).

## Empirical
No halt in 1e9 steps. Random re-randomisation of the left part with no-"00" words never
halts unless the far-left word starts "110".

## Update (Nov 26, later): structure of the run

- **Lean.** The no-00 lemma is proved in Lean (`lean/LeftEnd.lean`, PR #597 in busy-beaver-explorer).
- **Leftward sweeps over runs of 1s.** A straight leftward sweep passes a run of 1s only if the run's length is a multiple of 3. It enters each run in E after D, and it must meet each separating 0 in state C. B or E on a 0 turns right.
- **Macro picture.** The head zigzags right and then left. Macro turning points cluster at slowly drifting walls (positions about 0, 49, 240, 430, 500, 670, 1250, 1550 at step 2e6). Seen at a left turn, the tape is a chaotic zone at the left followed by periodic zones. Split at "00", the tokens are a=1.1, b=1.1.7, c=1.1.7.7 and d=1.1.5 (e.g. at step 1.5e8: ... (aab)^19 ... (a^6 b)^28 ... (baaa)^96 (abb)^48 (aaaac)^211, then the wall).
- **New token kinds keep appearing.** By step 4e8 the tape holds (ac)^16, (aac)^8 and a run 1.1.7^24.5, so the token set keeps growing.
- **Halting.** A halt needs D to read the blank left of "1 1" at the far left: E reaches the second cell while the first is 1.
- **Locality at the left end.** What the left end looks like after a left-end visit is determined by the state, the 30 cells to the left and 40 cells to the right when the head comes within 30 cells. Checked on about 1600 cases with no conflicts.
- **The leftward pass as a transducer.** Over tokens (1^a 0) it is nearly a sequential transducer with carry (state, about 12 output cells). The exception is a C carry, which turns back right through its own output (nested sweeps), so the carry is not finite with a fixed window.
- **More regular abstractions that failed** (exact left part, abstract right part):
  - run-window DFAs (last k runs, k = 4 and 6, run lengths capped at 12) reach a halt after 4 and 12 growth rounds;
  - the token-star language (tokens split at 00+) reaches a halt after 3 rounds, and the separators grow without bound.

## Update (Nov 26, evening): the leftward pass forgets; the left end is still coupled to what comes in

The key scripts are in this folder.

- **Leftward pass as a transducer.** Carry = (TM state, the 12 cells right of the head) at the first arrival at the start of each run of 1s (right after a 0), stepping over one token 1^a 0. The step is `f` in fL.py.
- **Forgetting lemma (exhaustive).** Start from any state in {B,C,D,E} and any 12 cells. After whole tokens covering 10 or more cells, with the head never leaving the 12-cell window, the carry is one of 239 (C*, cstar12.txt). C* is closed under f for every a up to 39. Checked for every token sequence up to 40 cells.
- **Arrival lemma (exhaustive, arrset.cpp).** Let b be the cell after a 0 that ends a run (cell b-1 = 0). Suppose the head was last at b+12 and then reaches b for the first time. Then (state, cells b..b+11) is in A_12, and A_12 equals C* (239). The check enumerates every no-00 word on [b, b+12) and every left move out of b+12, using I1 to drop C reading 0 next to a 0. The result does not depend on the history.
- **Real run.** In 1e9 steps the first 8 tokens at the moments the head leaves (goes 12 cells past their end) take only 43 values, saturated early. The first 12 tokens take 231 values, still slowly growing. At the 8-token boundary only 31 different carries arrive.
- **Region closure (region2.cpp; regionp.cpp with a carry file).** Take the region of the first m tokens and let any of the 239 carries arrive at any time:
  - m = 4 and m = 8 reach halts;
  - m = 12 has no halt in 2.1M regions but does not close, and its 8-token prefixes grow past 570.
  - Even with only the 31 real carries arriving in any order, m = 8 halts.
  - So the left end is coupled to the tokens right of it; arrivals cannot be treated as free input at a fixed token boundary.

## Update 3 (26 Nov 2026): the left end cannot be decoupled

- Region closure at m=8 using only the 31 arrival carries actually seen in the real run (creal8.txt) still fails: 200000 regions with no closure and 114046 spurious halts. So the problem is not that C* is too loose.
- In the real run, the 43 left regions meet only 312 of the 43x31 possible (region, carry) pairs.
- The arrival carry is not a function of (previous region, previous carry, current region): 117 of 312 such keys see more than one carry.
- Conclusion: what arrives at the left end depends on the counter-like zones further right ((aaaac)^209, (baaa)^96, (abb)^42, ...). Any proof has to model those zones as counters (exponent-level configurations), not the left end as a finite-state system.

## Update 4 (26 Nov 2026): the blocks further right are not a fixed set of counters

Whole tape at the first left-end visit after 1e8 * 1.25^i steps (i = 0..11), split at 00 into tokens and compressed into runs of a repeated word (6 or more copies), "~n" meaning n tokens that are not in a run:

- One block grows like a counter: (aaaac)^n at the right, n = 157, 197, 214, 237, 255, 271, 284, 404, 458, 504, 537, 563 (seen in its rotations caaaa, aacaa).
- The other blocks are not a fixed list. Between the 12 snapshots their words change (ab, aba, baa, aab, aaab, bba, abb, bab, aaaabaa, baaaaaa, aabaaaa, abaa), they appear and vanish, and 100 to 200 irregular tokens sit at the left end each time.
- The fixed-shape accelerators find almost nothing: tools/py/bbtools/rleaccel_rec.py with blocks of 2 proves 6 rules and reaches only 10^7.5 steps in 60 s.
- So an exponent-level model would need an open-ended family of zone patterns, and the halting question sits in the irregular left part those zones feed. I have no route to a proof from here.
