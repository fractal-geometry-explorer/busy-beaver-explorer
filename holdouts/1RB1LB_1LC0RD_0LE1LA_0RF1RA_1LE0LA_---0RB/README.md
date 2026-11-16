# 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB

bbchallenge id 696. One of the six-state holdouts. Analyzed by hand (group G02, then the CTL thread of 16 November 2026): shift rules proved, sweep rule decoded (XOR, rule 102), no closed tape language yet.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LB |
| B | 1LC | 0RD |
| C | 0LE | 1LA |
| D | 0RF | 1RA |
| E | 1LE | 0LA |
| F | --- | 0RB |

## What it does (observed)

The left side (31,721 cells after 10^9 steps) is runs of 1s of lengths 2 mod 3 separated by single 0s, i.e. a
string over the 3-cell words `110` and `111`; right of the start are ~200 cells of `11` and runs of 0s. Every sweep
rewrites the whole string (successive left-end visits show unrelated strings, not shifts) and makes it one or two
cells longer (width 2,366 -> 2,395 over 29 visits near step 3·10^6). This looks like arithmetic on a number written
on the tape, one operation per sweep, with a counter at the right.

## The sweep rule (16 November 2026)

Write x = 111 and y = 110. A round trip of the head (right sweep in state B, left sweep in E/A/B/C) maps a clean word
string w to v with v[i] = w[i] xor w[i+1] (x = 0, y = 1): the linear cellular automaton rule 102.

* Right sweep, B at the start of a run: `1^m 0 -> 0^(m-1) 1 1` (m >= 2), `1 0 1 -> 0 0 0`, `1 0 0` halts
  (B1 0RD, D0 0RF, F0), B on 0 turns left.
* Left sweep: E 0->1 stays E; E 1->0 goes A; A 1 goes B; A 0 turns right; B 0->1 goes C; B 1 turns right;
  C 0 goes E; C 1 goes A.
* `py/xor_epoch.py`: with the machine's own table, every word string ending in y of up to 16 words (65,535 strings):
  the right sweep never turns, the left sweep never turns, the result is the XOR string (last word x).

So every word string is possible in the bulk. Defects are walls where the 3-cell alignment shifts (runs of length
0 or 1 mod 3, double 0s). A single wall cycles `00 -> 1^(3k) -> ... -> 1^3 -> 00` while drifting left; a right
sweep stops at the first `00` wall (B reads 0), so walls act like counter digits. New walls come from the right end,
a 5-phase cycle that gains 2 cells per cycle. A halt needs B in token mode on `1 0 0`: a single 1 (seen only within
about 30 runs of the right end), maybe followed by y words read one cell out of step, then a `00` wall.

## Closed tape language searches (16 November 2026)

None closes (each reaches a halt in its abstraction or exceeds its budget):

* Whole-tape automata (abstract regular model checking: DFA over the tape with the head symbol, exact one-step
  image, states merged by k-step Moore equivalence forward, reversed or both), k = 1..6, forward from blank and
  backward from F reading 0.
* Run-length windows with lengths mod 3 (`c/rlwin.cpp`; F11 tried M = 1, 2, 4 only): K = 2..16 runs with lengths
  exact below 3 halt; exact lengths up to 4..8, or keeping runs near the blank ends exact, exceed 5 to 30 million
  abstract configurations.

Why: the bulk is a full shift (any word string), so windows of K runs grow like 2^K, while the right end needs
exact lengths. Next: automata that keep the right-end zone exact and let the bulk be any word string with walls
(TM.CTL accepts general automata on both sides). Scripts and notes: project folder `ctl-696/`.

## Lean

`lean/Rules.lean` (from `py/rules.py`): ten shift rules over 3-cell words (and runs of 0s), found by a symbolic
search over all words of 1-3 cells, each for every n and every tape around.

## Halting

Only F1 halts. Open; n-gram CPS (widths 3..7) fails; no halt in 10^9 steps (C). `bbtools.cycles` (K = 2) makes
little progress (the string is rewritten, not shifted, so there are no linear regimes).

## Notes for later

* Done: the sweep pair is the XOR rule (above). Next: prove it in Lean for all lengths (two per-word transducer
  lemmas and an induction over the word list; the toolchain was not available in the 16 November container).
* The right-end structure: write its 5-phase cycle as rules, list the walls it emits, and what F0 needs there.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 15, history 1 up to width 20, history 2 up to width 20, history 3 up to width 20, LRU history up to width 6 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 16, p = 3 up to width 16, p = 4 up to width 16, p = 6 up to width 16.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 1 under the head, 0 right, 0 two right.

## Pages

- [`pages/holdouts/1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/explainer.html`](../../pages/holdouts/1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/explainer.html)
- [`pages/holdouts/1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/proof-status.html`](../../pages/holdouts/1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB/lean/check.sh
```
