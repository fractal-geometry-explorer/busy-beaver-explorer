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
exact lengths. The next section shows the bulk is not quite free either: gaps after a `10` defect are constrained.
Scripts and notes: project folder `ctl-696/`.

## Defects and the danger pattern (16 November 2026)

Every tape seen when the head first reaches a new left cell (all 7,409 up to 3*10^7 steps) parses greedily as
words x = 111, y = 110 with two kinds of inserted defect, `0` and `10`, and a final 1. The only way into the halting
read `1 0 0` is the pattern `0 10 (110)* 0`: a `10` defect right after a 0, then y words, then a `0` defect. It never
occurs in those tapes.

Mutation tests on real tapes (scripts `mut*.py` in project folder `ctl-696/tools/`), run for 60 more left visits:

* Replace the words left of the first defect with random words: 150 of 150 runs stay clear.
* Replace all words between defects with random words (defects and the last 12 tokens kept, tapes containing the
  pattern dropped): 99 of 100 clear. Changing the defect types or positions too: 92 to 94 of 100 clear.
* Every halting run, shrunk to the smallest set of changed words, changes the words in a short gap `10 W 0`. In
  each deep sweep that gap is rewritten by the XOR rule (`10 xyxyx 0` becomes `10 yyyyy 0`), and once W is all y
  with a y or 0 before the `10`, the pattern appears and the next sweep halts.

So the bulk is not a free shift after all. Safety depends on the XOR orbit of the words between a `10` defect and
the next wall never reaching all y. That is a condition over GF(2) on gaps of any length, which a fixed window
cannot see, and which explains why the window and model-checking searches above close only by reaching a halt.
A proof would need to show how `10` defects are made at the right end and what gap words they start with.

## Walls as particles (16 November 2026)

Read the defects as particles with a charge mod 3 (the shift they put in the 3-cell alignment): `0` has charge 1,
`10` has charge 2. In the real run (`c/tens.c`, which tokenizes the tape at new left cells):

* A `10` in the bulk is born when two `0` walls with only x words between them meet: `0 x^k 0` becomes
  `x^(k+1) 10` (1 + 1 = 2). It ends when it and the next `0` wall cancel: `10 W 0` becomes words (2 + 1 = 0).
* There are only 4 such `10` lifetimes, at 8·10^3 to 2.7·10^4, 2.2 to 2.8·10^6, 4.1 to 5.6·10^6 and 6.6 to 8.5·10^6
  steps, each 9 to 60 tokens from the right end. After 8.5·10^6 steps there is none up to 10^11 steps (every 20th new
  left cell checked, 21,812 tapes, no halt). The other `10`s are the fixed one at the right end (`0 y 10 x 1`) and short-lived
  ones at the left end.
* While a `10` lives, the words after it change each deep sweep by v[i] = w[i-1] xor w[i], with y fed in from the
  left (45 of 45 updates without a shift), so they form a Sierpinski triangle that starts at the defect. They became all y 131
  times, and each time the word before the `10` was x. That is why the four lifetimes ended without a halt.

* The trigger for a merge is sharper than an all-x gap. `0 x^k 0` occurs all the time (17,770 tapes up to
  2·10^8 steps, at 3 to 69 tokens from the right end) and never merges when the word before the left wall is x. Every
  bulk merge came from `y 0 x^k 0` (k = 6 or 9), seen in the deep-sweep window right before each of the four
  births and nowhere else. `c/tens.c` also counts it: up to 10^11 steps the last one is at 4.07·10^6 steps (the
  6.5·10^6 one falls between samples). After 10^7 steps, an all-x gap after a bulk `0` wall always has x before the
  wall (341 of 341 in the every-5th sample to 2·10^8), just as an all-y gap after a `10` always has x before it.

So, by the data, a halt needs a `10` far from both ends, and none has formed since 8.5·10^6 steps. A proof along these
lines would show that `y 0 x^k 0` (a y word, a wall, only x words, a wall) never forms again in the bulk. The right end itself runs through four phases (`x 0 0 y 10 x`,
`x y 0 y 10 x`, `x 0 y x 0 x`, `0 x x 0 10 x`), and none of them contains the pattern.

## Rule 102 in Lean, and Lucas' theorem (21 November 2026)

* `lean/Xor.lean`, `epoch`: for **every** word string `w ++ [y]` followed by a 0, B on its first cell, the right sweep
  (`x -> 000`, `y -> 011`, B zigzagging `B 1 1 -> 0 B 1`), the turn (B on 0 writes 1, steps left in C) and the left sweep
  (C = "the word to the right is y", E = "it is x") leave the string `x102 (w ++ [y]) y`: word `i` becomes
  `w[i] xor w[i+1]`, with `y` after the end (`x102_getD`). The last word becomes `x`, and the 0 after the string becomes
  a 1. This replaces the exhaustive check in `py/xor_epoch.py` (strings up to 16 words) by a proof for all lengths.
* `lean/XorLucas.lean`, `closed_form`: iterating rule 102 with a fixed value after the end, word `i` after `t` sweeps is
  the XOR of the starting words `i + k` over the `k <= t` with `C(t, k)` odd, and by Lucas' theorem that is "the binary
  digits of `k` and `t - k` are disjoint" (`disj`, `pascal_rule`, shared with the Pascal-triangle machine
  1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF).
* `allx`: a gap of `n` `x`s next to the fixed `y` has word `j` (counted from the `y`) equal to `y` after `t` sweeps iff
  `C(t, j)` is odd. So the whole gap is `y` exactly when the binary digits of `t` contain those of `1, ..., n`, i.e.
  `t = -1 mod 2^b` with `2^b > n`: first after `2^b - 1` sweeps, then every `2^b`.

**What it says about the danger pattern.** In the gap `10 W 0` after a `10` defect the words follow the same rule with
the defect side fixed at `y` (section above). Write the gap with the defect cell as the polynomial
`W(z) = 1 + sum w_j z^j` over GF(2), mod `z^(n+1)`. One sweep multiplies it by `1 + z`; all `y` is
`1 + z + ... + z^n = (1 + z)^(2^b - 1)`; and `(1 + z)^(2^b) = 1` mod `z^(n+1)`. So:

* a gap of `n` words ever becomes all `y` **iff it already is a row of Pascal's triangle mod 2**: `w_j = 1` exactly when
  the binary digits of `j` lie inside those of some `s < 2^b`; it then becomes all `y` at sweeps `t = 2^b - 1 - s mod 2^b`;
* only `2^b <= 2n` of the `2^n` gaps of length `n` can ever reach the danger pattern, and every gap is periodic with period `2^b`.

`py/pascal_gaps.py` checks both statements for every gap of up to 14 words (all 32,766). The algebra is not in Lean. A
halt still needs, at such a sweep, a `y` or `0` before the `10` (in the data it was `x` all 131 times). So the open
question is now about binary digits: which gaps the right end hands to a newborn `10`, and what word stands before the
defect at the sweeps `t = 2^b - 1 - s mod 2^b`.

## In the frame of a `10` defect (21 November 2026)

`c/defect10.c` prints, at every new left cell up to 9·10^6 steps, each bulk `10` (more than 30 tokens from the right end)
with the 80 tokens before it and the gap after it; `py/defect_frame.py` reads the sweeps where something near the defect
changed (59 of them, in the three long lifetimes starting near 2.2, 4.1 and 6.6 million steps, gap closed by a `0` wall):

* **When the word before the `10` is `x`, everything is linear.** Keep the defect in place and index words left to right.
  Then the words before it go from `l` to `l'[i] = l[i-1] xor l[i]`, and the gap goes from `g` to
  `g'[j] = g[j-1] xor g[j]` with a `y` in place of the defect. That is one rule-102 line, information flowing to the
  right, with the defect a cell pinned at `y`: it swallows the word before it each sweep and emits `y` into the gap.
  All 50 sweeps with `x` before the defect follow it, on both sides (45 of 45 gap updates of unchanged length).
* **So the word before the defect is a Lucas sum**: `t` sweeps after a start, it is the XOR of the words `L_(1+k)`
  (the `k`-th word left of the defect at the start) over the `k` whose binary digits lie inside those of `t`. At a
  birth (`y 0 x^k 0 -> x^(k+1) 10`) the defect has `k + 1` `x`s before it, so the word before stays `x` for at least
  `k` sweeps. The prediction holds for 36 sweeps in total, each time up to the first sweep with `y` before the defect.
* **When the word before is `y`, the defect hops**: the 9 other sweeps are exactly the ones with `y` before the `10`. The
  defect moves back one or two tokens and the gap shrinks, and the linear picture restarts. If the gap were all `y`
  at such a sweep it would be `y 10 y^n 0`, the danger pattern.

So the danger pattern is a coincidence of two Lucas sums: the gap, whose all-`y` times are `t = 2^b - 1 - s` (mod
`2^b`) for a gap that is Pascal row `s`, and the word before the defect, which is `y` at the `t` where the digit-masked XOR
of the left words is 1. In the data the two never coincide: all 93 snapshots with an all-`y` gap have `x` before the defect, and
every `y` before the defect came with a gap that was not all `y`. A proof along these lines would have to control the left words that a newborn defect sees, which are rule-102 images of
the bulk, and the hops.

## Lean

`lean/Rules.lean` (from `py/rules.py`): ten shift rules over 3-cell words (and runs of 0s), found by a symbolic
search over all words of 1-3 cells, each for every n and every tape around. `lean/Xor.lean` and `lean/XorLucas.lean`:
the rule 102 epoch and its closed form (section above).

## Halting

Only F1 halts. Open; n-gram CPS (widths 3..7) fails; no halt in 10^9 steps (C). `bbtools.cycles` (K = 2) makes
little progress (the string is rewritten, not shifted, so there are no linear regimes).

## Notes for later

* Done: the sweep pair is the XOR rule, proved in Lean for all lengths (`lean/Xor.lean`), with its Lucas closed form.
* The right-end structure: write its 5-phase cycle as rules, list the walls it emits, and what F0 needs there.
* Done: how `10` defects are made (walls as particles, above). Next: prove that `y 0 x^k 0` never forms after 10^7 steps (no
  local rule found: the word before a wall and the gap after it are correlated only through the XOR history), and write the right end's four phases as rules.

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
