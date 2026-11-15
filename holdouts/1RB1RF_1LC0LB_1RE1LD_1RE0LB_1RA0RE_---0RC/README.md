# 1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC

bbchallenge id 154101. One of the six-state holdouts whose halting from blank tape is open. Decoded: it is a
**binary counter V at the left end that gains 39 or 42 (alternately) every 8 sweeps**, with a 3-bit sweep counter
and a long block (1011)^m at the right end that grows by one copy per sweep. **Proved in Lean: the machine can halt
only during a B-overflow transient** (the moment, once every second doubling of V, when V overflows in phase B), and
not during the first one: every sweep that does not start such a transient (all shallow and deep sweeps, and the
A-overflows) is proved for all counter values, widths and block lengths, and the run from blank tape through the first
transient is evaluated. What is left is one lemma (`H` of `nonhalting_of_transients`): that every B-overflow
transient ends in a steady visit again.

A dedicated pass (15 November 2026) decoded the transient completely ("The odometer" below) and found that this
lemma is **not a routine induction**: the transient runs a binary counter against a base-3 counter written over the
long block, the state it leaves behind depends on the width in a number-theoretic way, and the clean-up that follows
has to finish before the binary counter runs out, with a margin that is not obviously positive in every epoch. An
exact accelerated simulation follows the model to 1.1*10^17 steps (16 transients, widths 13 to 28) with no halt and no
exception. **Halting is open**; the earlier wording "almost certainly never halts" is withdrawn: no halt is in sight,
but there is no argument either that the clean-up always succeeds.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1LC | 0LB |
| C | 1RE | 1LD |
| D | 1RE | 0LB |
| E | 1RA | 0RE |
| F | --- | 0RC |


## What it does

A *visit* is a moment when the head stands in state C on the blank cell just right of the tape. At almost every
visit (all but a few dozen per epoch, see below) the tape is, left to right,

    0^inf  [1]  U(b_top) ... U(b_1)  b_0 0 1   M(t)   I(i)   (1011)^m 1 0   C>0

* `U(b) = b 0 1 1 0 1` is one binary digit b of a counter **V** (`b_top` first, `b_0` written as `b_0 0 1`);
  the width w is the number of digits. In **phase A** there is no lone 1 in front and the top digit is 1
  (2^(w-1) <= V < 2^w); in **phase B** there is a lone 1 in front and V < 2^w is arbitrary.
* `M(t)` is a fixed 45-cell word with one variable cell (index 11), the bit **t**:
  `M(0) = 110110111010011101110111011011101110111011101`, `M(1) = 110110111011011101110111011011101110111011101`.
* `I(i) = U(i_2) U(i_1) i_0 0 1` is a 3-bit counter **i** of the visits.
* `(1011)^m 1 0` (the same as `1 (0111)^m 0`) is the long block; m grows by 1 every visit.

**The rule** (visit to visit; m -> m+1 always):

* i < 7 (*shallow* visit): i -> i+1, nothing else changes.
* i = 7 (*deep* visit): i -> 0, t -> 1-t, and V -> V + 39 if t = 0, V + 42 if t = 1 (so V gains 81 every 16 visits).
* *A-overflow* (a deep visit in phase A with V + c >= 2^w): phase B, same width, V -> V + c - 2^w. The digits are
  rewritten shifted by one cell and a lone 1 appears in front, so the left end moves out by one cell.
* *B-overflow* (a deep visit in phase B with V + c >= 2^w): a transient of 8 to 32 visits in which the words do not
  parse (M carries a small extra counter near its cells 3 and 20-22), then steady phase A with **one more digit**. The
  left end of the tape moves out by a few cells. The two overflows are the only times the tape grows on the left
  (left records at steps 5,976,790 and 76,113,822 are A-overflows, 30,029,339 and 228,643,991 B-overflows).

Epochs seen (visit at which steady phase A or B starts, width):

| visit | 280 | 1040 | 2688 | 4271 | 7535 | 10711 | 17191 | 23624 | 36576 |
|---|---|---|---|---|---|---|---|---|---|
| phase, w | A 13 | B 13 | A 14 | B 14 | A 15 | B 15 | A 16 | B 16 | A 17 |

Each epoch lasts about 2^(w-1)/81*16 visits, so the epochs double in length, the width grows like log of the visit
count, and the left end grows like log(steps) (the triage's "fixed").

**Each sweep in pieces.** A visit is `back` across the block (4m+8 steps), a *middle* part that never touches the
block and turns around in M and I, and `forth` across the block (4m+5 steps):

    back:    L (1011)^m 1 0 C> 0^inf          ->  L C> 1 (1001)^m 10011 0^inf
    middle:  L X C> 1 R                       ->  L X' 1 F> R
    forth:   L 1 F> (1001)^m 10011 0^inf      ->  L 1 (0111)^m 01110 C> 0^inf

The shallow middles take 7, 19, 7, 31, 7, 19, 7 steps (i = 0..6) and only look at I and the last cells of M. A deep
middle adds c = 39 or 42 to V: it adds c-32 to the five low digits and, on a carry, runs the carry left through k
1-digits to the next 0-digit (12k + about 1440 steps); the head never goes left of that 0-digit's first cell.

## The odometer (one description for steady sweeps and transients)

The visit-level words above stop parsing in a B-overflow transient. A second decoding, at the level of single
*bounces* of the head inside the left part, covers everything. Fix the **seam**: the first cell of M (a fixed cell
of the tape from visit 280 on; at a visit it is 4m + 62 cells left of the head). Then the tape is

    0^inf   L (3-cell words x01)  |seam|  window (63 cells)   block (4-cell words)   0^inf

**Left of the seam: a binary counter L, +1 per bounce.** L is a row of words `x01` (x = 1 or 0: a word 1 or a
word 0). The head enters from the window in state B or D on the last cell of the nearest word. It runs left over
the words 1 to the nearest word 0, turns that into a word 1, and comes back, rewriting the j words it crossed as
1, 0, 1, 0, ... (from the far end toward the seam); it leaves in state **A** if j is even and **E** if j is odd. If
there is no word 0, a new word 0 is added on the blank tape and the parity is the other way round. This is a binary
counter in a redundant form with four phases:

| phase | words (from the far end) | when full |
|---|---|---|
| A | digits at even places, fixed words 1 between, top digit 1 | becomes B, head leaves in A |
| B | a lone word 0 on top, then as A | becomes A', head leaves in **E** |
| A' | digits at odd places (the fixed words 1 moved by one place) | becomes B', head leaves in E |
| B' | lone word 0 on top, then as A' | becomes A with one more digit, head leaves in **A** |

So the head normally leaves L in state A (*A-mode*: the steady sweeps), and between the overflow of phase B and
the overflow of phase B' it leaves in state E (*E-mode*: the transient's exit sweep, 3 * 2^w bounces or so).
`lean/Dense.lean` proves these rules for all word rows (`inc_zero`, `inc_ones`) and the four overflows for every
width (`ovf_A`, `ovf_B`, `ovf_A'`, `ovf_B'`), kernel-checked.

**The window** is 63 cells of finite control: G' (28 cells), four base-3 digits t0..t3 (4 cells each: `0011` = 0,
`0001` = 1, `0111` = 2), and a slot I (19 cells). In A-mode G' runs through a cycle of 81 bounces; twice per cycle
(39 and 42 bounces apart) it passes a carry on, which is the "+39 / +42" of the visit rule; 16 times per 81 bounces
the head is sent on across the block to the right end (16 visits). In E-mode G' has a cycle of 3 bounces
(`0110 1100 0101 ...`, `0110 1100 1101 ...`, `0110 1101 1101 ...`), and every third bounce adds 1 to the base-3
number t0..t3; a carry out of t3 crosses I, which then sends the head into the block 8 times in state A.

**The block** from cell seam + 63 is a base-3 counter with 4-cell digits, lowest digit first: `0110` = 0, `0010` = 1,
`1110` = 2, and `0000` = h (a half-done digit; the blank tape behind the block reads as h too). Two kinds of
*send* enter it (`py/block.py rules` shows them by direct simulation):

* **A-send** (head enters in state A): the number gains 1; the head returns in B (D if the lowest digit was 1).
* **E-send** (enters in state E): the head passes the zero digits; the lowest nonzero digit d decides: 1 -> h and
  back; h -> 0 and back; 2 -> 0 with the digits above it gaining 4 (base 3: +11); at the blank end a new zero digit
  is appended. **A visit is exactly an E-send on an all-zero block**: this is why the block grows by one word per
  sweep and why steady sweeps are simple. (`(1011)^m 1 0` read from the seam side in 4-cell words is the row of
  zero digits.)

**What a transient is.** At the B-overflow, L flips to E-mode with the block all zero. For about 3 * 2^w bounces
the window counts in base 3 and feeds carries into the block as A-sends, so the block's low digits become a base-3
number that depends on 2^w (the block digits at the end of E-mode, lowest first, were `2122102`, `10220111`,
`10221222`, `201202221`, ... for w = 13, 14, 15, 16, ...). When L overflows phase B' the head leaves in state A again,
with t0..t3 and the block's low digits arbitrary. The *final loop* then normalises them in A-mode: the E-sends that
would be visits on a clean block instead reduce the nonzero digits (value v -> floor(v/3), +4 when v = 2 mod 3, with
the half digits in between), until the block is all zero and the first true visit happens. In every transient seen
the final loop took 123 to 366 bounces (8 to 23 sends) and ended at a steady visit.

**Why the remaining lemma is hard** (all checked by simulation, none proved):

1. *The block is not safe under arbitrary sends.* `py/block.py halt`: from an all-zero block, the sends
   A, E, A, A, A, E, A, A, E (in this order) make the head come back in state C instead of B or D, after which
   nothing above applies. The real run never does this because of the timing of the window, so a regular-language
   invariant (CTL, n-gram CPS, which all fail on this machine) cannot work: the proof must carry the exact relation
   between the window's phase and the block's digits.
2. *The normalisation map has a fixed point.* v -> floor(v/3) + 4 at v = 5 (digits 2, 1): a block that starts the
   final loop with `2 1` in its two lowest places does not clear in a few sends; the pattern moves one word per send
   to the far end of the block (m + 1 E-sends, about 5 * m bounces; `c/seam.c`, start from a phase-B overflow at
   w = 9 with the block digits overwritten by `21`: 492 bounces for m = 60, 1,182 for m = 200, against 48 to 87 for
   other digits). In those small tests the run still reached a steady visit. In the real run 5 * m is of the same
   order as the number of bounces L has left before its next overflow (both are a constant times 2^w), so whether
   such an event stays harmless at every width depends on the constants and lower-order terms, which were not
   worked out reliably, and whether it ever occurs is a question about the base-3 digits of numbers tied to 2^w. It
   has not occurred in the 16 transients seen.
3. *Capacity.* With a short block (m <= 7 at w = 13) the transient does not come back to a steady visit at all.
   `Steady` keeps `w <= m`; the transient needs about w/2 block words, so this one is easy.

So a proof needs: the E-mode loop as an exact base-3 count (window and block together) over about 2^w rounds for a
general width, the block language of the final loop including the travelling pattern, and the arithmetic that the
final loop ends before L's next overflow. That is well beyond the generated case analyses used so far.

**Exact accelerated run.** `c/odo.c` simulates the machine from blank tape and skips only the walk over the zero
digits in front of the first nonzero block word during E-sends (4 steps per word each way, restored unchanged on
the way back in state B or D; if the head ever comes back in another state the skipped words are written out and
the run continues step by step, and the event is counted as a violation). Checked against the plain run: identical
tape hashes at 223 checkpoints (every 1000th crossing of the seam) up to 3 * 10^9 steps (`odo 3000000000 plain
1000` against `odo 3000000000 x 1000`, the `hash` lines). Result: **no halt and 0 violations in 1.1 * 10^17 steps** (165,831,169 visits). The transients:

| w | E-mode starts (step) | visit | E-mode ends (step) | visit | block digits at the end (lowest first) | final loop: bounces, sends |
|---|---|---|---|---|---|---|
| 13 | 30,029,418 | 2,655 | 31,860,224 | 2,687 | 2122102 | 204, 10 |
| 14 | 228,644,076 | 7,502 | 232,865,098 | 7,534 | 10220111 | 324, 9 |
| 15 | 1,187,789,872 | 17,182 | 1,193,487,148 | 17,190 | 10221222 | 204, 8 |
| 16 | 5,362,247,128 | 36,567 | 5,373,782,908 | 36,575 | 201202221 | 243, 13 |
| 17 | 22,745,507,638 | 75,363 | 22,773,545,992 | 75,379 | 1121112201 | 162, 11 |
| 18 | 93,720,808,906 | 153,025 | 93,757,592,880 | 153,025 | 2210002212 | 204, 12 |
| 19 | 380,387,678,892 | 308,334 | 380,461,247,202 | 308,334 | 02110012021 | 324, 17 |
| 20 | 1,532,691,992,766 | 618,966 | 1,532,839,129,606 | 618,966 | 010010211101 | 123, 13 |
| 21 | 6,154,027,202,248 | 1,240,322 | 6,154,639,000,782 | 1,240,354 | 211020100012 | 324, 13 |
| 22 | 24,662,934,679,398 | 2,483,046 | 24,664,317,806,198 | 2,483,086 | 1001112000211 | 243, 21 |
| 23 | 98,747,845,084,466 | 4,968,554 | 98,750,612,122,968 | 4,968,594 | 00222211001001 | 243, 16 |
| 24 | 395,183,745,842,638 | 9,939,571 | 395,186,100,037,864 | 9,939,571 | 00122200102002 | 285, 20 |
| 25 | 1,581,113,902,753,070 | 19,881,568 | 1,581,119,883,563,878 | 19,881,576 | 002122102011011 | 366, 20 |
| 26 | 6,325,229,745,281,072 | 39,765,613 | 6,325,239,162,062,610 | 39,765,613 | 001022011122022 | 243, 15 |
| 27 | 25,302,513,135,250,962 | 79,533,775 | 25,302,537,058,976,020 | 79,533,783 | 2220121222121121 | 204, 10 |
| 28 | 101,213,336,369,863,186 | 159,070,174 | 101,213,394,397,973,264 | 159,070,190 | 02022102220200201 | 162, 23 |

(The visit numbers differ by 0 to 40 between start and end: those are the "transient visits" of the older
description; the block digits and the final-loop lengths show no pattern in w.)

## Evidence

* `c/visits.c` simulates the machine, parses every visit and checks every consecutive pair against the rule:
  up to 2*10^10 steps (70,664 visits) all 61,515 shallow, 8,780 deep and 5 A-overflow pairs follow it, with 0
  exceptions; the 4 B-overflow transients (visits 2656-2687, 7503-7534, 17183-17190, 36568-36575) all end in steady
  phase A one digit wider (the A-overflows are at visits 1040, 4271, 10711, 23624, plus a fifth up to 2*10^10).
* `py/counter.py check` runs every middle case symbolically (bbtools.symtm) and compares with the rule.

## The B-overflow transient

A deep visit in phase B whose carry runs through all digits to the lone 1 (all digits above the low five are 1)
starts a transient that the steady words do not describe:

* **The overflow visit and the transient visits.** The digits all become 0 and V's top 1 reappears in a shorter form
  (`1 0 1 1` in front of the zero digits), and a small extra counter is written into M (cells 3 and 20-22 change).
  The shallow visits go on as before; each deep visit of the transient increments that counter instead of adding to
  V. `py/glue.py transients` runs all 81 possible B-overflows (t, the five low digits, digit 5 when they carry)
  symbolically from `0^inf 1 (U(1))^(k+3) [U(b5)] low M(t) I(7) (1011)^(m+40) 1 0 C> 0^inf`, for all k and m: each
  goes through 0, 8, 16, 32, 40 or 48 transient visits (22, 18, 14, 18, 8 and 1 cases) to its *exit visit*, where the
  run needs a case split on the number of zero digits: the exit visit's inner counter carries into them. 78 of the
  81 exit configurations are different. (In the run: visits 2656-2687, 7503-7534, 17183-17190, 36568-36575.)
* **The exit visit** is a single sweep of about 140.5 * 2^w extra steps (1,157,646 at w = 13, 2,311,558 at w = 14,
  4,606,788 at w = 15, 9,205,384 at w = 16). The head stays in the digit/M region and runs an inner loop of rounds of
  about 140 steps. In the digit cells sits a binary counter C (digits `110100` = 0 and `110110` = 1, i.e. the U words
  read from another cell, a fixed word `110111`, and a low bit `010011`/`011011`): **each round adds 3 to C**. To its
  right a second counter counts the rounds, written in M's cells as four base-3 digits (`0011`, `0111`, `0001`, with a
  lazy carry) and continued over the first copies of the block (`1100` -> `1101`, `0100`, `0101`). At w = 13
  (visit 2688) C starts at 14 with 13 bits, reaches 8189 after 2,725 rounds, overflows at round 2,726 (C = 0, and its
  leading `10` becomes `100`: one more bit, the left end moves out by one cell), counts 0, 3, ..., 16383 = 2^14 - 1 in
  5,461 more rounds (the leading cells become `110`), and the loop ends at the next overflow: 8,188 rounds in all.
  A shorter final loop and a clean-up follow, and the sweep ends at a steady phase-A visit with **one digit more**
  and V = 2^w + 203, 2^w + 323, 2^w + 203, 2^w + 242 in the four cases seen (t and i not necessarily 0).
* The block must be long enough for the second counter: with the visit-2687 tape and m <= 7 the exit visit ends
  early (no halt in 3*10^8 steps from those tapes). In the run m is about 2^w / 5, far more than the ~w/2 copies used;
  `Steady` keeps `w <= m` for this reason.

## What is proved (Lean)

* `lean/Rules.lean`: `back` and `forth` for every m and every tape L.
* `lean/Counter.lean` (generated by `py/counter.py lean`, 169 theorems): the 7 shallow middles `shallow0..6`, and
  162 deep middles `deep_<t>_<lo>[_<b5>]_<z|s>`: for t in {0,1}, every value lo of the five low digits, digit 5 when
  there is a carry, and the carry crossing 0 (`z`) or k+1 (`s`, for every k) 1-digits, for every tape L left of the
  0-digit that stops the carry.
* `lean/Overflow.lean` (generated by `py/glue.py overflow`, 81 theorems `ovA_<t>_<lo>[_<b5>]`): the A-overflow
  middles, `0^inf (U(1))^(k+1) [U(b5)] low M(t) I(7) C> 1 R` to `0^inf 1 (U(0))^(k+1) [U(b5)] low' M(1-t) I(0) 1 F> R`.
* `lean/Visit.lean` (by hand): the visit configurations `vis m (Xv pre b0 ds t i0 i1 i2)` (digits as a list of bits,
  `pre` blank in phase A or a lone 1 in phase B), `visit` (back, a middle, forth: one visit), the invariant `Steady`
  (at least 6 digits above b_0, block at least as long as the counter is wide), and `BStart`, the B-overflow visits.
* `lean/Steps.lean` (generated by `py/glue.py steps`): every visit as a theorem on these configurations (`vs_i`,
  `vd_...`, `va_...`), the dispatch on the low digits and the run of 1-digits above them (`deep_case_<t>_<lo>`), and
  **`steady_step`: a steady visit that is not a B-overflow is followed by a steady visit** (kernel).
* `lean/Steady.lean`: `start` (blank tape to visit 280, step 1,882,602, `native_decide`), the induction `reach_from`,
  and
  * **`halt_needs_B_overflow`**: if the machine halts from blank tape, the run reaches a steady visit that is a
    B-overflow first (native: the start-up);
  * **`halt_needs_later_B_overflow`**: one at step 31,879,658 or later (the run to visit 2688, past the first
    transient, is evaluated by `native_decide` too);
  * **`nonhalting_of_transients`**: if every steady B-overflow visit is followed by a steady visit, the machine never
    halts from blank tape.
* `lean/Dense.lean` (by hand, kernel): the counter L of the odometer description, for arbitrary rows of words and
  any tape to the right: `inc_zero` (nearest word 0 behind j words 1: 6j + 5 steps, leaves in A or E by the parity
  of j), `inc_ones` (no word 0: a new one on the blank tape), and the four phase overflows `ovf_A`, `ovf_B`, `ovf_A'`,
  `ovf_B'` for every width. Not yet connected to `Visit.lean`'s words (the two descriptions cut the tape at
  different cells).
* `lean/Blank.lean`: the halting configurations (only F reading 0 halts), no halt in 10^7 steps.

No `sorry`; `#print axioms nonhalting_of_transients` lists only `propext`, `Classical.choice`, `Quot.sound` and the
`native_decide` evaluation of the start-up.

## Status and the remaining gap

Open. Non-halting is exactly the hypothesis of `nonhalting_of_transients`: each B-overflow transient ends at a
steady visit. The dedicated pass that was meant to prove it found instead why it is hard (see "Why the remaining
lemma is hard" above): the transient leaves the block with base-3 digits that depend on the width
number-theoretically, the block is not safe under arbitrary sends (so no regular invariant), and one digit pattern
(`2 1`) turns the short clean-up into a walk along the whole block whose length is of the same order as the binary
counter's remaining room.

What can be said honestly: the run follows the odometer model exactly for 1.1 * 10^17 steps (16 transients, each
ending in a steady visit after at most 366 bounces); no halt was found; a halt, if any, lies inside or right after a
B-overflow transient at width 29 or more (Lean proves this only for the first transient; beyond it the claim rests
on the exact simulation). There is no heuristic argument of the usual kind either way: each transient is one more
draw of block digits, the dangerous-looking draws have a positive density in a naive model (about 1/9 for the pair
`2 1` in the lowest places, though none occurred in 16), and what such a draw does at large width is not known.

### Next steps

- Decide what a travelling `2 1` pattern does at realistic sizes: start `c/seam.c` (or an `odo`-style accelerated
  version of it) at an E->A flip with the block overwritten, for w = 13..25 and m as in the run, and see whether the
  run reaches a steady visit, flips to E-mode with a dirty block, or halts. This is the cheapest experiment that
  could change the picture (a halting mechanism, or evidence that the pattern is harmless).
- Find the closed form of the block digits at the end of E-mode as a function of w (the number of E-mode bounces
  is fixed by L, the window counts them in base 3 with period 3 * 81, the carries become A-sends): then the question
  "does the low pair ever equal 2 1" becomes an explicit one about 2^w in base 3.
- Lean: connect `Dense.lean` to the window (a finite table: 81 A-mode and 3 E-mode window steps, provable by
  `decide` once the window is a `List Bool` of length 63) and prove the A-send / E-send rules of the block by
  induction on the zero prefix. With these, `steady_step` could be re-proved in a few lines and the E-mode loop
  becomes an induction over L's increments.
- Accelerate further (skip whole steady epochs with the visit rule) to see more than 16 transients.

Tape samples (periodic notation, `w^k` is the word w repeated k times; `X>b` is the head in state X on symbol b; a long middle is cut with `...`):

- step 10,000,000: `10 011^3 010011^7 011^2 010 011^5 1011011^2 1011^3 0111^4 010011^2 011^3 1011^1192 C>1 1001^236 1`
- step 100,000,000: `100110^2 110^4 100110^2 110^6 10 011^5 010 011^3 1011011^2 1011^3 0111^4 010011^3 0111^3998 011 A>1 1001^907 1`
- step 1,000,000,000: `110^4 100110^3 110^6 10 011^11 0100 1^3 011^2 10^2 0111^3 011^2 1011^4 011^6 1011^1088 10 B>1 0110^14656 011`

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 18, history 1 up to width 14, history 2 up to width 13, history 3 up to width 11, LRU history up to width 13 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 16, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: E with 0 under the head, 1 right, 0 two right.

## Pages

- [`pages/holdouts/1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC/explainer.html`](../../pages/holdouts/1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC/explainer.html)
- [`pages/holdouts/1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC/proof-status.html`](../../pages/holdouts/1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC/lean/check.sh   # about 12 minutes
cd holdouts/1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC
gcc -O2 -o /tmp/visits c/visits.c && /tmp/visits 20000000000     # the model against simulation, about 90 s
python3 py/counter.py check                                       # the symbolic middle cases
python3 py/glue.py check                                          # the A-overflow middles
python3 py/glue.py transients                                     # the 81 B-overflows up to their exit visits
gcc -O2 -o /tmp/odo c/odo.c
/tmp/odo 3000000000 plain 1000 | grep hash > /tmp/p.txt; /tmp/odo 3000000000 x 1000 | grep hash > /tmp/a.txt
cmp /tmp/p.txt /tmp/a.txt && wc -l /tmp/p.txt                     # 223 equal tape hashes: the skipping is exact
/tmp/odo 4000000000000000                                         # the 16 transients, exact, accelerated (needs 2 GB)
python3 py/block.py rules; python3 py/block.py halt               # the block's send rules; an unsafe send sequence
gcc -O2 -o /tmp/seam c/seam.c && /tmp/seam 9 0 0 200 400000000 7 21 0000 0   # the travelling 2 1 pattern
python3 py/glue.py overflow > lean/Overflow.lean; python3 py/glue.py steps > lean/Steps.lean   # regenerate
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE`](../1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D
- [`1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD`](../1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E

<!-- end of related machines -->
