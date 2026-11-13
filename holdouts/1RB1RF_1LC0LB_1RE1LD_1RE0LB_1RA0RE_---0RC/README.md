# 1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC

bbchallenge id 154101. One of the six-state holdouts whose halting from blank tape is open. Decoded: it is a
**binary counter V at the left end that gains 39 or 42 (alternately) every 8 sweeps**, with a 3-bit sweep counter
and a long block (1011)^m at the right end that grows by one copy per sweep. **Proved in Lean: the machine can halt
only during a B-overflow transient** (the moment, once every second doubling of V, when V overflows in phase B), and
not during the first one: every sweep that does not start such a transient (all shallow and deep sweeps, and the
A-overflows) is proved for all counter values, widths and block lengths, and the run from blank tape through the first
transient is evaluated. What is left is one lemma (`H` of `nonhalting_of_transients`): that every B-overflow
transient ends in a steady visit again. Its long *exit visit* (about 140.5 * 2^w steps inside one sweep, two nested
counters) is decoded only roughly and not proved. Halting is open, but the machine almost certainly never halts.

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
* `lean/Blank.lean`: the halting configurations (only F reading 0 halts), no halt in 10^7 steps.

No `sorry`; `#print axioms nonhalting_of_transients` lists only `propext`, `Classical.choice`, `Quot.sound` and the
`native_decide` evaluation of the start-up.

## Status and the remaining gap

Open. Non-halting is now exactly the hypothesis of `nonhalting_of_transients`: each B-overflow transient (one of 81
cases, for every width) ends at a steady visit. The transient visits before the exit are routine (symtm runs them all
symbolically; Lean theorems for them would be generated the same way as Counter.lean, about 5 per case). The exit
visit is the real work: its two counters need a proof by induction on the rounds of the inner loop, for 78 different
start configurations, with the second counter's digits written over block copies.

Heuristically the machine does not halt: the exit visit of every case is a fixed program run on counters whose
lengths grow with w, the four seen (w = 13..16) and the symbolic runs up to the exit for all 81 cases behave alike, and
2*10^10 steps of direct simulation follow the model with no exception.

### Next steps

- Decode the exit visit exactly: the encoding of the round counter (base-3 digits with a lazy carry, then digits on
  the block copies), the final loop and the clean-up, and the start value of C, as a rule in w and the case (the
  digit counter C, +3 per round, two passes, is decoded above).
- Prove one round of the inner loop with symtm (two carries: through the 1-digits on the left and through the
  counter digits on the right), then the induction over the rounds in Lean, for one case, then for all 78.
- Generate the transient visits before the exit (Lean, from `py/glue.py transients`) and fill in `H`.

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
. /etc/profile.d/lean.sh && holdouts/1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC/lean/check.sh   # about 11 minutes
cd holdouts/1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC
gcc -O2 -o /tmp/visits c/visits.c && /tmp/visits 20000000000     # the model against simulation, about 90 s
python3 py/counter.py check                                       # the symbolic middle cases
python3 py/glue.py check                                          # the A-overflow middles
python3 py/glue.py transients                                     # the 81 B-overflows up to their exit visits
python3 py/glue.py overflow > lean/Overflow.lean; python3 py/glue.py steps > lean/Steps.lean   # regenerate
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE`](../1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D
- [`1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD`](../1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E

<!-- end of related machines -->
