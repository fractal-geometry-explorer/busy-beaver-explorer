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

`py/pascal_gaps.py` checks both statements for every gap of up to 14 words (all 32,766). The algebra is now in Lean (`lean/Gaps.lean`, below). A
halt still needs, at such a sweep, a `y` or `0` before the `10` (in the data it was `x` all 131 times). So the open
question is now about binary digits: which gaps the right end hands to a newborn `10`, and what word stands before the
defect at the sweeps `t = 2^b - 1 - s mod 2^b`.

## The danger pattern in Lean (21 November 2026, `lean/Danger.lean`)

* `danger_halts`: B at the start of `y 10 y^n 0` halts, for every `n`. The `y` is a run `1 1 0` (B leaves it as
  `0 1 1`); on the defect B goes into token mode (`B 1 -> 0 D`, `D 0 -> 0 F`); F crosses each `y` turning it into `000`
  (`token_y`); F reads the wall's 0 and halts.
* `shield`: with `x` before the defect, `x 10` is the single run `1 1 1 1 0`, which B rewrites to `0 0 0 1 1` and leaves
  in B at the start of the gap, the ordinary way.

So the danger pattern found in the data is a real halting shape, and the word in front of the defect decides whether
the right sweep reaches it in token mode.

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
  defect moves and the gap shrinks, and the linear picture restarts (the exact rule is the jump of the next section). If the gap were all `y`
  at such a sweep it would be `y 10 y^n 0`, the danger pattern.

So the danger pattern is a coincidence of two Lucas sums: the gap, whose all-`y` times are `t = 2^b - 1 - s` (mod
`2^b`) for a gap that is Pascal row `s`, and the word before the defect, which is `y` at the `t` where the digit-masked XOR
of the left words is 1. In the data the two never coincide: all 93 snapshots with an all-`y` gap have `x` before the defect, and
every `y` before the defect came with a gap that was not all `y`. A proof along these lines would have to control the left words that a newborn defect sees, which are rule-102 images of
the bulk, and the hops.

## The defect's jump, and one map for a whole lifetime (21 November 2026, `lean/Hop.lean`)

A deep sweep is a round trip that reaches a bulk `10` defect `T` and turns at the wall after its gap. Lean proves what
it does in both cases, for all word strings `P`, `G`, `C` and all `j`, `a` (x102 is rule 102, `x102(w, q)` has `q` after
the end):

* `shielded` (`x` before `T`): `P x T G y 0` becomes `x102(P, x) T x102(y G y, y) 1`. The defect moves one slot left.
  Counting `T` as a `y`, that is rule 102 on the whole line `P x T G y` (`x102_shielded`): the left words and the gap
  are one rule-102 line, and the defect sits in the slot whose new value is `x xor y = y`.
* `jump` (`y` before `T`): `P y T y^j x^(a+1) C y 0`, with `C` empty or starting with `y`, becomes
  `x102(P y, x) x^(j+a+1) T x102(C y, y) 1`. In token mode the right sweep crosses the `y`s; the first `x` throws B back
  into ordinary mode one cell late, so the defect **jumps forward to the last slot of the gap's first `x` block**, and
  the `j + a + 1` slots it jumped over become `x`.
* With no `x` before the wall the jump has nowhere to land: `P y T y^n 0` is the danger pattern and halts
  (`danger_halts`). If the first `x` block runs into the wall, the defect and the wall cancel (a merge).
* `clock`: after a jump over `m = j + a + 1` slots the words before `T` are `Q y x^m`. Each shielded sweep turns
  `Q y x^k` into `Q' y x^(k-1)`, so exactly `m` shielded sweeps follow and then the word before `T` is `y` again: **the
  next jump comes exactly `m` sweeps later**, whatever the words further left.

`py/hop_rule.py` checks the three rules with the machine's table (8,001 shielded and 40,320 jump cases, 504 danger
cases, all agree). `c/turns.c` and `py/defect_life.py` follow every deep sweep of the real run to 1.2·10^7 steps: 54
shielded sweeps, 10 jumps and 3 merges (one per lifetime), all as the rules say; the gap matches the series model below
on every word the old gap determines (63 of 63), and all 10 jumps and merges after a first jump came exactly `m` sweeps
after the previous one.

**The two Lucas sums, side by side.** Read the gap with the defect as the constant term, `W = 1 + g0 z + g1 z^2 + ...`
over GF(2). Then every sweep of a defect's life is one map:

* shielded sweep: `W -> (1 + z) W`;
* jump: `W = (1 + z + ... + z^j) + z^L C` with `L = j + a + 2` (a run of `j + 1` ones, then `a + 1` zeros, then `C`,
  which starts with 1) becomes `(1 + z) C`; with the `j + a + 1` shielded sweeps that the clock then forces, jump to jump
  is **`F(W) = (1 + z)^L C`**: strip the leading run of ones and the run of zeros after it, multiply by `(1 + z)^L`.

The words left of the defect enter only once: they fix the first jump, at the first sweep `s` where their Lucas sum
(the XOR of the `k`-th left words over the `k` whose binary digits lie inside those of `s`) is `y`; the gap is then
`(1 + z)^s W_birth`. From the first jump on, the left words never matter again (the clock), and the lifetime is the
orbit of `F`. It halts exactly when, at some jump, the leading run of ones of `W` reaches the wall (the gap is all
`y`), and it ends quietly when the first run of zeros reaches the wall first. So "the gap is all `y` while a `y` stands
before the defect" is now a statement about one sequence of power series.

What this does not settle: `F` alone does not keep the run of ones short. For random gaps the run length `j` at a jump
is geometric (`py/fmap.py`: `j = 0, 1, 2, 3` in 50, 25, 12, 6 percent of 171,912 jumps), so a halt is a matter
of which gaps are born, not something the map rules out. In the real run `j` was 0 or 1 at all 10 jumps and 3 at two
merges. The no-halt argument therefore still needs the births: that `y 0 x^k 0` (the only way a bulk `10` forms) never
appears again after 8.5·10^6 steps, which is about the walls and the right end, not about the defect.

## Which gaps the jumps can make dangerous (22 November 2026, `lean/Gaps.lean`)

Read the gap as the series `W = 1 + g0 z + g1 z^2 + ...` (defect = constant term) as above. `Gaps.lean` first ties the
series to the words of `Hop.lean`: on every coefficient the old gap determines, the shielded sweep leaves `(1 + z) W`
(`ser_shielded`) and the jump leaves `(1 + z) C` (`ser_jump`, `ser_rest`). Then it inverts `(1 + z)^t`:

* `mask t` is the series with coefficient `k` equal to 1 exactly when `k` and `t` share no binary 1. It is
  `(1 + z)^(-(t+1))` (coefficient `C(t + k, k)` mod 2), and `(1 + z) mask (t + 1) = mask t` is Pascal's rule
  (`mz_mask`), so `(1 + z)^t mask t = 1 + z + z^2 + ...` (`mzi_mask`).
* Multiplying by `(1 + z)^t` keeps and reflects agreement on the first `r` coefficients (`mzi_agree`), so **after `t`
  shielded sweeps the first `r` coefficients are all `y` iff they were `mask t`** (`reach_ones`).
* `mask` has period `2^b` below `2^b` (`mask_period`), so a gap of fewer than `2^b` words ever becomes all `y` iff it
  is `mask t` for some `t < 2^b` (`pascal_reach`). This is the Pascal-row statement of the Lucas section
  (`mask t` = row `2^b - 1 - t`), now proved for every length instead of checked up to 14 words.
* **The next jump** (`next_jump_run`): at a jump over `y^j x^(a+1)` with rest `C`, `L = j + a + 2`, the first `r`
  coefficients of `F(W) = (1 + z)^L C` are all `y` iff `C` agrees with `mask L` on its first `r` words. So the run of
  `y`s at the next jump is the length of the common prefix of `C` and `mask L`, minus one, and the danger pattern at the
  next jump needs `C = mask L` on the whole gap: one gap per `(j, a)`, at most about `n^2 / 2` of the `2^n` gaps of
  `n` words (190 of 1,048,576 for `n = 20`). Since `mask L` starts `y`, then `x` at `k = 2^(v_2 L)`, an odd `L` needs
  `C` to start `y x`, and a long run needs `L` divisible by a large power of 2.

`py/jump_gaps.py` checks the agreement rule on 163,800 cases (every `C` up to 12 words, `L` up to 40) and on the real
run (`./turns 12000000 150 > turns.txt; python3 py/jump_gaps.py turns.txt`): at all 10 jumps that have a successor in
the same lifetime, the next run equals the agreement minus one. Two came close. At 2.53·10^6 steps (`j = 1`, `L = 6`)
the rest `C = yyxx` is `mask 6` on every word the old gap holds; the next run was 3 because the gap had grown to 7 and
the words that entered at the wall did not continue the mask. At 5.44·10^6 steps (`L = 3`, `C = yxxxx` against
`mask 3 = yxxxy`) the agreement was 4 of 5: run 3 where 4 would have halted.

What this does not settle: the jump map now pins down the dangerous gaps exactly, but the words that enter the gap at
the wall between jumps are not controlled (the wall moves, and the series model only covers the words the old gap
determines), and the near miss at 2.53·10^6 steps shows that they can matter. Two ways forward: model the wall's
contribution between jumps (what the walls feed in is again a rule-102 image of the bulk), or return to the births and
show that `y 0 x^k 0` never forms again, so that no bulk `10` exists to jump.

## One round trip is a cellular automaton on cells (22 November 2026, `lean/Trip.lean`)

Drop the words and look at cells. A round trip starts when the head first stands on a new leftmost cell (blank, state A).
Let `Q` be the first cell with `c[Q] = c[Q+1] = 0`. If no 1 stands alone (`0 1 0`) before `Q`, then the cells from the start
to `Q` are runs of at least two 1s, each followed by one 0, and Lean proves the whole trip (`trip`):

* cells `lo .. Q` become `c'[p] = (c[p] == c[p+3]) = 1 xor c[p] xor c[p+3]`, with `1 1 0` imagined after `Q` (`ca3`, `ca3_getD`);
* `c[Q+1]` becomes 1; nothing right of it is read; the head ends on `lo - 1` in A;
* it takes `4 (Q - lo) - 6 z + 15` steps, `z` the zeros in `lo .. Q+1` (`trip_steps`).

The right sweep turns each run `1^m 0` into `0^(m-1) 1 1` (`rrun`). The left sweep spends **one step per cell**: arriving at a
cell, its state names the three original cells to the right (E = `111`, C = `110`, B = `101`, A = `011`, `sg`); it reads
`!(c[p] && c[p+1])`, which the right sweep left, writes `c[p] == c[p+3]` and moves on (`lstep`). The trip with `Q = lo` is the
3-step "blip" at the left end, covered by the same theorem.

So the machine is three interleaved copies of rule 102 (cells `p, p+3, p+6, ...`), run each trip from the left end up to the
first `00`. A 0 only ever spreads three cells left. The words `x = 111`, `y = 110` are one copy carrying data and two copies
fixed at 1; walls are where the data passes to another copy, and the rule does not see them. `Xor.lean`'s epoch is the
special case of clean words; the wall rules (R_k walls `1^(3k) 0` counting down to `00`, a `00` hit becoming `1^(3K) 0`)
are all consequences.

The only thing a round trip cannot cross is a lone 1 before `Q` (the right sweep's token mode, where F0 lives). `iso_birth`: in a
tape where no three neighbouring cells hold two 0s, an output `0 1 0` at `p .. p+2` comes only from `0 1 1 1 1 0` at `p .. p+5`.

**Token mode, in cells** (`lean/Token.lean`). A lone 1 sends the right sweep into token mode; it crosses the `110` words
after it and drops back one cell late at the first `111`. `rtok`: the cells and state it leaves are exactly those of the
right sweep over the *filled* tape, where the holes at `i+1, i+4, ..., i+1+3j` (the lone 1's 0 and the 0s of the `j`
words) are 1s. So the left sweep cannot tell, and `trip_tok`: any round trip over ordinary runs and token chains is `ca3`
of the filled tape. By `ca3_diff` that is the plain automaton with two cells flipped, `i-2` and `i+1+3j`, which is the
defect's jump of `Hop.lean` as a rule on cells. `tok_halt`: if the `110` words run into a 0 the machine halts in F.
`py/trip_model.py` applies this map to whole tapes: it reproduces all 10,528 round trips of the first 6·10^7 steps,
token-mode trips and right-end trips included.


**Fast simulator** (`c/trips.c`). Trips the theorem covers are done with 64-bit word operations; trips with a lone 1 before `Q`
and trips that reach the right end (with its fixed `10`) are run on the machine's table. Mode 1 also runs every trip on the
machine and compares the whole tape and the step count.

* `./trips 10000000 0`: 52,496,781,276,447 steps, no halt. 18 trips with a lone 1 before the turn, all before 8.5·10^6 steps
  (the known `10` lifetimes).
* `./trips 300000 1`: no difference from the machine in any trip.

**Wall words, in cells.** Take a segment between two walls (its 0s in one copy). At each pass of the sweep through it, its 0s
are multiplied by `1 + u` (`u` = three cells left): nothing is cut off at either end, since its neighbours' 0s are in other
copies. So after a plain pass the segment has an even number of 0s. A turn at its left wall (`00`) deletes its first 0; a turn
at its right wall applies `1 + u` and deletes its last 0. A bulk `10` is born exactly when a turn at the left wall finds a
single 0 left (the old `y 0 x^k 0`). An even count minus one is 1 only when `(1 + u) S` has two terms, i.e. `S` is
`y^n` (0s every three cells), and the left wall must reach `00` before a pass restores two 0s. So a birth needs a trip whose
turn ends a y-only segment with a 3-cell wall `111` on its left (PRE in `trips.c`). In the run there are exactly 5 such trips
(round trips 92, 108, 1,904, 2,608, 3,403), each followed by the token-mode trips of one `10` lifetime, and none after that
in 10^6 trips. The y-only segments that keep forming sit 10, 17, 24 and 53 cells from the right end, behind walls of 6, 9 or
18 cells, as part of the right end's periodic cycle (the last 75 cells repeat exactly every 10 right-end visits, growing 4 cells).

What a proof still needs: (1) the right end's cycle as a proved rule, which would make the near-end y-only segments
harmless; (2) that further left no y-only segment ends at a turn behind a `111` wall. (2) is about segment contents, which are
Pascal-triangle images of what the right end emits, so it is the same open question as before, but now with exact linear
dynamics and no wall rules in between.

## The right end is a closed 12-entry cycle (25 November 2026, `py/rend_cycle.py`)

The cell automaton gives a locality rule: a round trip writes every cell `p` up to the turn as `1 xor f[p] xor f[p+3]`
(`f` the tape with lone-1 holes filled), so a cell's new value depends only on cells to its right. Cut the tape at any
cell `P`. A trip changes the suffix `P, P+1, ...` in only three ways: not at all (it turns left of `P - 1`); by setting
`c[P]` to 1 (it turns at `P - 1`, which needs `c[P-1] = c[P] = 0`); or by a map that depends only on the suffix and on how
the right sweep arrives at `P`. In ordinary mode the only outside cell that matters is `c[P-1]`, and only when the suffix
starts `1 0` (a lone 1 at `P` iff `c[P-1] = 0`); running the machine on `0` + suffix and on `011` + suffix covers both cases.
Arriving in token mode (a lone 1 further left whose `110` words reach `P`) is the only other case. So **any suffix is a
closed system, driven only by when the sweep enters it**, as long as no token-mode sweep reaches the cut.

`py/rend_cycle.py` takes the last 100 cells (counted back from the rightmost visited cell, so the cut moves right as the
tape grows) and closes the set of such windows under all three moves. The set has **12 windows**. Each has a 1 at the cut, so
the second move never applies. Each has a single successor whatever `c[P-1]` is. Together they form one cycle of 12 entries.
So once the real run holds one of them, the last 100 cells go round this cycle forever and the right end never halts,
whatever happens further left, unless a right sweep arrives at the cut in token mode. Only one of the 12 windows (number 7,
`110 110 0 ...` at the cut) would halt on such an arrival. In the real run (`TL=100 ./trips N 0` and the script) the window is in the
cycle from round trip 2,112 on. Every later change is the predicted successor: 496 up to 3·10^6 trips (4.7·10^12 steps).

Shorter and longer windows behave the same way when they close (30 cells: 5 windows, the 5-phase cycle of the first
section; 154 cells: 36). Some lengths do not close, because their cut sometimes starts `1 0` and then `c[P-1]` decides
between a lone 1 and an ordinary run. So the right end is settled: **a halt needs a lone 1 in the bulk**, a token-mode sweep
starting left of the last 100 cells. That is the question of the previous sections (no new bulk `10` after 8.5·10^6 steps),
and the left end, where short-lived lone 1s and `110` chains come and go, is the other piece (next section).

## The left end is closed too, whatever the first segment holds (28 November 2026, `py/lend_closure.py`)

The same locality works at the left end, in the frame of the new blank cell `lo`. A trip rewrites the first `L` cells
from cells `lo .. lo+L+2` only. Beyond the first few cells the tape is the first segment, the oldest and longest one:
at every dump up to 10^6 trips, all 0s from `lo + 20` on lie in one residue class, and that segment is
tens of thousands of 0s long. So the abstraction takes the window, the cell just after it (known: it left the window on the
trip before) and two **free** cells after that, where only the one in the segment's class may be 0. It runs the machine
on these cells and a tail `111111 00`, which ends any `110` chain and gives the turn; by locality the tail cannot
change the window. Then it puts a new blank cell in front.

For `L = 20, 24, 30` the set closes with 448, 1,152 and 4,608 states, and for `L = 36` with 18,432. None halts, and
the window never pushes a 0 of another class into the segment. All 10 real left windows dumped up to 10^6 trips lie in the
set. So **the left end never halts, whatever the first segment contains**, provided (a) the first segment stays wider than
the window and (b) no `110` chain from a left-end lone 1 runs through the whole first segment to its wall. Chains do run
into the segment (2 of the 4,608 states). In the real run the longest left-end chain up to 1.5·10^6 trips is 62 cells, against a segment of about 10^5 cells.

Together with the right end: a halt needs a lone 1 that the right sweep meets in token mode in the bulk, with `110`
words up to a 0. That is either a bulk `10` defect (born only after a PRE trip, none after trip 3,403), or a whole
segment, the first one included, turned into `110` words. Both are statements about segment contents, which follow
rule 102 between walls (`(1 + u)` per pass, one 0 trimmed per turn). That is now the whole open problem.

## The right end to depth 12,000: one traveling profile (28 November 2026, `c/rend_orbit.c`)

The closed window of the right end works for much longer windows if the cut is placed well. When the suffix starts with
`1 1`, the cell before the cut cannot matter: there is no lone 1 at the cut and no `00` across it, and no turn just left
of it can touch the suffix. Dropping cells from the left of a window is always sound, because every suffix obeys the
same rule. So `c/rend_orbit.c` keeps the last `L` cells, drops cells from the left until the window starts `1 1`, and runs
the machine on `0` + window for each entry. Then every entry has **exactly one outcome**, given no token-mode arrival from
further left. The window has finitely many values, so the sequence is eventually periodic. The program runs it until a window
repeats, then confirms the repeat cell by cell.

| L | transient (entries) | period (entries) | growth per period | lone 1s or halts |
|---|---|---|---|---|
| 100 | 0 | 12 | 4 cells | none |
| 800 | 23,998 | 117 | 4 cells | none |
| 1,500 | 100,187 | 234 | 4 cells | none |
| 3,000 | 444,501 | 479 | 4 cells | none |
| 6,000 | 1,873,945 | 966 | 4 cells | none |
| 12,000 | 7,686,155 | 1,921 | 4 cells | none |
The start is the real tape at round trip 599,938, and the windows it produces are the real ones: from the tape at trip 299,862,
the window after 742 entries is exactly the real tape at trip 599,938 on its last 1,400 cells. So **the last 12,000 cells never
hold a lone 1 and never halt from then on** (the direct run shows none before either, after trip 3,902), unless a right sweep arrives from deeper in token mode.

Every period grows the right end by the same 4 cells, which is one turn of the 12-entry cycle at the end. So near the right end the
tape converges to one **traveling profile**: the same cell pattern, shifted 4 cells right per right-end cycle, entered about
`L / 6.3` times per cycle at depth `L`. In the profile the segments get longer with depth. Here is one profile window of 3,000 cells:

| depth of the segment's left wall | 0s | span (cells) | wall gap |
|---|---|---|---|
| 2,517 | 84 | 480 | 10 |
| 2,060 | 79 | 447 | 16 |
| 1,651 | 67 | 393 | 22 |
| 1,317 | 45 | 312 | 10 |
| 1,064 | 48 | 243 | 16 |
| 862 | 34 | 186 | 13 |
| 696 | 24 | 153 | 31 |
| 563 | 22 | 102 | 16 |
| 436 | 24 | 111 | 19 |
| 348 | 10 | 69 | 7 |
| 296 and less | 2 to 12 | 3 to 51 | 1 to 19 |

The span is about a fifth of the depth. So every short segment, where a `10` defect was ever born (all 5 births were within
94 cells of the end), now lies inside a proved window. Deeper than that, every segment of the profile is hundreds of cells long, and they grow with depth. The open question narrows to this: **no long segment deep in the bulk ever turns entirely into `110` words.** The tape
deeper than the profile is older (cells born at the left end and filled from the right). It shows the same picture: segments
with tens to tens of thousands of 0s.


**Deeper than the proved window** (`SEG=1000 ./trips 4000000 0`, every bulk segment sampled every 1,000 trips, between `lo + 40`
and 12,000 cells from the end): no segment there has fewer than 100 0s. The closest any came to all `y` is 195 `x` words out of
450 (100 to 999 0s) and 466 out of 1,006 (1,000 or more). So deep segments look like even mixtures of `x` and `y`, with no sign of
the Pascal structure an all-`y` segment would need. This is a measurement, not a proof.

## Lean

`lean/Rules.lean` (from `py/rules.py`): ten shift rules over 3-cell words (and runs of 0s), found by a symbolic
search over all words of 1-3 cells, each for every n and every tape around. `lean/Xor.lean` and `lean/XorLucas.lean`:
the rule 102 epoch and its closed form (section above). `lean/Danger.lean`: the danger pattern halts. `lean/Hop.lean`:
the shielded sweep, the jump and the jump clock (section above). `lean/Gaps.lean`: which gaps sweeps and jumps can
turn into the danger pattern (section above). `lean/Trip.lean`: one round trip is the cell automaton
`c'[p] = 1 xor c[p] xor c[p+3]` up to the first `00`; `lean/Token.lean`: with lone 1s, the same on the filled tape, and the halt (section above).

## Halting

Only F1 halts. Open; n-gram CPS (widths 3..7) fails; no halt in 10^9 steps (C). `bbtools.cycles` (K = 2) makes
little progress (the string is rewritten, not shifted, so there are no linear regimes).

## Notes for later

* Done: the sweep pair is the XOR rule, proved in Lean for all lengths (`lean/Xor.lean`), with its Lucas closed form.
* Done (25 November 2026): the right end's cycle, as a closed system of 12 windows of the last 100 cells (`py/rend_cycle.py`).
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
