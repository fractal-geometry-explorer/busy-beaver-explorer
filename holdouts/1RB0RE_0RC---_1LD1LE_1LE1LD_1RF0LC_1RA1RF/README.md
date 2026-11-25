# 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF

bbchallenge id 75625. A binary word written in 4-cell letters 1110 and 1111; every leftward sweep replaces it by its running parity (XOR from the right), so the space-time diagram is Pascal's triangle mod 2 (Sierpinski triangles), in epochs that each grow the tape by about 1.75.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 0RC | --- |
| C | 1LD | 1LE |
| D | 1LE | 1LD |
| E | 1RF | 0LC |
| F | 1RA | 1RF |

## What it does

Letters `u = 1110`, `v = 1111`. Between sweeps the tape is a word in `u` and `v` (blocks `1^(4k+3) 0`) plus a short
fixed end on the right. Step 2,003,981:

    u^3 v u v^2 u v u v u^3 v^2 u v u v u v^2 u^2 v^3 u v^2 u v^3 u v u^3 ...   (about 650 letters)

**Leftward sweep = running parity** (proved, `lean/Rules.lean`). The head is in D (even) or C (odd) on the last cell
of a word `111x`:

| state | letter | writes | next |
|---|---|---|---|
| D | u = 1110 | 0101 | C |
| D | v = 1111 | 1111 | D |
| C | u | 1111 | D |
| C | v | 0101 | C |

so behind the head is the running XOR from the right (u = 1), written as 1111 (even) / 0101 (odd). Iterating the
running XOR gives Pascal's triangle mod 2: the Sierpinski triangles of the space-time diagram.

**Epochs** (observed, `c/epochs.c`). The head bounces between the left end and an inner wall that moves left; the
zone between them is rewritten every bounce, the tape right of the wall is frozen; when the zone closes, a full
crossing starts a new epoch.

| step | left end | right end |
|---:|---:|---:|
| 47,799 | 374 | 47 |
| 145,962 | 703 | 58 |
| 487,979 | 1,319 | 69 |
| 1,427,948 | 2,265 | 80 |
| 4,277,179 | 4,020 | 91 |
| 13,419,889 | 7,237 | 98 |
| 40,483,837 | 12,641 | 109 |
| 124,076,294 | 22,085 | 112 |
| 383,276,545 | 38,918 | 115 |
| 1,162,585,978 | 68,091 | 130 |

## Twin

`1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF` has identical configurations at 12 of the 13 epoch starts up to
1.7·10^9 steps (about 1.5 times later); see its folder.

## The tape as a list of blocks (F11, 13 November 2026)

Read the tape as blocks of 1s separated by single 0s. Every meeting of the head with a block or a separator is one of
the rules of `lean/Blocks.lean` (kernel; written by `py/blocks_rules.py`):

| going | situation | what happens | rule |
|---|---|---|---|
| right, F | a block | crossed | `f_block` |
| right, F | separator, then a block of one cell | separator filled, the cell erased, the next separator filled, F goes on: the blocks on both sides gain a cell each | `f_single` |
| right, F | separator, then a block of two or more | **turn**: the block on the left gains two cells, the block on the right loses two, the head leaves in D | `f_turn` |
| right, F | `0 0 0 1` | filled | `f_three_zeros` |
| right, F | `0 0 0 0` (right end) | writes `1011`, leaves in E | `f_end` |
| right, F | `0 0 1` | **halt** | `halt_F` |
| left, D | a block | crossed and kept; the separator after it is filled and the next block is entered in E | `d_block`, `d_sep` |
| left, E | a block | every second cell erased (the block becomes blocks of one cell); if its length is odd the next separator is filled and the next block is entered in D, if even E reaches the separator and turns right | `e_pairs`, `e_last`, `c_sep`, `c_last`, `e_turn` |

So a leftward pass keeps and breaks up blocks in turn (that is the running parity of `lean/Rules.lean`, a block
`1^(4k+3) 0` being the word `v^k u`), and a rightward pass merges what was broken, until it meets a block of two
or more cells and turns there.

`python3 py/blocks.py 100000 4016 70` prints the block lists at every turn. What they show (observed, one epoch
followed turn by turn, steps 4,104 to 7,890):

- **Growing phase.** The head bounces between the left end of the tape and a turning place that moves right, 2 to 20
  cells per bounce, eating the blocks beyond it two cells at a time (27, 20, 24, 28, 32, 49, 53, 73, ... 155 cells
  from the left end). At each turn on the right the zone is a list of blocks `1^(4k+3)` (the last one a cell
  longer); at each turn on the left it is blocks `1^(4k+1)` separated by odd numbers of one-cell blocks.
- **Crossing phase.** When the turning place reaches the right end of the tape, the head crosses back to the left end
  in short bounces (8 to 28 cells wide), leaving behind it blocks of 3 and pairs `1, 5` (the 4-cell words `1110` and
  `1011`), which the next growing phase eats.

## Halting

Only B1 halts; B is entered only from A0 and A only from F0 (`1RA`). So the machine halts exactly on `F> 0 0 1`:
`halt_F` (`lean/Blocks.lean`) and, for the converse, `halt_route` (`lean/Route.lean`: two steps before any halt the
machine is in F on `0 0 1`). An earlier version of this page said `F> 1 0 1`; that was wrong (F on a 1 stays in F).

One way to put `0 0 1` on the tape is a turn at a block of exactly two cells that has another block after it
(`turn_two`): the turn erases the block and leaves its separator next to the next one. In the run from blank tape
(`c/turns.c`, 10^10 steps, 139,833 turns of F):

- every turn was at a block of odd length (3: 36,463 times; 5: 46,436; 7: 19,254; 9: 20,280; ...), except 22 turns
  at a block of exactly two cells, and each of those was the last block of the tape, with blank tape after it;
- F met two 0s in a row 42 times, each time at the right end of the tape with only blank cells beyond.

So up to 10^10 steps the question is decided at the right end only, about twice per epoch. This is an observation.
What would make it a proof is an invariant that keeps every block that is turned at odd, away from the right end, and
a description of the right end; neither is proved.

Regular-language deciders tried here (all fail, i.e. their closed sets contain a halting configuration; none of this
says anything about halting): see "Deciders tried" below.

- No halt in 10^10 steps (`c/turns.c`).
- See "Pascal's triangle and Lucas' theorem" below: Lean now proves that an odd frozen block at a right turn halts,
  whatever the zone, and the 2-cell-letter invariant (observed to 10^10 steps) is what rules it out.

## Pascal's triangle and Lucas' theorem (21 November 2026)

**One bounce is one row of Pascal's triangle mod 2 (Lean, every zone).** At a right turn the head is in E just right of
the zone, on the first cell of the frozen tape. The zone is a word `w` in `u = 1110` (1) and `v = 1111` (0) after a
prefix that is empty or one 1. If the frozen tape starts `1 1 1`, then for **every** word `w` (`bounce`,
`lean/Pascal.lean`) the machine is back at a right turn after 8|w| + 6 or 8|w| + 8 steps, with

- the zone `T(w)`: write a 1 after the last letter, then replace each letter by the XOR of it and all letters to its
  right (the running XOR of `w 1` from the right), so the zone grows by one letter;
- the prefix kept if `w` has an odd number of `u`, toggled otherwise;
- the frozen tape two cells shorter.

The pieces: the left sweep in C (odd) / D (even) writes `0101` / `1111` (`sweep`), the left end toggles the prefix
(`lend`), F rewrites `0101` as `1011` going right (`rsweep`), and `1011 1011 ... 11` regroups as `11 1110 1110 ...`
(`regroup`). A frozen block of `2k + 1` cells gives `k` bounces (`bounces`).

**The rows in closed form (Lean, Lucas' theorem).** Number the letters from the right end of the zone (0 next to the
frozen tape) and flip letter 0; then a bounce is "running XOR, then shift by one", so the space-time diagram obeys
Pascal's rule (`diagram`, `lean/Lucas.lean`). After `j` bounces letter `i` of the flipped zone is the XOR of the
flipped starting letters `d_k` with `C(i - k - 1, j - 1)` odd, and by Lucas' theorem that coefficient is odd exactly
when `i - k >= j` and the binary digits of `j - 1` and `i - k - j` are disjoint (`closed_form`; `pascal_rule` proves
Pascal's rule for the bit test from scratch, without Mathlib). Every Sierpinski triangle in the space-time diagram is
an instance.

**What it says about halting: the zone does not matter, the frozen tape does.** Let `m` be the length of the block of
1s under the head at a right turn.

| frozen tape from the head | next | where |
|---|---|---|
| `1^m 0 ...`, m >= 3 | one bounce, m - 2 | `bounce` (Lean) |
| `1 0 1 ...` (m = 1) | halt, F reads `0 0 1`; so any odd m followed by `0 1` halts, whatever the zone | `halts_of_odd` (Lean) |
| blocks `2, b, c, ...` | the zone absorbs `2` and `b`; frozen blocks `c - 1, ...` (if c = 1 the next pair goes too) | `py/frozen.py` (20,000 random zones and frozen tapes) |

So inside a growing phase halting depends only on the parities of the frozen blocks, never on the binary digits of
the zone; those digits matter only through what the crossing phase writes into the frozen tape.

**The invariant that would settle it (observed).** At all 139,833 right turns in E of the first 10^10 steps, the tape
from the head to the last 1 is a word in the 2-cell letters `11` and `01` starting at the head (`c/twoletter.c`).
Then the block under the head has even length and every later block odd length, so the odd case never comes up.
The block under the head had 2 to 4, 6 to 8, 10 to 16 or 18 to 32 cells (dyadic bands, once 62 and once more than 64),
the Sierpinski pattern once more:

| m | 2 | 4 | 6 | 8 | 10 to 16 | 18 to 32 | more |
|---|---:|---:|---:|---:|---:|---:|---:|
| right turns with tape after the block | 36,458 | 46,426 | 19,254 | 20,280 | 14,830 | 2,546 | 2 |

A proof of non-halting would follow from showing that this invariant is preserved. That needs the crossing phase:
there about 60% of right turns happen inside old zone material rather than at the edge of a clean zone, and the frozen tape
is written by the sweeps, so the zone's digits enter. Not proved.

**Even head blocks and walls, in Lean (21 November 2026, `lean/Absorb.lean`).** All for every zone word and prefix:

* `absorb`: frozen tape `1 1 0 1^(4k+1) 0 1 R`: the head block and the next block are absorbed; the next right turn has
  the clean zone `tmap ws`, `v^k`, `u` and E on `R` (the third block, one cell shorter).
* `absorb3`: frozen tape `1 1 0 1^(4k+3) 0 1 R`: the same, but the zone comes out `tmap ws`, `v^(k+1)` and then a *wall*
  `1 0` next to the head, two cells out of step with the letters.
* `wbounce`: a bounce against a walled zone is the running XOR of the word with a `0` appended (`smap`), the wall stays
  and the head block loses two cells. `halts_of_odd_wall`: an odd head block followed by `0 1` still halts.

With `bounce` and `halts_of_odd` from `Pascal.lean` this covers every right turn in a clean or walled zone except two:
a 2-cell head block followed by an even block (which the observed invariant rules out), and an even head block
meeting a walled zone. That case is settled below ("Walls are letters"): with 2-cell letters a wall is an ordinary
letter and the sweep does not turn back early. The crossing phase is what a non-halting proof still needs. The halting shape itself is now known in both zone kinds: an odd head block.

**Walls are letters (21 November 2026, `lean/Wall.lean`).** Cut the tape into 2-cell letters, aligned with the head at
a right turn: `a = 11` and `b = 10` left of the head, `a = 11` and `c = 01` right of it (read from the head outwards,
`b` and `c` are the same two cells `0 1`). A clean zone is a word in `ab` (= `u`) and `aa` (= `v`), and the wall `1 0`
is a single `b`, so a zone with walls anywhere is just a word in `a` and `b`. A frozen tape whose head block is even
and whose later blocks are odd (the observed invariant) is a word in `a` and `c`. All of the following is proved for
every such zone, prefix and frozen word:

| pass | what it does | Lean |
|---|---|---|
| left sweep, C (odd) / D (even) | running XOR of the zone from the right (`b` = 1), writes `a` (even) or `c` (odd); never turns early, always reaches the left end | `sweep2` |
| left end | adds one `a`, toggles the prefix in C | `lend` |
| right sweep, F (even) / E (odd) | running XOR from the left (`c` = 1), writes `b` (odd) or `a` (even); stops at a new right turn at the first place the XOR is odd twice in a row (E reading `a`) | `rsweep2`, `rsw2` |

* `bounce2`: one bounce is the composition, for any zone in `a`, `b` (walls anywhere) and any frozen word in `a`, `c`.
* `wall_even`: the case left open above, an even head block (`1 1 0 ...`) meeting a walled zone, is the instance with
  zone `b` followed by the zone's letters. The sweep does not turn back early; the next turn is given by `rsw2`, and its zone
  is again a word in `a` and `b` (possibly with walls inside, which is harmless now).
* `turn_next`, `not_halts_of_closed`: the next right turn has the same shape, computed on lists by `nxt`, unless the right
  sweep runs past the end of the frozen word into the rest of the tape `R`. So the machine cannot halt before that
  happens, and a set of (zone, prefix, frozen word) closed under `nxt` is a proof of non-halting. Halting needs F on
  `0 0 1`, which this shape never contains.

What this leaves is the right end of the frozen word and the crossing phase. In the first 10^9 steps, 22,747 of the
44,837 right turns have this shape all the way to the left end of the tape; at the others (the crossing phase) the left
side also holds `c` letters left behind by earlier sweeps. There the left sweep stops at the first `c`: C on it turns
right at once, D on it goes on in E, which turns `a` into `b` until it meets a `b` and turns right.

**Every right turn, with the crossing phase (observed, `py/turnshape.py`).** Read the tape at a right turn (E
reading 1 and stepping left) in the 2-cell letters above, plus `o`, a lone 1 that shifts the letter grid by one cell.
Then all 17,758 right turns of the first 2·10^8 steps have one of three shapes:

| left of the head (far to near) | head and right of it | right turns |
|---|---|---:|
| `[o] Z`, `Z` in `a`, `b` (the `o` is the prefix `p = 1`) | `a`, a word in `a`, `c`, then one lone 1 or nothing | 9,005 |
| `[o] Z o Z'`: the same with one more `o` inside the zone | the same | 8,735 |
| as above | E on a lone 1, the last cell of the tape | 18 |

So the rest of the tape `R` in `Turn w p s R` is always blank or a single 1, no part of the zone has two `b` next to each
other, and a crossing is the time between a turn where `nxt` is `none` and the next turn with no `o` inside the zone.
At every turn with no `o` inside the zone the next right turn is the one `nxt` predicts, with the same `R` (8,988
times), or `nxt` is `none` (17 times, and each of those starts a crossing). During a crossing the inner `o` is
the far edge of a short new zone. The old zone beyond it is eaten a few letters per bounce, and the frozen word grows
by as many letters. Most crossings take the zone from hundreds of letters down to about ten.
So halting is possible only inside a crossing (`turn_next` covers every other turn).

What does not close, at this level:

* *Turn-to-turn n-grams.* Use the exact map from one right turn to the next (the machine is run, so nothing is
  approximated between turns). Take as the closed-set candidate every turn whose string of letters (prefix, zone,
  head, frozen word, end) has only length-`k` factors seen at reachable turns. For `k` = 3 to 6, a few hundred short
  members map to turns outside the three shapes (several lone 1s in the frozen tape). Writing the frozen side in
  cells instead of letters and growing the factor set to a fixed point (`k` = 6) reaches an odd head block, which
  halts. The factor sets can't see that a short zone never meets a long frozen word whose blocks have the wrong
  phase.
* *Bounded look at the crossing.* Where a crossing goes is not decided by any bounded number of zone letters next to
  the head (`py/turnshape.py`, part 3). Out of all zones of up to 12 letters, 216 of the 1,024 classes fixed by the 8
  letters nearest the head (plus the state and the end) still contain both outcomes. The crossing reads the whole
  zone, because it sweeps it over and over.

So a proof needs an invariant that ties the zone's digits to the frozen word's, which is the Pascal-triangle structure
again, not a regular language over letters.

**The left sweep of a crossing, in Lean (`lean/Crossing.lean`).** At a crossing turn the zone is `O o N`: a near
part `N`, a lone 1, and a far part `O`. Every letter ends in a 1, so `o` followed by `O` is again `O` in letters,
one cell further out. `Turn2 N O p s R` is this shape. For every `N`, `O`, prefix and frozen word:

* `cross_near`: the left sweep over `N` is `sweep2` (running XOR, no early turn) and reaches `o` in C (odd) or D (even).
* `cross_even`: if the parity is even, D writes 1 over `o` and sweeps `O` in letters to the left end, as in a clean zone.
* `cross_odd`: if the parity is odd, C turns into E on `o`. E turns each `a` of `O` before its first `b` into the
  misaligned pair `1 0` (`erun`), then turns right on that `b`, which becomes `a` (`eturn`).

So one bit, the parity of `N`, decides whether a crossing bounce reaches the left end. Observed at all 2,590
crossing turns of the first 2·10^7 steps: the letter of `O` next to `o` is always `b`, so in the odd case E turns at
once. Neither that fact nor the other observed ones (no `bb` in any part of the zone, `b` next to the head) is kept by
one exact turn-to-turn step on all small shapes. A zone of one or two letters meeting a frozen word of `c`s can put
a lone 1 into the frozen side; the run never builds that combination, but nothing local says why. That is where this
attempt stops.

**Crossing bounces in Lean (`lean/Crossing.lean`).** Write a crossing turn as `Turn2 N O p s R`: near part `N`, the
lone 1, far part `O`. The lone 1 commutes with an `a` (`shift_a`: `1 | 11` and `11 | 1` are the same cells), so `O` can
be taken to start with `b`. All of the following holds for every zone, prefix and frozen word.

* `turn2_odd`: when the parity of `N` is odd, the next turn is `Turn2 W2 (a :: O') p r R`. Here `O = b :: O'`, and
  `W2` and `r` come from the same right sweep `rswL` as in `turn_next`, over `N`'s output, `c` and the frozen word.
* `turn2_even`: when the parity is even, the same holds with the far part replaced by the sweep's output `W1`, provided
  the right sweep crosses the far part's output without turning and arrives in F.
* `far_even`, `clean_even`, `clean_odd`: in the 4-cell letters of `Pascal.lean`, a far part `u ws` always meets that
  proviso. An even bounce turns it into `u (sx true ws)`, the running XOR (Pascal's rule), and an odd bounce removes its
  first `u`. So a clean far part stays clean through every crossing bounce, and nothing in it can stop a bounce.

At all 2,590 crossing turns of the first 2·10^7 steps the far part is clean (`u ws`). A crossing can leave the shapes
only through its near part, by reaching the right end of the tape while the far part is not used up yet. That adds a
second lone 1, or happens right after a turn on the last cell. Small words show both (`py/crossing.py table`). A break
is not a halt: in a search over words with first run 0 to 3, inner runs 1, 3, 5 or 7, last run 1 or 3 and up to four `b`s (not kept), only
1 of the 36 words whose crossing breaks halts within 2·10^5 steps. So what remains is a
race between the odd bounces, which use up the far part, and the near part's growth toward the right end.

**The holdout as a question about lists (`lean/End.lean`, 22 November 2026).** The right end of the tape comes in
four cases. F on blank (`end_F_blank`) gives a crossing turn with an empty near part. E on blank, or F on the last 1
(`end_E_blank`, `end_F_one`), gives an ordinary turn with one more `a`. E on the last 1 is itself a right turn that
bounces like `Turn`. With these, every right turn of the run is one of three list states: `T` (`Turn`), `T2`
(`Turn2`), or `EO` (E on the last 1). `astep` computes the next state on lists alone, by running XORs and the
stopping rule of the right sweep. It returns `none` in only two cases:

1. F reaches the blank end during a crossing, while the far part is not used up;
2. an even crossing bounce is blocked by its far part (impossible when the far part is clean, `far_even`).

Proved in Lean:

* `astep_sim`: each list step is at least one step of the machine.
* `start`: the first right turn, step 12, is `EO [b, a]` with prefix 1.
* `not_halts_of_arun`: if `arun k (EO [b, a] none true)` is defined for every `k`, the machine never halts from blank
  tape.

So the whole holdout is now one question about one list program: does it ever reach case 1 or case 2? The Python
version (`py/listmachine.py`) agrees with the real machine at every one of the 17,758 right turns of the first
2·10^8 steps. Evaluating the Lean `arun` with `#eval` gives the same tapes as the Python version after 300 and 2,000
list steps, and neither case occurs in that run.

**40,000 list steps (`py/listmachine.py run 40000`, about 25 minutes).** Run on its own from `start`, the list machine
takes 40,000 steps without reaching case 1 or case 2: 17,897 `T` turns, 22,084 `T2` turns and 19 `EO` turns. The far
part is clean (`dbl (true :: ws)`) at every one of the `T2` turns, and the zone grows to 21,395 letters.

**Odd runs stop the sweep (`lean/Race.lean`).** A right sweep from F stops at the first 0 it reads in E, so it reads
a whole word without stopping and ends in F only if the word is in `(0 | 11)*`. Call a 0 followed by an odd run of 1s,
followed in turn by a 0 or by the end of the word, a *witness*. Proved in Lean:

* `rswL_witness`: a sweep never gets through a word with a witness and ends in F.
* `astep_T2_witness`: a crossing turn whose far part is clean and whose frozen word `s` has a witness always has a
  next list state. That covers both failure cases at once.

So case 1 needs a crossing turn with blank end whose frozen word has no witness. In the 40,000 list steps
(`py/race.py 40000`) there are 18,062 crossing turns with blank end, and 18,052 of them have a witness. The other 10
come right after the 7 times that E reads the last 1 during a crossing. Six of those times, `s` is `0` (and once then
empty) for one or two bounces. Once, after list step 28,414, it lacks a witness for bounces 1, 3, 4 and 5 (`s` is
`0`, `10`, `0110011110000110`, `110011110000110`). The list machine gets past all of them, but only because of the
near part. What is left for case 1 is to show that those first few bounces after E reads the last 1 are safe, and
that the witnesses never run out after that.

**The ten turns without a witness, as theorems (`lean/Window.lean`, 22 November 2026).** The ten come in six
*windows*: the first bounces after E reads the last 1 during a crossing (an `EO` turn with a far part, which erases the
last 1, so the end is blank from then on). The near part at those six `EO` turns is one of three words:

| near part at the `EO` turn | windows | turns without a witness | Lean |
|---|---:|---:|---|
| `b a b a^6` | 4 | 4 (bounce 1, `s = 0`) | `window_W3`: within 2 list steps |
| `b a b a^12` | 1 | 2 (bounces 1, 2; `s = 0`, empty) | `window_W6`: within 3 list steps |
| 43 letters, list step 28,450 | 1 | 4 (bounces 1, 3, 4, 5) | `window_W43`: within 6 list steps, far part starting `u v v` |

Each theorem is about a family of list states, not just the run's: it holds for every prefix `p` and every clean far
part (`dbl (true :: ws)`, for any `ws`; for the third, any `ws` starting `0 0`). It says that `astep` does not fail
for that many steps and reaches a `Safe` state: the crossing is over (`Plain`, what a bounce with no lone 1 returns),
or the frozen word has a witness and the far part is clean (`Witnessed`; then the next step exists, `witnessed_step`,
which extends `astep_T2_witness` to far parts with leading `a`s). The proofs keep the far part symbolic: the near
side reads only the run of `a`s it absorbs after an odd bounce (`coreO_falses`, `core_odd`), and an even bounce turns
the far part's 4-cell word into its running XOR (`core_even`, from `far_even`). The 43-letter window is written by
`py/window43.py`, one lemma per bounce.

**What this does not do, and why.** It does not close the holdout: it covers the turns where witnesses are missing,
not the claim that witnesses never run out later in a crossing, and it takes the `EO` near parts and far-part prefixes
from the run. Both of those depend on the far part, which is the zone the growing phase built:

* `eo_W1_fails`: `EO (b a b a^2)` fails at once, for every clean far part. The run's `b a b a^6` is `b a b` plus the
  `2 + 2z` letters `a` absorbed from the far part's first run `u v^z`, with `z = 2`; a far part starting `u u` gives
  `b a b a^2`.
* `py/game.py` plays the near side against a free far part (the run lengths `z` it hands over are chosen freely). It
  finds failures from crossing starts `a^m` (m = 1, 2, 3, as in the run) and from real states of the run two bounces
  after an `EO` turn: a long run of `a`s turns the near part into a zone that eats the whole frozen word two letters per
  bounce, like a growing phase.

So the near part cannot be handled on its own; a proof has to say which run lengths the far parts of real crossings
have, which is the Lucas-theorem structure of the zone at the end of a growing phase.

**A faster list machine (`c/listmachine.cpp`).** The same list machine in C++ (it matches `py/listmachine.py` state for
state on the first 3,000 steps; its step count also counts the turns handed back by the right end, so it runs a little
ahead of the Python count). `./listmachine 1000000` (about 25 minutes) runs 10^6 list steps without a failure: 458,336 `T`,
541,637 `T2` and 27 `EO` turns, and the zone grows to 620,913 letters (about 1.2 million cells; with the left end
growing like twice the square root of the step count, that is of the order of 10^11 machine steps, an estimate, not a
count). E reads the last 1 during a crossing 8 times, always with one of the three near parts above (`b a b a^6` six
times, `b a b a^12` and the 43-letter word once each), and the 12 crossing turns with blank end that have no witness
are all in those windows.

**Do witnesses run out? Perturbed orbits (22 November 2026, `c/locality.cpp`, `c/perturb.cpp`).** The Lean windows
cover every crossing the real orbit makes in 10^6 list steps, but they do not show that witnesses never run out later.
Three experiments say why a proof along these lines is hard, and suggest the machine may well halt in the end.

- *Locality (observed).* The next crossing start (its near part `a^m` and the first 30 letters of its far part)
  depends only on the last 200 or so letters of the frozen word. `./locality 12240 200 12 7` keeps the last 200
  letters, randomizes the rest, the length, the zone and the prefix, and all 13 runs print the same next crossing;
  with only the last 30 kept (`./locality 12240 30 20 0`) they differ. So the far parts the growing phase builds are
  a function of a short, deep window of the previous frozen word, with carry-like dependence on its far end, and
  there is no evident finite description of them.
- *A random far part fails.* Run against random clean far parts, the near side (`py/game.py`) fails in about 3% of
  crossings, almost always within about 30 bounces. The real orbit's far parts are not random, but nothing found so
  far separates them from the failing ones.
- *Perturbed orbits halt.* `./perturb 186 10 1000 9 11 1000000000` runs the list machine from blank tape to list
  step 186, keeps the last 10 letters of the frozen word, randomizes the rest and the prefix, and follows 1000 such
  orbits through 9 more crossings. At each `astep` failure it rebuilds the tape (`cfg` of End.lean) and runs the
  real machine for up to 10^9 steps. Per crossing after the cut, the failures (and real halts among them) are
  0, 5 (2), 0, 23 (23), 4 (4), 10 (4), 10 (8), 11 (4), 4 (2), 0: 67 failures, 47 of them real halts, out of 1000
  orbits. That is about 0.5 to 1% of orbits halting per crossing. Later the rate seems lower: from list step 12240
  (K = 10, 120 orbits, 4 crossings) there was 1 failure in 476 crossings (halting not checked), and with K = 200
  none.
- *The real orbit and its siblings.* The unperturbed orbit runs 10^6 list steps without failure, and so do three
  other small starts of the list machine (`EO` with `W = 101000`, `p = 0` and `p = 1`, and `W = 1010`, `p = 1`):
  10^6 list steps each, no failure.

So the machine behaves like a Collatz-like probabilistic halter: each crossing is a fresh, nearly independent trial
with a small (and perhaps falling) chance of halting, and orbits that the machine could have taken do halt. A
non-halting proof would need hidden structure that makes the real far parts special, such as a closed description of
the words the growing phase builds; none has been found. A halting proof would need to follow the real orbit to the
failing crossing, which at the present growth (epoch step counts about 3 times larger each time) may be far beyond
reach. A bit-parallel list machine would push the halt hunt further.

**The halt hunt on the real orbit (23 November 2026, `c/bitlist.cpp`).** A bit-parallel list machine (64 letters per
machine word, one fused pass per bounce, threads for long zones) matches `c/listmachine.cpp` state for state on the
first 150,000 steps and reproduces its 10^6-step counts exactly, about 20 to 50 times faster. From blank tape it ran
10^8 list steps without a failure of `astep` (about 14 hours on 3 cores): 41,941,838 `T`, 58,058,124 `T2` and 38 `EO`
turns, the zone reaching 5.6·10^7 letters (about 1.1·10^8 cells). E reads the last 1 at list steps growing by a factor
of about 1.75 (4,463,710, 7,833,642, 13,742,098, 24,102,211, 42,285,079, 74,185,719), each followed by one long
crossing (the last ran from about 75·10^6 to 99.9·10^6), but the last time E read it during a crossing was at list
step 471,169, and after the first 10^6 steps there was no crossing turn with blank end at all (192,818 in all, 12
without a witness, all early). So the hazard that makes perturbed orbits halt has not come back on the real orbit.
On a failure the program saves the state, and `./bitlist tm H state` rebuilds the tape and runs the machine.

**Safe and dangerous epochs (observed, 25 November 2026, `c/bitlist.cpp`).** Each epoch ends when E reads the last 1
with no far part. The whole zone then becomes the far part of the next crossing. Usually the crossing starts at once,
with a 1 at the right end (`r = 1`), and then no crossing turn has a blank end, so no witness is needed. In the first
3·10^6 list steps, the epochs where this did not happen are exactly those whose zone, read from the head at E's event,
starts `101001` (otherwise `101000` or `101010`). In 6 such epochs E turns back first. Three times a second E event
follows at once and the crossing starts safely; three times (list steps 38, 9,201 and 471,164) the crossing starts with
E reading the last 1 again, `r = 0`, and every turn needs a witness. A crossing that ends with `r = 0` passes the
blank end on to the next epoch, which explains the other early dangerous crossings. Nothing in the frozen word seems to
force the safe prefix. With the real frozen word at the end of the crossing at list step 629,196 replaced by random
letters, 13 of 30 runs started the next crossing without E's event at all, and 2 more reached it with the zone starting
`001000`. The real frozen words have stable statistics (44.6% ones and the same run-length distribution at every epoch
from 1,546 to 1.3·10^6 letters), like a random sequence. On the real orbit the 10 epochs after list step 471,169
(14 E events, up to list step 130,131,762) were all safe.

**Crossings as one map (observed, `py/crossing.py`).** A crossing starts when `nxt` is `none`. By then the right
sweep has used up the whole frozen word. What is left is the swept zone `W`, the prefix `p`, and the end cell `r`
(blank, or a single 1), with the head in F or E according to the first letter of `W`. So the whole crossing, up
to the next turn with no lone 1 inside the zone, is a function of `(W, p, r)`. The function `crossing` runs it, and it
matches the real run at all 13 crossings of the first 2·10^7 steps. The machine is therefore an iterated map on
crossing starts: a crossing writes a short zone and a frozen word, then `nxt` runs until the next crossing starts.
It can halt only if some crossing leaves the three shapes.

Write `W` (nearest letter first) as runs of `a` between its `b`s. The 17 crossing starts of the first 2·10^8 steps
(|W| from 19 to 12,192) have these features:

* The last run (at the prefix) is always odd.
* Every inner run is odd except at most two even runs among the first five (lengths 2, 4 or 8). So past the first few
  letters the zone is a clean 4-cell zone.
* The first run is 0, 1, 2 or 3.

The run never breaks a crossing, but these features do not rule a break out:

* In the small-word table (`crossing.py table`: inner runs 1, 3 or 5, up to 5 `b`s), an even last run breaks about a
  third of the time. Odd last runs are safe when the first run is 2 or 3. With first run 0 or 1, 28 words still
  break, for example `(0, 1, 3, 5, 3)` with `r = 1`.
* Allowing inner runs up to 9, 440 of 18,744 cases with first run 2 or 3 and odd last run break, for example
  `(2, 1, 7, 1, 1)` with `r = 0`.

Which zones are safe therefore depends on run lengths modulo higher and higher powers of 2. That is the dyadic
pattern of Lucas' theorem again. A proof would have to show that the zones built by `nxt` from a crossing's output
avoid these words, and no candidate statement for that is known.

A stronger form holds at every right turn in E, on all nine machines of the two tables, for 10^9 steps each
(`c/evenblocks.c`): every block of 1s between the two ends of the tape has odd length, except the block under the head
and at most one "wall" block to its left, and there is no `00` between the ends of the tape. Sampling every step shows the same picture
between turns: no `00`, and the parity of the offsets of the 0s switches at most once on each side of the head. An
abstract interpretation built on that (`py/absz.py`: K cells each side kept exactly, the rest summarized by its first cell,
the parity of its first 0 and the number of parity switches; K = 2 to 8, up to 3 switches) does not close: it lets the
head reach configurations with a second switch near the right end, or with a `00` that the real run only makes
for a moment in D. Closing it needs the letter structure (block lengths mod 4) in the summary.

**The other machines of R05.**

- Same table, other start (`1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF`, and the mirrored
  `1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB` and `1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---`): every theorem above is
  about the table, for any surrounding tape, so it holds for them after renaming the states. Lean checks it for
  `1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF` (`lean/Pascal.lean`, `lean/Lucas.lean` in its folder, written by
  `py/port_pascal.py`); the mirrored two would need the tape sides exchanged. The 2-cell-letter invariant holds at
  every right turn of all three runs for 10^9 steps.
- The slower twin `1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF` follows this machine step for step up to a break
  (`lean/Twin.lean` there), so the bounce applies to it through that simulation; the four other holdouts on the twin's
  table are that table started in B, C, E and F. The invariant holds at every right turn in E for 10^9 steps of the
  twin table started in A, B, C and E; started in F (`1RB1RA_1RC0RF_1RD0RD_1LE---_0LC1LF_1RA0LE`) it fails at 12 right
  turns near step 2.6·10^7, each within 30 cells of the right end. The twin halts only on `F> 0 0 1 1`, so a failure
  is not a halt there.
- `1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB` runs rule 102, whose `j`-th power is `v[i] = XOR_k C(j, k) w[i + k]`,
  odd exactly when the binary digits of `k` are among those of `j` (the same theorem of Lucas); its danger pattern is
  a gap of words reaching all `y` under that map. Done there (`lean/Xor.lean`, `lean/XorLucas.lean`): the round trip
  is proved to be rule 102 for every length, with the same Lucas lemmas, and a gap can reach all `y` only if it is
  already a row of Pascal's triangle mod 2.

## Notes for later

- The turning places and the left end are now rules on blocks; the missing piece is the format of the tape at the
  start of an epoch (which blocks the crossing phase can leave) and what the right end does with it.
- The three other machines with this table (see Related machines) obey the same block rules after renaming states
  and mirroring; their runs are different.

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 12 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

- Run lengths mod 4 with memory beyond the window (21 November 2026, `py/rlcps.py`): each side is its K nearest runs
  (1-runs exact up to T, longer ones by length mod 4; 0-runs exact) plus an n-gram summary of the runs beyond, grown
  to a fixed point as in n-gram CPS. K = 2..6, T = 4..8, n = 2..4: every closing parameter set reaches a halt in the
  abstraction, the others exceed 2·10^6 configurations. The spurious paths all go the same way: F walks right far past
  the window, and the summary it built on earlier walks offers block sequences that never occur in the frozen tape
  (even blocks, `0 0`). The summary does not know that the tape right of the zone is a word in `11` and `01`.
- A fixed feature automaton read from the far end of each side (`py/dfactl.py`: open run and its length mod 4, the
  number of even blocks and of `0 0` gaps seen, capped): halts in the abstraction after about 2,200 abstract
  configurations, through a `0 0` created at the right end early in the run and carried to the head. Counting
  features cannot tell "a `0 0` at the right end" from "a `0 0` in the bulk".

What a proof needs instead is the phase structure: the growing phase is now in Lean for clean and walled zones
(`lean/Absorb.lean`), and in the crossing phase the run looks like the wall of `absorb3` moving left through the old
zone one block per few bounces (block lists at turns, steps 7,484 to 7,800 above). Writing the wall's step as a block
rule, and the right end's two events per epoch, would give a macro-machine whose states are these phases.

## Pages

- [`pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/explainer.html`](../../pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/explainer.html)
- [`pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/proof-status.html`](../../pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**[`1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF`](../1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/README.md) is a slowed-down copy of this machine (observed, not proved).** Read that machine's states A as A, B as B, D as C, E as E, F as F of this machine. Then 4,995,966 of its first 10^7 configurations (tape, head position and state) are configurations of this machine, in the same order. The last one is step 9,999,982 there and step 6,664,008 here, so it takes about 1.5 times as many steps. The tables are not renamings of each other. Lean proves (`lean/Twin.lean` in the other machine's folder, `sim_or_break`, `not_halts_of_noBreak`) that each step of the faster machine is matched by one or three steps of the slower one up to the first break, a configuration where the paired states act differently, and that neither machine halts if no break ever comes. A halt of either machine is itself a break, and the halting transitions of the two do not correspond, so the two are not known to halt together.

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB`](../1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/README.md): rename A→D, B→E, C→F, D→A, E→B, F→C and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF`](../1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/README.md): rename A→C, B→D, C→E, D→F, E→A, F→B; it is this table started in state E
- [`1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---`](../1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/README.md): rename A→E, B→F, C→A, D→B, E→C, F→D and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
