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
