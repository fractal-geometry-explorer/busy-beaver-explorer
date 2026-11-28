# 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---

bbchallenge id 103746, group G08 (two-sided square-root growth). Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 0RC | 0RA |
| C | 1RD | 1RF |
| D | 1LA | 0LD |
| E | 1LD | 0RF |
| F | 1RB | --- |

## What it does

The tape is an alternating pattern `1010…` cut into blocks `(10)^n` by single extra cells, the *separators*. At
every turn of the head at the right end it reads

    (10)^n0 s1 (10)^n1 s2 … sk (10)^nk A> 1 1          separators s_i ∈ {0, 1}

written below as `n0 s1 n1 … nk` with `|` for a separator 1 (it makes a pair `11`) and `.` for a 0 (a pair `00`).
`c/blocks.c` prints this list at every right-end turn and checks the form; it holds at all 30,932 right-end turns of
the first 10¹⁰ steps.

Every sweep complements what it crosses (on an alternating stretch that is a shift by one cell): moving left A, E, D
take four cells at a time (`sweep_left`), moving right B and A two (`sweep_right`). One round trip from the right end
back to it is a *tick*. The sweep passes some separators and turns at one; which one depends on the separators and
on the parities of the blocks. `py/ticks.py` finds the rule of every tick by a symbolic run with the last few block
lengths as variables. The common ones (`e` an even block, `o` an odd one, x the block before):

    x | e                 ->  x . e+2                          (tick_last, Lean)
    x | o | o             ->  x . o+1 | o+1                    (tick_oo, Lean)
    x | e . e . e         ->  x . e | e+1 | e+1                (tick_chain, Lean)
    x | o | o . e . e     ->  x . o+1 | o-1 | e+1 | e+1        (tick_chain_oo, Lean)
    x | e . e . e . e . e ->  x . e | e+1 | e-1 | e+1 | e+1   (and so on: the 0s after the turning point become 1s,
                                                               the blocks after it change by +1, -1, …, +1, +1;
                                                               tick_chain and tick_chain_oo for any length)

So the separators count like an odometer whose digits are read with the parities of the blocks, and the last block
grows by one or two on every tick. Of the 30,932 ticks in the first 10¹⁰ steps, 30,528 are in
the two families `x | e (. e . e)^k` and `x | o | o (. e . e)^k`, 30,674 follow one of 61 patterns, 20 have a block
of length 1 where the templates are too coarse, and 238 reach the left end.

When a tick needs the left end, the head works there for a long time and rebuilds the front of the list. The same
sequence of lists recurs on larger scales, with extra blocks on the right:

       22,986  3|3|12|15|1.48.94                   ->   39,846  88|6|2|13|21|94
      778,692  3|3|12|15|1.48.212.258.468          ->  799,968  88|6|2|13|21|210|259|469
       81,286  2|97|3|11|1.58.168                  ->  122,674  108|4|100|1|17|168
    1,452,208  2|97|3|11|1.58.174.370.692          -> 1,499,356  108|4|100|1|17|172|371|693

and the list grows slowly (8 blocks at 10⁶ steps, 12 at 10⁹, 14 at 10¹⁰), with new large blocks appearing at the
left after the biggest rebuilds (10766 at step 631,723,450; 43798 at 3,994,138,280).

The only halt is F reading a 1. `halt_route` (Lean) shows that two steps before any halt the machine is at
`B> 0 1 1`: E is entered only from A reading a 1, which leaves a 0 to E's right, so `E> 1 1` (`halt_E`) never
happens, and `C> 1 1` (`halt_C`) only comes from `B> 0 1 1`. In block terms B would have to stand on the last 0 of a
block followed by a separator 1; in the run F always reads a 0.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the two sweeps for any length; two whole ticks for any
  lengths (`tick_last`, `tick_oo`); `halt_C`, `halt_E`.
- `lean/Chain.lean` (kernel, written by `py/chain.py`): the two tick families for chains of any length and blocks of
  any size, `tick_chain` (`x | a . b1 . c1 . … . bk . ck . d . e`, all even) and `tick_chain_oo`
  (`x | p | a . b1 . c1 . … . d . e`, p and a odd, the rest even), from one right-end turn to the next, for every
  list of pairs and every tape x. A tick is split into five symbolic pieces with unknown tape around them (`enter`,
  `lu` one pair on the way left, `turn`/`turn_oo`, `ru` one pair on the way right, `leave`); `left_pass` and
  `right_pass` are inductions on the list of pairs. With `tick_last` and `tick_oo` this covers the families
  `x | e (. e . e)^k` and `x | o | o (. e . e)^k` for every k (30,528 of the 30,932 ticks of the first 10¹⁰ steps
  are in them, by `py/ticks.py`).
- `lean/Chain2.lean` (kernel, written by `py/chain2.py`): seven more turn shapes over the same chains.
  `x | p | a . a2 . b1 . c1 . … . d . e` with a odd and an odd number of even blocks after it turns at the separator
  before p (`tick_chain_pe`, `tick_chain_po`, `tick_chain_p1` for p even, odd ≥ 3, 1); `x | 1 | a . b1 . … . d . e`
  is `tick_chain_oo` with a first block of length 1 (`tick_chain_1o`); `x | p | a . c` are whole ticks
  (`tick_pe_last`, `tick_po_last`, `tick_p1_last`). `py/chain2.py check` reads every tick of the first 10¹⁰ steps
  as an instance of a theorem of `Rules`, `Chain` or `Chain2` (blocks of length 2 or 3 are the smallest values of
  the families) and compares the end tape with the run: 30,673 instances, 0 mismatches, and the other 258 ticks
  are the left-end ticks.
- `lean/Rebuild.lean` (kernel, written by `py/rebuild.py`): the left-end tick at step 22,986,
  `3|3|12|15|1.48.(2v+4)` → `88|6|2|13|21|(2v+4)`, for every v (8v + 16,500 steps).
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a halt is
  `B> 0 1 1`.
- `c/blocks.c` (trusted computation): the block list at every right-end turn, with the form checked (10¹⁰ steps in a
  minute; a third column gives how far left of the first 1 the head went in the tick); `py/blocks.py` is the same in
  Python, without the third column.
- `py/ticks.py` (trusted computation: symbolic runs, not Lean): the rule of each tick, grouped by pattern.
- `lean/Front.lean` (kernel, written by `py/front.py`): the left-end ticks of 13 front shapes, for every chain
  length and all block sizes (next section).

## The left-end ticks decoded (22 November 2026)

A *left-end tick* is one whose rule needs the left end of the list: `py/ticks.py` finds no rule for it, or the head
reaches the first 1 of the tape (`c/blocks.c` now prints, as a third column, how far left of the first 1 the head
went during the tick). There are **258** of them in the first 10¹⁰ steps: the 238 of `py/ticks.py` and 20 copy ticks
that `py/ticks.py` had put among the ticks needing a finer split. Each one splits into a *front* and a *chain*:

    F . C          C = m1 . m2 . … . mk, all even, all separators 0, as long as possible

**The chain law.** In every left-end tick, as in the ordinary ticks, the chain C becomes `C'`: every separator turns
into `|` and the blocks change by, counted from the right, +1, +1, −1, +1, −1, … So `6.10.24.46` becomes
`7|9|25|47`. The left pass over C and the right pass back are the ordinary ones (`left_pass`, `right_pass` of
`lean/Chain.lean`), so a left-end tick is one new piece at the left end, between the two passes.

**The front rules (proved).** 198 of the 258 left-end ticks have one of 13 front shapes, and for each the front
piece is a symbolic run that closes for every value of the block lengths (`py/front.py`). `lean/Front.lean` proves,
for each shape, the front piece and the whole tick, from one right-end turn to the next, for every number of blocks
in C and all lengths (`tick_<shape>`, kernel only). `py/front.py classify` checks the rule against the run at each
of the 198 ticks, all agree. In block notation (e even, o odd; n0, n1, … the front's blocks; C odd or even means
the number of its blocks):

| front | ticks | rule |
|---|---|---|
| `n0 . C`, n0 even, C even | 48 | `3 \| n0−1 \| C'` |
| `n0 . C`, n0 even, C odd | 16 | `n0+3 \| C'` |
| `n0 \| n1 . C`, both odd, C even | 37 | `3 \| n0 \| n1−1 \| C'` |
| `n0 \| n1 . C`, both odd, C odd | 47 | `n0−1 \| n1+2 \| C'` (this one only reads into n0) |
| `n0 \| n1 . C`, n0 even, n1 odd, C even | 3 | `n0+2 \| n1−1 \| C'` |
| `n0 . n1 \| n2 . C`, n0 even, n1 and n2 odd, C even | 2 | `n0+3 \| n1 \| n2−1 \| C'` |
| `n0 \| g1 \| … \| gj \| x . C`, all even, C odd, j = 0 to 7 | 45 | `n0+4 \| g1 \| … \| gj \| x−1 \| C'` |

(The last row is 7 shapes in `lean/Front.lean`, one per j that occurs, j = 0, 1, 2, 3, 4, 5, 7.) For example
`2.6.10.24.46` → `3|1|7|9|25|47` (first row), `92.6.4.8.38.128` → `95|5|5|7|39|129` (second),
`10774|20|8|10|28.234.190.1378.544.1248.1642.13314` → `10778|20|8|10|27|233|191|1377|545|1247|1643|13315` (last).
So the left end of the list is a small counter of its own: the first block grows by 3 or 4, or splits off a new
block 3 at the left, and which one depends on the parities and on whether C has an even or odd number of blocks.

**The copy ticks.** 54 left-end ticks have a front ending `| 1`:

    P | 1 . X . C          (C odd)  →   N | P' | C''          N = 2X − c(P)

The head goes back and forth between the left end and X, and each round moves one pair of X into a new first block
(`py/front.py` finds the piece does not close: it reads X cell by cell). After a few rounds that rework P, every round
is the same, so the outcome depends on X only through N. `py/copy.py` checks this on the real machine
(`c/tick.c`, one tick from a given list) for each of the 52 ordinary copy ticks: the tick run again with X + 2,
X + 10 and X + 100, and with C replaced by `100.200.300` and by `4.6.8.10.12`, changes nothing but N, by exactly twice
the change of X; and C'' is C' with its first block one less. So **each copy tick is a function of P alone**, `c(P)`
and `P'(P)`, with 33 different P in the run:

| P | ticks | c | N \| P' |
|---|---|---|---|
| `3` | 14 | 1 | `N\|9` |
| `113`, `151`, `8375`, `9355` | 6 | 1 | `N\|p+6` |
| `110\|3855` | 1 | 4 | `N\|111\|3861` |
| `111\|1765\|97` | 1 | 4 | `N\|114\|1763\|103` |
| `3\|3\|12\|15` | 5 | 8 | `N\|6\|2\|13\|21` |
| `2\|97\|3\|11` | 3 | 8 | `N\|4\|100\|1\|17` |
| `1780\|6\|10761` | 1 | 8 | `N\|1782\|7\|10767` |
| `2.6.1784\|15` | 1 | 8 | `N\|4\|6\|1785\|21` |
| `3\|3\|18876\|11\|17\|8417` | 1 | 12 | `N\|6\|2\|18878\|14\|15\|8423` |
| `92\|6\|1\|11.28.204\|279` | 1 | 16 | `N\|94\|8\|4\|10\|28\|205\|285` |

(all 33: `python3 py/copy.py ./tick < classify.txt`). Read from the right, P' is P with the last block + 6 and the
others changed by a small transducer that reads the block's parity and the separator after it: after the +6, an even
block gets +1 and an odd one −2; after a −1 or −2 the next block gets +3, and after a +3 or a 0 the next gets +2;
after a +1 or +2 an even block gets +2 (0 if the separator after it is a 0) and an odd one −1. Every
separator becomes `|`. When the first block of P is followed by a 0, or is a lone 2, it is absorbed into N
(`112.4|7|1781|33|1.328` → `760|6|10|1779|39`, 760 = 2·328 + 112 − 8). This transducer is read off the 52 ticks; it is
not derived. Two copy ticks are different: `3|1|771|1.26…` → `1546.33|…` and `3|1|47|1.18…` → `98.25|…` copy the block
between the two 1s (N = 2Y + 4) and add 7 to X.

**The recursion (observed).** After a copy tick the new block N stands at the left of the list, and the blocks that
then grow in front of it replay the run from blank tape: after `9340|2|10|106|…` (step 5,660,813,996) the part left of
the big block reads `27`, `26`, `3|25`, `3|3|24`, `3|3.24`, `2|5|23`, `2.6|22`, …, the lists of the blank run
(`4`, `3|5`, `3|3|6`, `3|3.8`, `2|5|9`, `2.6|10`, …) with the blank run's growing last block replaced by a shrinking
one next to N. Copies from further right interrupt the replay (the big block of 18874 at step 6,921,870,502 comes
from the block 9440 behind it), so the list is a counter whose top digit restarts the whole run in front of every new
big block, at every scale. This is the "same sequence of lists on larger scales" of the first section.

The other 6 left-end ticks (steps 4 to 274,716) have at most one block after the front, too few for the passes.
Each is proved as a concrete run, from its right-end turn to the next, by the kernel (`lean/Early.lean`,
`early_0` … `early_5`, written by `py/early.py`), so all 258 left-end ticks of the first 10¹⁰ steps have a Lean proof.

**The copy ticks in Lean (22 November 2026).** After its first rounds (the *entry*) a copy tick settles into a
loop whose state, at the left end of the tape in state D, is

    1 (10)^(2j+2)  0 (10)^(2b1+2)  0 (10)^(2b2+2)  …  0 (10)^(2bm+2)  0 0 (10)^(2r)  Z

j the pairs already copied into the new first block, b1 … bm the reworked P (all even blocks, separators 0), r the
pairs of X still to copy, Z the chain, never touched. Each half round moves one pair of X: the head crosses every
block to the right in state B (`crossB`), takes a pair at X (`xa`, `xb`), crosses back in state D, restoring each
block (`crossD`), and adds a pair at the left end (`el1`, `el2`, `el3`). These seven pieces are local, so `round`
holds for every list of blocks (two inductions on the list), and `loop` (induction on r) runs the copy to r = 0
(`lean/Copy.lean`). For each front shape of the run (each block of P a variable of fixed parity, as in `lean/Front.lean`) the entry and
the two exits (`exit3` when the chain goes on, `exit1` when it has one block) are symbolic runs, and
`copy_<shape>_long` / `copy_<shape>_one` are the whole tick from one right-end turn to the next, for every X, every
value of the blocks of P, every chain and every number of pairs (`lean/CopyS1.lean` … `CopyS9.lean`). The two
ticks with front `3|1|Y` copy Y instead of X: two rounds make the front a single block, and the same loop then
copies Y's pairs, with X (moved, 7 pairs longer) and the chain after them (`lean/CopyY.lean`, `copy_oI1Io_long`, for
every Y, X and chain). In `3|1|7|9.26|…|1583` (front shape `o|1|o|o.e|e|o|o.e|e|o`) the front `3|1|7` comes up
during the entry and copies its 7, a loop inside the entry, so that entry is one symbolic run only with that block
fixed at 7 (every other block, X and the chain stay variables); that run is long, so it is proved in 18
segments, three to a file (`lean/CopyS3_p1.lean` … `CopyS3_p6.lean`, `py/splitraw.py`). The loop then copies blocks of one fixed length; the exits are proved with a variable for that block and used at its value, since a run with a literal block length made Lean unfold the steps (over 13 GB; with the variable, under 1 GB). 23 front shapes are proved; **all 54 copy ticks** of
the first 10¹⁰ steps are instances, and the end of each theorem, read as a block list, is the list the run reaches
(`py/copyloop.py check`).

**Copy rounds are left-end ticks (Lean, 22 November 2026).** Cut a copy tick at the turns at the edge of X: each
round from one turn to the next runs the same *middle* as the left-end tick of the list `F | 3`, F the front at that
round. In both runs the head comes to the last separator of F in state D, works inside F without reading anything
right of that separator, and comes back to it in state A; the pieces before and after the middle never read F. So
`lean/Transfer.lean` (written by `py/transfer.py`) proves, for any tape F with a middle `Mid F F'`, both the tick
`F | 3 -> F' 1 0 | 4` (`main_of_mid`) and the copy round from the turn at `F | (10)^(2c+2)` to the next turn at
`F' 1 0 | (10)^(2c+2)`, one pair of X further (`round_of_mid`; `rounds_of_mids` for any number of rounds): the
rework of P is the left-end tick law applied to the front once per pair of X.

The middle is then proved block by block. An even block after a separator 1 is *passive*: the middle crosses it
leftwards (`le`), runs on what is in front of it, and comes back (`re`), and after the round the block is what it
was; so any number of even blocks after separators 1 at the end of the front pass through unchanged (`mid_evens`, an
induction on the list). In front of them the middle turns, and that turn is a symbolic run for every value of its
blocks: `L | o -> L . o+1` for an odd block after a 1, whatever L is (`round_od`); `e -> e+2` for an even first
block (`round_e0`, the copy loop); `o -> 3 | o` for an odd first block (`round_o0`); and 19 more turn shapes with
a separator 0 or a block 1 near the turn (`round_b_<shape>`, each block a variable, split at 0 where the run needs
it), e.g. `L | o . e -> L | o-1 | e+2`. The 54 copy ticks of the first 10^10 steps have 2,094 turns at X before the
last (and 56 last turns at X, where no pair is left and the exit starts); `py/transfer.py check classify.txt` finds 2,013 of them to be
rounds of these theorems, for every value of the blocks and every number of passive blocks.

The first rounds are rules too. When the front ends in a separator 0 (the first round of 34 ticks, the second of
20), the round runs the middle of the tick of `F . 3`: the head comes to that 0 in state D and back to it in state B
(`DMid`, `main_of_dmid`, `round_of_dmid`), and the middle is a symbolic run for 6 turn shapes (`round_d_<shape>`:
`L | e .`, `L | o .`, `L . e .`, `L | 1 .`, `e .` and `o .` at the left end). When an odd number of pairs stands
after the front's last separator 1 (the first round of 20 ticks), the round never reads the front: it turns that
separator into a 0 and moves one pair (`round_odd`, for every front). Over the front `1 | e | …` the middle reads
the next block too, so that block goes into the base (`^1|e`). With these, all 2,091 rounds are rounds of a theorem
for every front of their shape. The other 3 of the 2,094 turns at X before the last are no rounds: over the
front `3 | 0 | …` inside a copy of Y the head takes the pairs of X one by one (a loop, not a single pair moved), and
those ticks are proved whole above.

What is still open here: the turn shapes as one rule (a finite list of turn shapes is proved, each for every value of
its blocks, not a rule for every shape), and the replay as a statement on lists.

## What is open, next steps

1. The other tick patterns (done, 23 November 2026): with seven more turn shapes (`lean/Chain2.lean`) every one of the
   30,931 ticks of the first 10¹⁰ steps is an instance of a Lean theorem: 30,673 of the chain theorems (`py/chain2.py
   check`, which compares each theorem's end tape with the run), the other 258 of the left-end theorems below.
2. The rebuilds: decoded in the previous section. 198 of the 258 left-end ticks of the first 10¹⁰ steps are proved
   for every chain length (`lean/Front.lean`), the 6 early ones as concrete runs (`lean/Early.lean`); the 54 copy ticks are checked to depend on the block X only through
   the new block 2X − c(P), and all 54 are proved in Lean for every X and chain (`lean/Copy.lean`, one theorem
   per front shape). Every round of a copy tick is the left-end tick of `F | 3` or `F . 3` on its front, and all 2,091
   rounds of the run are rounds of rules proved for every front of their shape (`lean/Transfer.lean`).
   Open: one rule for every turn shape.
3. An invariant of the block lists, kept by all rules, that keeps B off `0 1 1`.
   First steps (`py/invariant.py`, a computation): of all 113,105 lists of at most 5 blocks of length 0 to 5,
   4,635 halt within one tick (`1.0`, `1.2`, `1.1|1`, …). Every one of them breaks the local condition C: every
   block 1 has a separator 1 before it, and every block 0 stands between two separators 1 and before an odd block
   of length at least 3. The run keeps C at all 30,931 right-end turns of the first 10¹⁰ steps after the first
   (block 1 comes only as `|1|` and `|1.`, block 0 only as `100|0|19`), and none of the 31,636 small lists with C
   halts. C alone is not kept by a tick, though: 3,268 of those lists give a next list without it (`2.3 -> 1|6`,
   `2|1.3 -> 2|0|6`, …), lists that the run never shows. So the invariant needs C together with the parity
   structure that the tick families keep, and for the left-end ticks, the shape of the front.

Why the method that proves 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB (a finite table of forms, then linear
inequalities on their counts) does not apply as it is: the forms here are block lists of unbounded length (3 to 15
blocks in the first 10¹⁰ steps, the 30,932 lists by length: 15, 23, 75, 125, 360, 594, 2893, 3611, 5943, 6559, 6726,
3762, 243 for 3..15 blocks), and the tick rules depend on where the turning separator is. The 229 left-end visits
(the first block changes) happen when the separators read `|.......`, `........`, `|.........`, ... (64 different
separator patterns), so a rebuild rule must take a whole list. Their outcomes contain blocks that drift slowly over
many ticks (10799 → 10946 and 43792 → 41212 between 10⁹ and 10¹⁰ steps), so any invariant has to be stated on lists.
A finite table cannot close here; what is needed is a general tick rule and a general rebuild rule on lists.

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| right | 256,027,010 | 39,174 | 10 | 11 | 21 | 0.53 |
| left | 265,858,840 | 39,818 | 9 | 12 | 21 | 0.53 |
| right | 1,024,010,442 | 77,665 | 9 | 11 | 20 | 0.50 |
| left | 1,041,330,765 | 78,341 | 11 | 11 | 22 | 0.50 |
| left | 4,096,125,978 | 149,240 | 13 | 11 | 21 | 0.59 |
| right | 4,418,673,606 | 152,712 | 14 | 9 | 20 | 0.57 |
| right | 16,384,323,864 | 335,797 | 11 | 15 | 26 | 0.39 |
| left | 16,609,920,373 | 337,957 | 15 | 15 | 27 | 0.40 |

**Proposed family: F06, block-list counters** (blocks of pairs with a base-3 counter, as in 1RB1RF_1LC0LB… (same table)).

The description grows slowly: 20 to 27 level-2 tokens at every record from 2.6·10^8 to 1.7·10^10 steps, and 11 to 45 runs in the macro simulator (blocks of 4 cells) at the sampled records up to 10^17 steps.

The machine shares its table with 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- (states renamed, some of the four mirrored; `related.json`), started in another state. On the screen the four runs show the same list of blocks at the same moments. For example near step 6.4·10^7 all four tapes read blocks of 3, 1,546, 39, 1,753, 117, 1,467 and 997 pairs `01` and then a last block, of 4,405 pairs in 1RB1RF_1LC0LB… and of 4,409 pairs here. The four last blocks differ by 2, 4 and 6 pairs and the records come at slightly different steps. This is an observation at the sampled records: it is not a proof that the runs correspond, and nothing about halting is carried over.

For 1RB1RF_1LC0LB… the right end is proved in Lean to be a base-3 counter on the separators of such a list (`bb6-1RB1RF_1LC0LB/lean/Counter.lean`). Those theorems are about that machine's table with its own state names; they apply here only after the renaming is carried through, which has not been done. A list of blocks with a base-3 counter is F06.

Next step: Carry the renaming through, so that the counter theorems of 1RB1RF_1LC0LB… become theorems about this machine, and state exactly how the two tapes differ (the last block and the left end).

## One run for four machines (F09, 13 November 2026)

Four holdouts have the same table up to renaming the states and mirroring the tape (`holdouts/related.json`), started in
four different states. Written in the states of 32883 (`1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---`):

| machine | id | start state in the table of 32883 | mirrored | first aligned trip: step, runs | first run |
|---|---|---|---|---|---|
| `1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---` | 32883 | A | no | 6, `[6]` | r + 4 |
| `1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---` | 40600 | D | yes | 1, `[2]` | r |
| `1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---` | 103746 | B | yes | 17, `[10]` | r + 8 |
| `1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---` | 131976 | E | no | 37, `[14]` | r + 12 |

A trip starts when the head, in state A of that table, steps onto a new leftmost cell; the tape is then a list of runs of
alternating cells, written as their lengths. `py/lockstep.py` of 32883 simulates two of the four runs and compares the
run lists trip by trip.

**Observed: the four runs are one run, shifted.** At every one of the first 527,004 trips, up to 2·10^12 steps, the four
tapes have the same run lengths except for the first run, and the first runs differ by constants: r for 40600, r + 4 for
32883, r + 8 for 103746 and r + 12 for 131976 (the last two need one trip more to get going, so their trip k + 1 is
compared with trip k of the others). No mismatch occurred. Output: `py/lockstep_2e12.txt` in the folder of 32883.

### What is proved, and what is missing

The four tapes differ only in the length of the first run, so the question is whether the machine can ever see that
length other than mod 4. The head touches the first run only by entering it from the right: it steps onto the last
cell of the run in one of the five states a left move leads to (A, B, C, D, F), and that cell is 0 or 1. That makes
ten entries. Each either bounces (the head looks at no more than the last 2 cells of the run and comes back out),
sweeps (the head goes to the left end, turns and comes back, and the outcome depends on the length mod 4), or halts
at once (F on a 1).

**Proved in Lean (kernel), `lean/Shift4.lean` in the folder of 32883, 24 theorems generated by `py/shift4.py`:** for every entry, the
outcome for a first run of n + 4 cells is the outcome for n cells with one more copy of a 4-cell word in the run:
same exit state, same cells left between the run and the head, same change of the run length. The bounces are
proved for any tape to the left of the cells they touch, the sweeps for every n of the form 4a + 5, 4a + 6, 4a + 7,
4a + 8. `py/shift4.py check` compares n with n + 4 by simulation for every n from 1 to 300: the outcomes agree for
every entry and every n of at least 3, and differ only for n = 1 and n = 2.

**What follows.** While the head is outside the first run, two tapes that differ only in that run make the same steps.
So the four runs stay shifted copies of each other, and the four machines halt together or not at all, **provided**
the first run of the shortest tape (the run of 40600) has at least 3 cells every time the head enters it (with at
least 5 cells every step of the argument is a Lean theorem; for 3 and 4 cells the sweeps rest on the script). That
proviso is the only thing missing. It is observed, not proved: `py/entries.py` finds that in the first 2·10^10 steps
the head enters the first run 57,701 times in the run of 40600, with at least 5 cells each time (5 at step 7, 7 at
step 16, 8 or more afterwards; `py/entries_2e10.txt`), and the first run gains 8 cells every three ordinary trips.

Why the proviso is not a local fact: a bounce takes 1 or 2 cells off the right end of the first run, and nothing in
the ten entries limits how many bounces can happen between two sweeps. In the real run there is at most one bounce per
ordinary trip (the carry at digit 1), so the run grows, but showing that for every trip needs the theory of the
transfers, which is not complete (section "Why the gap does not close yet" of the README of 32883). So the statement
"the four machines halt together" is not proved, and no page claims it.

The rules proved for one of the four tables hold for the other three after renaming, because rules do not depend on
the start.

Reproduce (from the folder of 32883, about 12 minutes each):

    python3 py/lockstep.py 0 3 2e12    # start A against start D
    python3 py/lockstep.py 4 1 2e12    # start E against start B
    python3 py/lockstep.py 0 4 2e12    # start A against start E
    python3 py/shift4.py check 300     # every entry, n against n + 4
    python3 py/entries.py 3 2e10       # first-run length at every entry, run of 40600 (5 minutes)

### In Lean: one halting question, given one condition (16 November 2026)

`holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/lean/Lockstep.lean` (kernel only: `propext` and `Quot.sound`; its generated part is
`holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/lean/FarEnd.lean`, written by `holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/farend.py`) proves the shared run as one theorem about the four machines from blank
tape. It does not need the ten entries above. It compares two tapes that differ only by k periods `1010` inserted at
the left end, just left of the leftmost 1 (`Rel k`). Every step keeps that relation except a step onto the leftmost
1, and there the head is in one of the five states a left move leads to:

| state on the leftmost 1 | both tapes |
|---|---|
| C | the head crosses the k extra periods and comes back out in B with the same cells as without them (`far_C`, every k) |
| D | the same, out in A (`far_D`) |
| F | both halt at once |
| A or B | the tapes are told apart: **the excluded case** (`Bad`) |

After 2, 11, 26 and 50 steps the table started in D, A, B and E is at `0^inf 1 B>1`, with 0, 1, 2 and 3 periods
`1010` more on the left (`at_D`, `at_A`, `at_B`, `at_E`, by evaluation). The renamings and the mirror are proved too
(`halts_40600`, `halts_103746`, `halts_131976`). So:

* **`one_question`**: if in the run of 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- from blank tape the head never reads
  a 1 in state B or C with only 0s to its right (`Good40600`), then 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---,
  1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- and 1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD--- each halt from blank tape
  if and only if 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- does.
* **`three_questions`**: if in the run of 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- the head never reads a 1 in state
  A or B with only 0s to its left, then 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- and
  1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD--- each halt if and only if it does.

**What the condition says.** The only moves to the right from a 0 are A0 and E0, and both write a 1, so an excluded
configuration can only be reached by a move to the left: D on a 0, or C on a 1, just right of the leftmost 1. In the
table of 32883 that is a doubled cell `00` or `11` within three cells of the left end, a first run of at most 3 cells.
A sweep reaches the leftmost 1 in C, which is harmless. So the condition is the old proviso in an exact form: the
first run of 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- (of 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- for the second
theorem) never gets shorter than 4 cells.

**Checked, not proved.** The condition holds in the first 10^11 steps on a plain cell simulator (`holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/c/good.c`) and in
the first 10^14 steps on the run-length simulator (`holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/goodrun.py`), for both runs. Both runs are 23,850,930 and 23,850,932 cells wide after 10^14 steps (start D, start A). Proving it needs the
same theory of the transfers as the halting question itself: in the run, the first run loses a cell at a bounce and is
always swept (and lengthened) before the next one, except at the end of a transfer that moves the second run, and
nothing local rules out a tail that sends the head back sooner (a game against an arbitrary tail drains it).

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/lean/check.sh
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/route.py     # rewrites lean/Route.lean
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/chain.py     # rewrites lean/Chain.lean
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/rebuild.py   # rewrites lean/Rebuild.lean
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/front.py lean # rewrites lean/Front.lean
gcc -O2 -o blocks holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/c/blocks.c
gcc -O2 -o tick holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/c/tick.c
./blocks 1e8 | python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/ticks.py
./blocks 1e10 > blocks.txt                                                       # 1 minute
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/front.py classify < blocks.txt > classify.txt   # 30 s
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/copy.py ./tick < classify.txt                  # 3 minutes
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/copyloop.py classify.txt      # rewrites lean/Copy*.lean
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/copyloop.py check classify.txt  # all 54 copy ticks
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/transfer.py                    # rewrites lean/Transfer.lean
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/transfer.py check classify.txt  # 2,091 rounds, 3 loop starts, 56 exits
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/chain2.py check blocks.txt   # every tick: 30,673 chain instances, 258 left end
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/invariant.py blocks.txt   # small lists that halt; the local condition C
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/early.py   # writes lean/Early.lean (the 6 early left-end ticks)
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---`](../1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/README.md): rename A→B, B→C, C→D, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---`](../../bb6-1RB1RF_1LC0LB/README.md): rename A→C, B→E, C→A, D→B, E→D, F→F; it is this table started in state C
- [`1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---`](../1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---/README.md): rename A→C, B→D, C→E, D→B, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror

<!-- end of related machines -->
