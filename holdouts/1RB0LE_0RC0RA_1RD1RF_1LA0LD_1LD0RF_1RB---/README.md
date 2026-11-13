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
- `lean/Rebuild.lean` (kernel, written by `py/rebuild.py`): the left-end tick at step 22,986,
  `3|3|12|15|1.48.(2v+4)` → `88|6|2|13|21|(2v+4)`, for every v (8v + 16,500 steps).
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a halt is
  `B> 0 1 1`.
- `c/blocks.c` (trusted computation): the block list at every right-end turn, with the form checked (10¹⁰ steps in a
  minute); `py/blocks.py` is the same in Python.
- `py/ticks.py` (trusted computation: symbolic runs, not Lean): the rule of each tick, grouped by pattern.

## What is open, next steps

1. The other tick patterns: 166 ticks of the first 10¹⁰ steps, besides the 238 rebuilds (blocks of length 1, mixed
   parities). The pieces of `lean/Chain.lean` should cover most of them with new turn pieces.
2. The rebuilds. A rebuild reads the block after its turning point cell by cell, so `rebuild_3_3_12_15_1_48` has a
   variable only for the last block. With more blocks to the right, the head comes back from the left end in a
   state that depends on them (it is not the state the pass pieces expect), so a rebuild does not split like an
   ordinary tick. A general rule has to follow the counter that the rebuild runs on that block.
3. An invariant of the block lists, kept by all rules, that keeps B off `0 1 1`.

Why the method that proves 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB (a finite table of forms, then linear
inequalities on their counts) does not apply as it is: the forms here are block lists of unbounded length (3 to 15
blocks in the first 10¹⁰ steps, the 30,932 lists by length: 15, 23, 75, 125, 360, 594, 2893, 3611, 5943, 6559, 6726,
3762, 243 for 3..15 blocks), and the tick rules depend on where the turning separator is. The 229 left-end visits
(the first block changes) happen when the separators read `|.......`, `........`, `|.........`, ... (64 different
separator patterns), so a rebuild rule must take a whole list. Their outcomes contain blocks that drift slowly over
many ticks (10799 → 10946 and 43792 → 41212 between 10⁹ and 10¹⁰ steps), so any invariant has to be stated on lists.
A finite table cannot close here; what is needed is a general tick rule and a general rebuild rule on lists.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/lean/check.sh
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/route.py     # rewrites lean/Route.lean
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/chain.py     # rewrites lean/Chain.lean
python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/rebuild.py   # rewrites lean/Rebuild.lean
gcc -O2 -o blocks holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/c/blocks.c
./blocks 1e8 | python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/ticks.py
```
