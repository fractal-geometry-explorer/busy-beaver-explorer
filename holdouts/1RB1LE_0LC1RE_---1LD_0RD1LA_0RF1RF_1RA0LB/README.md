# 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB

bbchallenge id 23376, one of the BB(6) holdouts (group G07).
Family: **ladder of self-similar levels (an odometer of 16-state digits) eating a fuel of old blocks**.
Decision: **halts**, after about 1.27·10^758 steps (trust level: *trusted*, an exact accelerated simulation; the
rules it uses are checked against the machine, and the rule for a level is proved in Lean for every block count).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 0LC | 1RE |
| C | --- | 1LD |
| D | 0RD | 1LA |
| E | 0RF | 1RF |
| F | 1RA | 0LB |

## The result

The machine halts at step (bbchallenge count, the halting transition included; 759 digits)

    1273570026215650652576204366833869367875394700670518866132181185110806733669410724190300031696550658
    6744907656942464101157448948237346588336567552669889198473153389753320096745827167245739364964711459
    6314125471135660566111943361843730621394792642277333936847623104308961000089724168905591219305595735
    9317138647525895179113344101002335816717542370035178609912789212172268904407962275829506165146393369
    3081929606642951186489924869694615857619482583640286894060501463961772478955000926577703315252560603
    3456073540691727721901256364141236872161550422869463852043401520343212555953181130714885650835768030
    3182778375315650198749003644673867462140091885037188742822727259261875902846979470017263432385223239
    81475257408390954658553165337971013334254732281910474403686

in state C on a 0, two cells left of the leftmost 1 of the tape. The head starts its last trip to the left at
right-end visit number (379 digits)

    6457109013376761952964397678097307615669340968993585759245814706743742046125940261247241066403890938
    4921701383450217754147886572468554736197625553999240068081856681779372618228883033212414243885068152
    1283069351513437601549190087049853084328964379790397466399345248004876904194995716198540946835334119
    9468784692405027220745645833011312600661412072060494393516371733163287212276888

At that moment the tape is about 1.29·10^379 cells long: 887 levels (below) and a tail of 20 pairs at the left end.

## What the machine does

**Pairs and digits.** A *visit* is the head in A on the blank cell right of the tape. Read the tape from the head
leftwards in pairs of cells, X = `0 1`, Y = `1 1`, and write a word as *digits*: the lengths of its runs of Y between
the X's (`2 1 4 4` is `Y Y X Y X Y Y Y Y X Y Y Y Y`). Each visit adds one pair. At every second visit the word is

    front   4^n1 s1   4^n2 s2   ...   4^nk sk   tail

* the **front** is `2 1` or `5`; two visits later it is the other one. Going from `2 1` the head makes an *H-hit* on
  the rest of the word, going from `5` a *V-hit* (one visit for the hit, one short visit of 8 steps, the bounce);
* a **level** is a rung of n blocks `4` (the ten cells `0111111111`) and a separator s, one of the eight words
  `0 1 0 1`, `0 3 1`, `7 1`, `5 3`, `0 6`, `5 0 1`, `0 1 3`, `10`;
* the **tail** is what is left, down to the blank left end.

**A level is a digit with 16 values.** The separator and the kind of the next hit give 16 *positions*, and every
hit moves the level to the next one:

    position   0     1    2    3    4    5     6    7    8    9   10   11    12   13   14   15
    separator 0101  031   71   53   06  0101  501   71  013   06  10   501  031  013   53   10
    hit        H     V    H    V    H    V     H    V    H    V    H    V    H    V    H    V
    passes on             H         V               H              V         H              V
    rung +1                    x                    x                   x                   x

At ten positions the hit is absorbed (the separator changes, the rest of the tape is not touched); at six it is
passed on: the rest gets a hit, alternately H and V. The rung gains 4 blocks in 16 hits. A hit costs
112 n + c steps inside the level (H) or 56 n + c (V).

**Levels are transparent.** A hit on the rest is a fixed list of *calls*: the head crosses into the rest in one
state and comes back in another (V: in C, back in E; H: five calls, in C, E, B, C, D, back in E, F, E, A, E). What a
level does depends on the rest only through the states in which the calls return. So the part of the tape left of
a level lives exactly the life it would live with the front put directly before it, only slower: 6 hits for every 16.
The whole ladder is an odometer: level k gets (3/8)^(k-1) of the hits, and its rung is (3/8)^(k-1) as long
(the factor 8/3 between rungs seen in the earlier passes).

**The tail and the fuel.** Rarely the head runs into the left edge of the tape and comes back in an unusual state;
that flattens the ladder: every block `4` becomes `0 3` (the *reset*; at visits 3, 11, 25 and, with a ladder of six
levels, at visit 3,006, step 27,167,343). After a reset a new ladder grows at the right, and its tail eats the
flattened blocks one by one: with the fuel `(0 3)^m` to its left the tail goes through a cycle of 12 hits,

    7 3 3 > 5 4 0 4 > 4 0 7 0 4 > 4 0 1 0 1 0 3 4 > 4 4 0 1 3 0 1 4 7 > 5 4 7 > 11 7 > 4 0 1 0 1 0 10 >
    4 5 3 0 1 0 1 0 1 0 3 3 > 5 0 1 0 1 0 3 3 > 7 1 0 1 0 3 3 > 4 0 1 3 0 3 3 3 > 7 3 3

that uses up two fuel blocks and leaves three new levels. Every new level slows the tail down by 8/3, so the ladder
after the reset of visit 3,006 (fuel: 370 + 139 + 52 + 19 + 6 blocks and what the old separators became) needs about
(8/3)^887 visits to eat its way to the left edge.

**The halt.** When the fuel is gone the tail is `0 3 1 0 3 1 0 5`, with blank tape behind it, and an H-hit is due.
Its first three calls come back as usual; in the fourth the head (in C) runs through the tail, B reads the blank
cell left of the tape and steps left, and C reads a 0: the halting transition. (The machine halts exactly when B
reads a 0 that has a 0 on its left; inside the tape every 0 is single.)

## How the halting step is found

`py/accel.py` keeps the levels as a list of (position, n) with exact integer arithmetic and runs the machine itself,
cell by cell, only on the *reduced word*: the front followed by the tail (3,539 hits). When a hit on the reduced word
returns in unusual states, the deepest level is put back into the reduced word and the hit is tried again (587
times; never further than one level). Steps are counted exactly: per level from the closed form of
Σ (a·n + b) over its hits, per hit of the front, and in the reduced run for the tail; the last, unfinished visit from
the steps each level and the front take before the call that does not return.

What it rests on, and how each part was checked:

* **The level table for every n** (the table above, the call lists, that the rest is touched only through the calls):
  proved in Lean for every block count n >= 1 and every tape left and right of the level
  (`lean/Levels.lean`, kernel; one theorem for each stretch between two crossings of the level's borders), and tested
  on the machine for 16 positions x 28 block counts x 13 rests (`python3 accel.py levels`, 5,656 cases, which also
  measures every step constant).
* **The bookkeeping** (which level is where, visit numbers, step counts): the visit numbers and step counts of the
  accelerated run equal those of a direct run at all 291 compared visits up to step 1.18·10^11
  (`python3 accel.py check`), in three variants of the simulator (0, 1 or 2 levels kept in the reduced word, started
  at different visits). The run started at visit 600 predicts the reset of visit 3,006 at the right visit.
* **The whole run**: keeping the 1, 2 or 3 deepest levels in the reduced word (so that every level is simulated cell
  by cell for its first hits, and no level is ever put back) gives the same 887 levels, the same tail, the same visit
  number and the same halting step.
* **The last visit**: a tape with the 887 levels at their final positions, small block counts and the final tail
  halts under direct simulation after exactly the number of steps the formula gives (`python3 accel.py last`).

Not proved in Lean: the composition of these facts into `Halts`. That needs the induction over the list of levels
(the level theorems are there) and the 3,539 reduced hits as a certificate.

## Independent check

A second worker re-derived the result with separate code (`verify/`: `mymodel.py`, `measure.py`, `myrun.py`,
`final.py`, and the direct simulator `sim2.c`). Only the 16-position table was taken from this README; the step
constants were measured again.

* The re-derivation gives the same 887 levels, tail, last visit number and 759-digit halting step.
* Direct simulation equals the accelerated run at 12,169 checkpoints in 440 windows spread over the whole run
  (visit number, step count and whole tape), dense around the four fuel-segment boundaries.
* About 80 truncated endgames (front, two deepest levels and the real remaining tape), run directly to the halt,
  stop at exactly the predicted step; the longest takes 4,568,217,938,175 steps.
* 1,800 random synthetic tapes: 256 halts and 358 resets agree with the model, none disagrees.

What remains unobserved: the run between step 1.2·10^12 and the halt with more than about 14 levels on the tape. There
the result rests on the level rules proved in Lean for every block count and on the bookkeeping tested above. The halt
is not forced by the shape of the tape alone: a uniform small start of the same shape resets instead of halting.

## Status

* **Trusted (exact computation)**: the machine halts at the step above.
* **Lean (kernel)**: `lean/Levels.lean` (from `py/levels_lean.py`): the level rules for all n; `last_visit_halts`: the last visit on the word
  without its 887 levels (`2 1 0 3 1 0 3 1 0 5`, blank left) halts after 278 steps; `lean/Rules.lean`:
  whole visits for three families of words and a halting tape (`edge_halts`).
* **Lean**: `lean/Blank.lean`: the halting configurations; no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* **Trusted**: no halt in the first 10^12 steps (`c/mrun.c`, a direct simulator on 16-cell blocks, 3·10^9 steps a
  second; the head came to the left end at steps 1,779 and 27,158,883 only);
  closed tape languages (windows 4, 6, 8) confine the halt to the left end.

## Deep exact run

No halt in the first 6.00x10^19 steps: the macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with blocks of 10 cells ran
from blank tape to step 60,000,783,412,981,265,560. It is exact, and at this block size it agrees with the
direct simulator after 2,000,002,519 steps (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/deep.py run 240`, then `verify`).

## Pages

- [`pages/holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/explainer.html`](../../pages/holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/explainer.html)
- [`pages/holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/proof-status.html`](../../pages/holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/lean/check.sh
cd holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/py
python3 accel.py                    # the run to the halt: visit number and step (20 s; --defer 1..3: same result)
python3 accel.py levels             # the level table and the step constants against the machine
python3 accel.py last               # the last visit on a small tape with the same levels, direct against formula
gcc -O2 -o /tmp/visits ../c/visits.c && /tmp/visits 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB 1e10 A 2 100000000 2 > /tmp/v.txt
python3 accel.py check /tmp/v.txt   # visit numbers and step counts against the direct run
python3 words.py                    # the C visit against the Python one
python3 levels_lean.py > ../lean/Levels.lean      # regenerate the Lean level rules
python3 rules.py > ../lean/Rules.lean ; python3 vmodel.py 3000000        # the earlier word rules
```
