# 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA

bbchallenge id 9123. A BB(6) holdout whose halting from blank tape is open (group G07).
Family: **nested base-4 counter on pairs (a recursion on words) with fuel, an eater and right-end events**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LF |
| B | 1LC | 1RB |
| C | 1LF | 1LD |
| D | 1LE | 0RD |
| E | 1LB | --- |
| F | 1LA | 0LA |

## What it does

**Pairs.** Cut the tape into pairs of cells and write `X = 10`, `Y = 11`, `O = 00`. A *wall visit* is the head in F
on a 0 with nothing but 0s to its left. At a wall visit the tape to the right of the head is a word S over X and Y
(`0^inf F> 0 S 0^inf`; in 3·10^6 steps, 1,39x of the wall visits are of this kind and follow the rule below, the others are the
visits around the right-end events). The wall is the growing end: it moves **one pair to the left at every
visit**; the right end of the tape stands still between right-end events.

**The rule.** The next wall visit shows V(S) = G(S), one pair longer, where

    G(Y^a X X U)     = X^a Y Y Y U                      the head turns back at the first double X
    G(Y^a X Y^k X U) = X^a Y G^k(Y Y U)     (k >= 1)    a "digit" k passes k visits on to the rest
    G(Y^a)           = X^a Y Y                          the head reaches the blank right end in B

In the machine: B runs right over Y's; at `Y B> X X` it turns (`<F Y Y Y`); at `Y B> X Y^k X` state D erases the
k Y's, the pair before them becomes blank too, and B and F fill two of the k + 1 blank pairs: `X O^(k-1) Y Y Y B>`.
F, coming back, swaps X and Y in every pair it crosses, and on a blank pair it turns round again (`O -> Y`, B to
the right). So each of the k - 1 blank pairs left behind is a wall for the rest of the tape: the rest gets k
visits before F goes home. `py/gmodel.py` checks the recursion against the machine (20,000 random words; every
covered wall visit of the run from blank tape).

**The counter.** Read S as digits (the lengths of the runs of Y between X's). Then `1 0` is the six-cell word
`111010`, and after the first few hundred steps the tape is

    wall | 3 or 000 | (1 0)^N1 | w1 ... (1 0)^N2 w2 ... (1 0)^N3 w3 ...

with digit words w that cycle through four phases, `0000000 -> 3 00000 -> 0000 3 -> 3 00 3 -> 0000000`. Two wall
visits make one phase (a *bounce* `000 -> 3`, 16 steps, then a crossing of the first block), the block gains one
`1 0` in the second and in the fourth phase, and the fourth phase sends the head on into the rest of the tape (the
carry). All of it is **proved in Lean** for every block length n and every tape R to the right
(`lean/Rules.lean`: `bounce`, `phase1`, `phase2`, `phase4_in`, `phase4_out`): one cycle of 8 wall visits takes

    000 (1 0)^n 0000000 R    to    000 (1 0)^(n+2) 0000000 R'

in 104 n + 407 steps plus the time the head spends in R, and R' is what one visit makes of R (in the recursion:
R' = G(X R)). So the rest of the tape lives the same life eight times slower, whatever the block length is: that
is why the block lengths fall by about 4 from level to level (after 10^9 steps: 5998, 1492, 372, 88, 21) and why
level k moves once every 4^(k-1) phases. Between two levels there may be a frozen stretch of other digits
(for example `4 1 0 0 1 0 0 0 0 0 1 0 1 0 4 3 1 0 4 0 3 0 0 0` between the first and second block); they pass the
visits on unchanged.

**Right-end events.** The recursion stops when the head reaches the blank right end in D (S ends in `X` or
`X Y^k`): this happens when the last level overflows, at steps 1,937; 57,942; 61,755; 63,313; 83,647; 125,133; 48,737,226 in the first 10^13
steps (`rightvis`-style count: the head back at the right end after more than 1,000 steps away). What happens
then is not regular: the head comes back in A or D, pairs change parity (`01` pairs appear), blank stretches are
left inside the tape.
The event at step 48,737,226 is a **reset**: 29,000 steps later (step 48,766,065) the head, coming back across
the first block (1,308 copies), has turned it into a single run `1^7855`, and a new counter grows from there (the
earlier pass followed it to 4.5·10^9 steps; pieces of the long run of 1s are still being worn down at 2·10^9).

**Where it can halt.** Only E reading 1. In the pair picture that needs a blank pair with `11` or `01` to its left
at the moment the head backs onto it from a blank cell, which the counter never produces; a right-end event can.
There are words of X and Y on which the wall visit halts: the shortest is `X Y^7 X X` (253 steps; Lean:
`pure_tape_halts`), and 8 (this machine) or 18 (the twin) of the 16,383 words of at most 13 pairs do. None of
them is a tape of the run from blank. So the pair structure alone cannot prove that the machine runs forever: the
answer depends on which words the right-end events leave behind, and those look irregular.

Near-twin: [`1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA`](../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/README.md): the same table with C, D, E wired differently. The recursion G, the four
phases and their step counts are the same for both; the right-end events differ.

## Later pass: 10^13 steps

* **No halt in 10^13 steps** (trusted: `c/mrun.c` of
  [`1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB`](../1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/README.md), a direct
  simulator on blocks of 16 cells with a full table). At step 10^13 the tape reaches 300,908 blocks (about 4.8 million
  cells) to the left.
* **Right-end events**: after the reset at step 48,737,224 there is **none up to 10^13** (an event: the head back
  at the right end after more than 10^5 steps away).
* At wall visits 500 to 3,000 the tape has the same front and level forms as the twin (`0 0 0` / `3`, then
  `(1 0)^n` and one of four digit words); the head crosses the border of the front in the states `>D <F >B <F`.
* The twin's notes on the carry as a call and on an accelerator that strips levels apply here too: see
  [the twin's README](../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/README.md).

## Status

* **Lean (kernel)**, `lean/Rules.lean` (written by `py/rules.py`), for every count and every surrounding tape:
  the pair moves `reflect`, `flipX0/1`, `flipY0/1`, `turn0/1`, `digit1`, `digit`; the wall moves `bounce`,
  `cross`; the counter phases `phase1`, `phase2`, `phase4_in`, `phase4_out`; and `pure_tape_halts`.
* **Lean**: `lean/Blank.lean`: the halting configurations; no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* **Trusted**: `py/gmodel.py`: V = G on random words and on the run from blank tape; `py/blocksim.py` /
  `py/bscheck.py` (the earlier exact simulator on runs of `111010`). Direct simulation: no halt
  in 10^13 steps (`c/mrun.c` of the 1RB1LE_0LC1RE folder; 2·10^10 with `tools/c/tmrun.c`).
* **Trusted**: a closed tape language from windows of 6 cells confines the halt to a head with only 0s on its left
  (`python3 -m bbtools.ctl 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA 6`).
* **Open**: what the right-end events do in general, and so whether a halting word ever appears.

## Next steps

* The carry is a visit of the rest (`R' = G(X R)`), so the whole run is the iteration of one map on words, and the
  levels only set the clock. An accelerator that strips the regular levels (each proved rule of the form
  "p visits turn P(n) T into P(n + c) T' with T' a visit of T") would reach the right-end events directly,
  exponentially faster than any step-by-step run; the frozen stretches between levels need the same kind of rule.
* Extend the recursion to the three ways a visit of the rest can come back (F, the regular one; A; D) and to tapes
  with `01` and blank pairs: that is the full macro machine, and the place to look for an invariant or for a halt.
* A mirrored CTL certificate (left and right swapped) would make the confinement a Lean theorem.

## Deep exact run

No halt in the first 2.16x10^18 steps: the macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with blocks of 6 cells ran
from blank tape to step 2,166,473,947,245,007,495. It is exact, and at this block size it agrees with the
direct simulator after 2,000,010,334 steps (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/deep.py run 240`, then `verify`).

## Dedicated pass: an exact accelerator on digits, through the right-end events

The code is shared by the twins and lives in [`1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/py`](../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/py): `geng.py` (the recursion on digit words with rules found by
symbolic execution), `msim.py` (a cell-level macro simulator that hands wall visits to it), `accel_run.py`,
`accel_check.py`, `calibrate.py`; `c/wv.c` prints the wall visits of a direct simulation.

**The recursion on digits, with step counts.** Write a word as its digits (lengths of the runs of Y between
X's; the last digit is the trailing run) and h(T) = G(0 T) (a *hit* of the tape T). Then

    G(a T) = 0^a h(T)                    16 + 4a steps, plus those of the hit
    h(0 T) = 3 + T                       (the first digit of T grows by 3; no further step)
    h(k T) = 1 + G^k(2 + T)   (k >= 1)   2k steps, plus those of the k visits of the sub-tape 2 + T
    h()    = 2                           the hit of the empty rest: -4 steps (G(a) = 0^a 2 costs 12 + 4a)
    h(k)                                 a hit of the last digit: a right-end EVENT (not in the recursion)

and h(1 0 T) = 1 0 h(T): a unit `1 0` (cells 111010) passes every hit on, at 26 steps a crossing. The step counts
are exact: fitted, then checked on 3,995 random words for each twin (`calibrate.py`), and the accelerated run below
reproduces the step number of every wall visit it was compared with.

**What the tape is made of** (found by the engine, not put in by hand):

* a *level* is `(1 0)^n` followed by a digit word that cycles `0^7 -> 3 0^5 -> (1 0) 0^4 3 -> (1 0) 3 0^2 3 ->
  (1 0)^2 0^7`: four hits add two units and pass one hit on, so level i gets a 4^-i share of the hits;
* *frozen* stretches between levels pass every hit on unchanged;
* *fuel*: a run `(1 0 0)^m`. It is made when a frame `7 0 (1 0)^n ...` re-opens itself as its own last sub-visit
  (each round eats 6 units of the level and leaves `1 0 0` four times), i.e. an old level is turned into fuel;
* an *eater* at the bottom of the active ladder consumes 3 units of fuel every 11 hits and leaves fresh ladder
  rungs behind (the 20-digit word `1 0 4 0 0 0 1 0 1 0 4 3 1 0 4 0 3 0 0 0`, a level with n = 1); the rungs then
  grow as levels. This is the same economy as the fuel of the decided sibling
  [`1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB`](../1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/README.md), with one
  difference that matters: here an event that is not a reset turns ladders back into fuel, so the fuel does not
  simply run out;
* an *event* is a hit that reaches the last digit. On cells the head then runs to the blank right end in D, the
  sub-tape `2` at the end gets its visits, and on the way back every frame that was open is closed in a
  different way than in the recursion (a level `(1 0)^n` crossed by the returning head becomes one digit of
  about 3n: in the event after wall visit 186, `(1 0)^40` became the digit 126). The word at the next wall visit is
  again a word of X and Y.

**The accelerator.** `geng.py` keeps a word as tokens (a digit, `0^m`, `(1 0)^n`, `w^n` for a short word w)
with big integers as counts, and evaluates G and h recursively. Three kinds of rules are found automatically by
running the recursion on a prefix with symbolic counts and an opaque rest (every comparison made on the way is
recorded as a linear condition, so a rule is applied exactly as long as its conditions hold): *cycle rules*
(p hits change the counts of a prefix by fixed amounts and pass c hits to the rest; this finds the level cycle
and the eater), *run rules* (h(k w^n T) = E^(n-1) h(k w T)) and *recursion rules* (h(pre[n] T) = F h(pre[n - c]
T'), the frame that turns a level into fuel). `msim.py` simulates cells (blocks of 24, run-length coded, with the
right part of the tape kept as tokens until the head needs it); when the head stands at a wall with blank pairs on
its left and a pure X/Y word on its right it asks the engine for as many visits as there are blank pairs. So the
events themselves are done on cells and nothing about them is assumed. During an event the chain of open frames
found by the engine's failed attempt is reused as a list of facts (`plan`), which makes an event with ten thousand
nested frames a matter of seconds.

**Validation against direct simulation** (`accel_check.py` with the output of `c/wv.c`): the word right of the
wall *and* the step number agree at every wall visit compared, visits 1 to 1,422 (3·10^6 steps) and visits 112,522 to 112,524 (step 20,000,957,941): 1,425 visits, through all six early events,
with the outer wall advancing one visit at a time; and again, on the first 3·10^6 steps, with jumps of up to 7, 50
and 1,000 visits. The
recursion rules give the same word and the same step count as the plain recursion on a case that needs 2.3·10^7
recursive calls without them. Not done: an independent re-implementation, and a comparison beyond 10^11 steps
(out of reach of direct simulation), so the long run below is *exact by construction but only as trustworthy as
this one program*.

**The run from blank tape** (`python3 ../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/py/accel_run.py 2 60 100 7`, 7 s; exact numbers in
`../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/py/accel_run_2.txt`):

* events follow the wall visits 3, 14, 23, 186, 189, 5,424 (steps 47; 768; 1,729; 56,552; 59,211; 48,700,374);
* after the event of visit 5,424 a ladder grows on fuel as in the twin: 164 levels at wall visit 10^100, 243 at
  the next event. **No event between visit 5,424 and visit 4.137·10^148** (step 2.967·10^297; 149 and 298 digits);
* at that event the simulator takes the head to the right end and starts back, but then meets a fuel run
  `(1 0 0)^1,778,879,143,158` under an eater: every 11 hits leave a 20-digit rung behind, and the engine has no
  rule that emits such a word, so it would need 10^12 nested calls. The run stops there.

So: **no halt up to wall visit 4.137·10^148, step about 2.967·10^297**, if the accelerator is right (the earlier exact macro run
reached 2.16·10^18 steps). The halting question stays open, for the same reason as for the twin
([`1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA`](../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/README.md), which was followed through one more event, to step 3.1·10^4475).

**Next steps** (in this order): (1) cycle rules that emit an arbitrary frozen word, not only `1 0` units, with
that word as a run token on the digit side and on the cell side (blocks whose period is not a divisor of 24);
(2) the walk through a run of rungs during an event as a rule (now one nested frame per rung, on cells); (3) the
event itself as a second recursion on digits: the return sweep is a transducer on the open frames, and with it
the whole machine would be one map on digit words, the place to look for an invariant or for a halt.

## Long accelerated run (16 November 2026)

**No halt up to wall visit about 10^25600 (step about 1.733·10^51200)**, and no right-end event after the seventh
one. The old run stopped at the seventh event, after wall visit 4.137·10^148, at step 2.967·10^297.

*Why the old run stopped, and the new rules* (all in the shared `geng.py`, all found by symbolic execution with an
opaque rest, like the old ones):

1. *Frozen words.* During the seventh event's return, an eater sat on a fuel run `(1 0 0)^1,778,879,143,158`. Every
   11 hits it emits the 20-digit rung `1 0 4 0 0 0 1 0 1 0 4 3 1 0 4 0 3 0 0 0`. In that context the rung is frozen:
   h(w X) = w h(X) for every nonempty X, at a fixed crossing cost. The engine now proves such words by running h
   symbolically on `w ++ opaque`. Cycle rules may emit a frozen word once per cycle, and the crossings of the later
   hits are summed in closed form. Frozen prefixes are stripped from runs of hits, as the `1 0` units already were.
   Before this change, each rung was a new nested frame, about 10^12 of them.
2. *Nested frames.* Next, G^12(2 (1 0 0 3 0)^n X) opens G^12(2 (1 0 0 3 0)^(n-1) X) at its 7th visit and then
   works on the inner result. This is a recursion that is not a tail call, and it was 5.7·10^20 deep. A
   nested-frame rule op^q(A[n] X) = U V^j h^(cj)(Z) is now derived from a symbolic run of one level, in which the
   inner frame answers as a hypothesis `U ++ Y`. The rule is checked by computing the base case directly and is then
   applied by induction.

*Validation.* `accel_check.py` was run against direct simulation (`c/wv2.c`): all 1,422 compared wall visits agree,
words and step numbers. In `py/validate_new.py`, 400 random cases plus eater and nested cases give the same words
and step counts with the new rules as with the plain recursion (rules off) and as with `Gref`. With the new rules
the twin's first eight events are reproduced digit for digit (visits and steps).

*The run, first pass* (`STACKMB=128 python3 accel_run.py 2 3000 100`, under `ulimit -v 3000000`, 14 minutes):

* The run passes the seventh event (460 s) and its return sweep.
* After that, the outer wall doubles its jumps through visit 10^200, 10^400, ..., 10^6400 and 10^12800. No
  event and no halt occur. At visit 10^12800 the tape has 456,166 tokens and 36,647 levels `(1 0)^n` with n > 50.
* Then the run ran out of memory. The next jump is a carry that descends through the levels, one engine frame
  (`h^q`) per level, more than 31,000 deep. Memory grew with the square of the depth: 0.3 GB at depth 8,000,
  1.2 GB at 16,600, 2.3 GB at 22,800. That came from live cons cells, not from big integers (the frames' own
  integers were about 230 MB at depth 17,800, and `gc.collect` freed nothing).

*Why the memory was quadratic, and the fix.* A word is a linked list. When a level passes hits on to the rest, the
rest is rebuilt down to the deepest place that changed. Each open level kept a reference to its own input, the old
version of the whole rest below it, so the levels held about depth²/2 cells between them. That input is needed
again only if the carry stops early, at an event. Two changes, both in `geng.py`:

* *Dropped inputs.* Below depth `NDROP` (1,500), a level that hands a carry to the rest now lets go of its input
  first (`DROP`). If the carry then stops early, the engine raises `Replay`, and `msim.try_hook` redoes the
  whole call with dropping off. So results are unchanged, and only events deep in a carry pay the old memory.
* *Cost scoping.* Each power frame counts its own steps from 0 and adds them to its caller's count when it ends,
  instead of taking snapshots of the huge running total. This is exact, because integer addition is
  associative.

The changes were validated as follows:

* `accel_check.py` agrees with direct simulation at all 1,399 and 1,422 compared wall visits (words and step
  numbers). This holds with `NDROP=3` and `NDROP=30`, which force dropping and replays on the early events.
* The twin's eight events are identical, visits and steps, with and without dropping (`NDROP=3`, 3 replays).
* `validate_new.py` gives ALL EQUAL on 400 random cases with `NDROP=3`.

*The run, second pass* (`MEMLOG=1 STACKMB=256 python3 accel_run.py 2 5300 100 1000 400000`):

* The run is faster than before: it reaches 10^6400 at 324 s, against 468 s.
* At depth 20,000 it uses 0.39 GB, against 1.8 GB before, and memory now grows linearly.
* It passes 10^12800 (441 s), and then visit 10^25600 at 1,008 s. There the word has 739,128 tokens and 57,907
  levels, and the descent went 41,800 deep in 1.08 GB.
* There was no event and no halt.

*Why it stops now.* I stopped the run there, to give the core to the twin. The next jump would go about
115,000 levels deep. The integers in each frame also double in size, so it would need about 4 GB. Going further
needs the frame integers shared or dropped too, or the carry through the levels as one rule.

Trust: computations, exact by construction, validated only as far as direct simulation reaches (about 10^11 steps).
They were not re-derived independently.

## Level-stripping accelerator (22 November 2026)

**No right-end event, and so no halt, before wall visit 10^(8.73·10^146)**, against 10^25600 for the run above
(the first phase alone gives 256^(2.394·10^146), about 10^(5.77·10^146)). The accelerator is described in the twin's README (section "Level-stripping
accelerator"; code `py/lsa_*.py` there, arithmetic in `lean/Accel.lean` there): the ladder of levels is a
mixed-radix counter, and an eater's K super-cycles are jumped at once with a closed form.

*The word at wall visit 10^3200* (`python3 lsa_run.py 2 3200` in the twin's `py` folder): 5,316 levels at the top,
then the eater `6 0^1 3 0^3 (1 0)^1 4 0^4 3` on a fuel `(1 0 0)^m` with m = 6.46·10^147, and below it about 300
smaller fuels, each about a half to a third of the one before.

*The first phase.* That eater is of the ×256 kind: 3,633 hits burn 27 units of fuel, pass 5 hits down and leave a
block of four base-4 levels. It runs K = 2.394·10^146 super-cycles. The region below takes all
5K = 1.2·10^147 hits in one `hpow` without an event: its first level is a sink. So the phase ends, and each of
its K blocks multiplies the hits needed from above by 256. Every hit at the top of that region is at least one wall
visit, which gives the bound above.

*After it.* The sink becomes fuel 3.99·10^146 for a ×16 eater. Then come ×64 eaters (730 hits, 4 units of fuel,
21 hits down) on runs of the 20-digit rung `1 0 4 0 0 0 1 0 1 0 4 3 1 0 4 0 3 0 0 0`, in all its rotations. Each
fuel is an affine function of the round count before it: 5K/3 after the ×256 phase, 10K/11 after the ×16 phase,
(21K + δ)/11 between ×64 phases, with δ small. So a fuel shrinks by a factor of about 2.1 per phase, down to single
digits. That is one *descent*: about 3 phases per decade of the fuel `(1 0 0)^F` that started it. Then the next fuel
`(1 0 0)^F` of the bottom word starts the next descent.

*The long run* (`LSA_CKPT=ck.pkl python3 lsa_run.py 2 3200` in the twin's `py` folder, with the cached transitions
described there): 42,000 phases in about 3 h, in 233 descents, with no event. Kinds: 41,494 ×64,
424 ×1024, 58 ×16, 23 ×256. Composing the phases gives the top hits needed to get that far:
2^(2.899·10^147), so **no right-end event, and no halt, before wall visit 10^(8.73·10^146)**.

*Why the event is still out of reach.* The bottom word does not run down. At visit 10^3200 it held 259 fuels
`(1 0 0)^F` with 23,132 digits in all. After 233 descents it holds 269, with 24,688 digits: each descent leaves about
one new fuel behind. The fuels that start a descent only shrink slowly, from about 10^146 to about 10^115 over those
233 descents. The bottom is itself a counter, one level above the descents. Reaching the event needs that counter
as a rule: a descent as one step on the list of fuels.

*Descents of descents.* The fuels that start the descents follow the same law one level up. In the 42,000 phases,
after a few irregular starts (146, 144, 146, ..., 142 digits), the starting fuels go 120, 120, 120, 119, 119, 119,
..., 35, 34, 34, 34 digits: three descents per digit, so they too shrink by a factor of about 2.1 from one descent to
the next. Then a fuel of 125 digits starts the next such run. So the bottom is a hierarchy of the same shape at every
level: a descent is about 3·D phases on a fuel of D digits, a second-level descent is about 3·D descents, and so on.
The number of phases to the event grows like a power of the fuel sizes with as many factors as there are levels,
far beyond what any run of phases can reach. The next step is to prove the self-similarity: that a descent of level
k on a fuel F acts on the rest of the word like one phase of level k − 1, with its round count and block map as
functions of F. Then the levels could be jumped like the phases are now.

Trust: computations, exact by construction. The phase jumps reproduce the twin's seventh event exactly
(kinds ×256, ×16 and ×1) and agree with plain batches on 6 words with a ×64 phase; the cached transitions agree
with the plain steps over the first 700 phases.

## The descents as arithmetic, and the factory rule (22–23 November 2026)

**What was asked:** prove the descent recursion and skip whole descents, to reach the eighth right-end event.
**What came out:** the laws between phases, measured on 12,482 phases and proved as arithmetic in Lean
(`lean/Descent.lean`); three fixes that let the accelerator run past phase 30 again; the rule of the *factory*
that writes the fresh fuels (11 hits make one rung), checked with symbolic counts, and law A derived from it in
Lean (`lean/Factory.lean`). The bottom word does not grow: what looked like a growing list of runs is one run
stored in many pieces. The event is still out of reach, and no new bound: the logged phases give exactly the
bound above.

*Three fixes in the twin's `py/lsa_phase.py` and `py/lsa_region.py`.* Run again from the word at wall visit
10^3200 (saved as `g07/lead12/start2_visit1e3200.pkl` in the project files; 43 min to rebuild), the accelerator
stalled for more than half an hour after phase 30. Causes, all fixed:
* when an eater stops with a little fuel, say 9 rungs of one rotation, the next run of the same word follows in
  another rotation: `(t s)^9 t (s t)^F`. That is `t (s t)^(F+9)`, one fuel, but as tokens it is two, so no known
  eater shape matched. Copies of a run's word just before it are now folded into it, digit by digit
  (`fold_toks`, also in `head_split`, so the cache key of a transition stays the same);
* single-hit feeding asserted that the bottom gets exactly one hit per batch, but one hit of a level can pass
  two; it now takes them (`Region.feed`);
* a cached transition starts with single hits (the next eater can take its regular shape at any hit of its
  cycle), but there it only looks up shapes already known; a new super-cycle search at every hit took minutes.

The run then went at about 17 phases a second, slowing to about one a second at phase 12,000.

*The laws* (`python3 py/lsa_laws.py LOG` in the twin's folder, on the log written with `LSA_LOG=LOG`). The eaters
of the ×64 kind leave a slack F − 4K of 5 to 9. Their fuel is a run of the 20-digit rung, and the rung is a
*frozen* word: a hit crosses a run of rungs unchanged (494 steps a rung), so the 21 hits a super-cycle passes down
go through every run of rungs to the next part of the word that is not frozen. Of the next fuels after a ×64
phase:
* 6,936 are fresh and follow **law A**, 11 F' = 21 K + e with −913 ≤ e ≤ 224 (almost all between 24 and 150):
  one rung for every 11 hits passed down, a ratio of 44/21 ≈ 2.1 per phase;
* 1,401 are fresh and follow **law B**, F' = K + δ with 2 ≤ δ ≤ 12: one rung for every 21 hits, a ratio of 4;
* 4,063 are older runs of the word, met when a chain of fresh fuels has run out.

*Descents of descents.* A run of fresh fuels is a descent. In the log they come in families: from phase 5,379
the descents start on fuels of 120, 120, 119.7, 119.3, ..., 106.9 digits (0.32 digit less each time, the ratio of
law A once more) and last 185, 171, 146, 129, 108, 93, ..., 4, 2 phases. Then a new family starts on 124 digits.

*The bottom word does not grow.* Counted as tokens, the long runs below the eater went from 362 at the start to
5,257 at phase 12,000, which first read as a growing list of "staircases" (an earlier version of this section
said so). They are not separate runs: the digits across each junction are periodic with the rung's period 20, so
neighbouring pieces in different rotations are one run that the engine stored as several tokens. Merged
(`groups` in the twin's `py/lsa_laws.py`, and now in the accelerator itself, `MERGE` in `py/lsa_phase.py`):

| after phase | long runs | their digits | of them fuels (1 0 0)^F |
|---|---|---|---|
| 0 (wall visit 10^3200) | 279 | 24,236 | 262 |
| 13,999 | 306 | 27,474 | 272 |

So the word below the eater is a list of about 270 fuels (1 0 0)^M and a few dozen rung runs, and it barely changes
over 14,000 phases. Merging also makes most "older run" transitions disappear: on the first 1,404 phases of the
merged run, 1,294 follow law A, 80 law B and only 18 are other transitions (−58 ≤ e ≤ 174).

*The factory: where law A comes from.* Behind a ×64 eater the word reads

    (10) 4 0^6 (10) 4 0^4 3 [100]^M 3 4 0^3 4 3 4 0^3 (10) X

and every hit the eater passes down lands there. Run with symbolic counts n and M (`python3 py/lsa_factory.py` in
the twin's folder), each of the 11 states of its cycle gives the same rule, for every n ≥ 1 and M ≥ 7 (25
recorded conditions, all of that form):

    11 hits:  (10) [rung]^n 4 0^6 ... [100]^M ... X   ->   (10) [rung]^(n+1) 4 0^6 ... [100]^(M−6) ... h^2(X)

So the factory writes one rung of the next fuel for every 11 hits, burns 6 units of its [100] fuel and passes 2
hits on. An eater phase of K super-cycles passes about 21 K hits down, so the next fuel F' has 11 F' ≈ 21 K: law
A. In Lean (`lean/Factory.lean`, for every value, the rule as a hypothesis): `iter` (q cycles add q rungs, burn
6 q fuel, pass 2 q hits), `rungs_bounds` (t + 11 lo ≤ 11 n_t + 10 and 11 n_t ≤ t + 11 hi) and
`lawA_of_factory` (a phase of k super-cycles whose H hits, 21 k − s0 ≤ H ≤ 21 k + s1, all reach the factory
writes a fuel satisfying `Descent.LawA` with offsets 10 + s0 and s1 + 11 hi). The offset e of law A is the
factory's phase in its cycle plus the hits at the ends of the phase.

*No new bound.* With phase j needing at least a_j^(K_j) times the hits of what is below it (`blk_ge`), a stack
of phases needs at least 2^(Σ K_j log2 a_j) top hits (`phases_compose`). Over the 12,482 phases that is
2^(2.8989·10^147), the bound of the 42,000-phase run (wall visit 10^(8.73·10^146)): it all comes from the first
phases, whose fuels have 146 to 148 digits; after phase 5,000 no fuel had more than 127 digits. The word still
holds fuels of up to 147 digits further down, and when the eater gets to them the exponent grows again, but each
phase adds at most about 10^148 to it (the fuel times log2 a, while fuels stay below 10^148). So the bound grows
only like the number of phases, and skipping descents raises it only if it skips very many of them; the event
itself comes when the whole list is used up.

*In Lean* (`lean/Descent.lean`, for all values; the offsets are hypotheses, the run's constants an instance):
`lawA_step_lower`/`upper`, `lawB_step` for one phase; `descent_A_lower`/`upper` (21^j (23 F_0 + c) ≤ 44^j
(23 F_j + c) and 44^j · 23 F_j ≤ 21^j · 23 F_0 + 44^j · 4 hi) and `descent_B_lower`/`upper` (factor 4) for a
descent; `phases_compose` and `blk_ge` for the top hits over a stack of phases. This is the arithmetic only. That
the machine's phases satisfy the laws is the log, not a proof.

*What a level skip still needs.* The picture is now a flow of hits through a few kinds of parts: an eater
turns 4 rungs into 21 hits (multiplying the hits needed above by 64), a factory turns 11 hits into one rung and 2
hits further down while it burns its [100] fuel, and below it the next factory. A skip one level above the eater
phases would run this flow as arithmetic. The three missing pieces (law B, a factory out of fuel, where the 2
hits go) are in the next section.

Trust: computations, exact by construction; the laws are observations over 12,482 phases; the factory rule is
a symbolic run of the digit recursion (the engine, not Lean); the Lean files are the arithmetic, with the
factory rule as a hypothesis.

## Law B, the ladder, and refuelling (23 November 2026)

**What was asked:** the three pieces a level skip still needed: the rule behind law B, what a factory does when
its fuel runs out, and where the 2 hits it passes on go.
**What came out:** law B is not a rule of the machine; the hits go to a base-4 *ladder*; and when the fuel runs out
the factory burns the top block of that ladder. Each rule is checked on the digit recursion (the engine), not in
Lean. No new bound yet.

*Law B was the engine's bookkeeping.* Every law-B transition was the eater crossing from one piece of a run of the
rung to the next piece of the same run (the junction digits are periodic). The merge of such pieces was not
applied where the cached transitions pick the next fuel (`head_split` in the twin's `py/lsa_phase.py`). With that
fixed, the first 1,050 phases from wall visit 10^3200 have no law-B transition at all: 1,018 follow law A
(−42 ≤ e ≤ 174), and the 20 others are the ends of descents (every ~440 phases the eater moves on to the next
fuel [100]^M) and one stretch of 17 phases on older rung runs. They give the same bound as the 1,404 unmerged
phases (Σ K log2 a = 2.8986·10^147). The twin's seventh event comes out the same.

*Where the 2 hits go: a ladder.* Below the factory's fuel the word holds five blocks (10)^R0 ... (10)^R4
(R0 = 10^143.5, each about a quarter of the one before), with counter digits 0^7, 0^4 3, 3 0^2 3 in the junctions,
then the next fuel [100]^(10^146.5) and below it the next, larger ladder. The ladder counts the factory's hits in
base 4: after 11 q hits to the factory, block i has grown by q / 4^i, up to the carries (|error| ≤ 1). So R0 is
about the number of hits the factory has had, divided by 11.

*When the fuel runs out the factory refuels from the ladder.* A few hits after [100]^M is used up, the top block
becomes the next fuel and the ladder moves up by one block:

    (10)^R0  ->  [100]^(2 floor((R0 − 1) / 3) − 4),     R'_j = R_(j+1) + (R0 / 3) / 4^(j+1)  (|error| ≤ 3)

and the fuel after the ladder gains at most one unit. So the new ladder is about the old one divided by 3, and
the factory goes on. Its new fuel lasts about 11 R0 / 9 more hits.

`python3 py/lsa_refuel.py N` in the twin's folder checks both rules on N random ladders (40 checked: worst carry
error 0.75 for counting and 2.75 for refuelling). The word there is the one after phase 999, with the block lengths
and the fuels as parameters. With the factory rule (`py/lsa_factory.py`) this gives the whole flow below an eater:

* an eater turns 4 rungs into 21 hits and multiplies the hits needed above it by 64;
* the factory turns 11 hits into one rung of the next fuel and 2 hits for the ladder, and burns 6 units of
  [100] fuel;
* the ladder counts the hits in base 4;
* when the fuel is gone, the ladder's top block becomes the next fuel.

A level skip would run this flow as arithmetic until the ladder and the fuel after it are used up. That is the
next step. The rules here are observations of the engine on many values, not yet proofs.

*The long run, merged (23 November 2026, night).* Two more bugs in the accelerator held the run back. Both were
eaters it never treated as phases, so they were fed 200 hits a batch for hours:
* an eater shape was marked as having no super-cycle when its block was not regular at one hit. That depends on
  the hit, not on the shape. After phase 1,756 an eater on 66,946 rungs was skipped this way. Now a shape with a
  known super-cycle is always used (`find_phase`), and an irregular block only starts single hits;
* the head of an eater could have at most 16 tokens before its fuel. After phase 12,174 one had 17. Now it can
  have 24 (`HEADMAX`).

With both fixed the run went from wall visit 10^3200 to phase 13,008. That is 12,488 law-A transitions, and law A
holds throughout (−76 ≤ e ≤ 284). The run starts 136 ×256 phases on [100] fuels, and 30 of them begin a long descent (100 phases or more). Their starting fuels fall from 10^147.8 to 10^43:
the [100] fuels near the eater are used up one after another. The bound is still that of the first phases. At
phase 13,008 the run stalls again, this time inside the engine. A ×16 phase passes 10^42 hits into a stack of
ladders, (10)^N blocks from 10^45 down to 10^36, and the engine carries them level by level. The ladder rule of
`py/lsa_refuel.py`, done as arithmetic, is what is needed there.

*Past phase 13,008 (23 November 2026, day).* The stall is where the descents first run out of [100] fuel under a
×16 phase: at phase 12,886 a [100]^5.7·10^43 fuel lay there, at 13,008 the next thing down is the top block
(10)^n of the base-4 ladder (n ≈ 2.6·10^42). Three hits turn that block into fuel [100]^(2n/3), and the rest of the
4.8·10^41 hits pile up in a new block above it, (10)^(q/2), which the engine built one hit at a time (13 s per
million). Under it lies a ladder of about 70 blocks; a run of x hits adds x/12 to the first and a quarter less to each
next one. Three changes in the accelerator (twin's `py/lsa_phase.py`, `py/lsa_ladder.py`):
* the ladder now also takes levels that keep every hit, levels with a literal fuel inside, and levels whose count
  falls (it counts them down in closed form; when one runs out, one plain hit takes it through its refuel). When a
  word cannot be cut into levels, 256 plain hits are done and it is cut again. The engine's own large powers
  (h^q and G^q met inside its recursion) go this way too. The 4.8·10^41 hits now take under a second;
* after 64 batches with no phase the batches double (up to 65,536 hits; exact either way);
* an eater region may take in more than 16 tokens of the rest while the hits it passes down still need more of it.
  The ×16 eater after phase 13,010 passes its hits through the next [100] fuel and needs 17.

Checks: the twin's 7th event from 10^1600 is the same exact visit; at phases 12,000 and 12,886 the new code gives the
same tape (a polynomial hash over the digits) and the same step count as plain hits. The phases themselves can come
out at another hit of an eater's cycle, since the word is cut into tokens differently. The run now goes on past
13,008: 13,009 is a ×16 phase on the leftover fuel, 13,010 a ×256 phase on the new [100]^1.7·10^42 fuel, and from
there ×16 and ×256 phases on the [100] fuels of the stack (10^42 to 10^45) follow. The 8th right-end event is not
reached yet.

*To phase 16,282 (24 November 2026).* The run then went on to phase 16,282 (about 400 phases an hour while the fuels
were small, 10^2 to 10^7, and faster again on the 10^20-scale fuels further down). Phases 16,281 and 16,282 have
the fuels of 16,168 and 16,169 to the last digit: the word near the top repeats every 113 phases, while the
levels above it count. At the same point of that period the run stalls again, and it does so reproducibly from a
checkpoint. One batch of 200 hits takes about 13 minutes. Below the region lies a smaller copy of the ladder stack,
(10)^n blocks with n ≈ 10^23 and [100] fuels of 10^23. The 8th hit of the batch turns the top block into
[100]^(2n/3), as at phase 13,008, but here the engine finds no recursion rule for it: G^7(2 (10)^n X) calls
G^7(2 (10)^(n−2) X′) with a G^3 into X between, and the head of X runs through four states
(0^4 3 4 …, 3 0^5 4 …, 0^7 4 …, 3 0^2 3 4 …) before it repeats. So the recursion is n/3 levels deep, and the
time is linear in n (2.7·10^−4 s per unit: 27 s at n = 10^5, so about 10^15 years at n = 10^23). What is needed
is a recursion rule over several levels at once (the four states of X as one period). That is the next piece.

*Past the stall (25 November 2026).* A closer trace corrected that diagnosis: the engine does have and use a
recursion rule here, h(7 0 (10)^n S X) = (100)^4 h(7 0 (10)^(n−6) S h(X)) over the four states S, and it passes
n/6 hits on. The linear cost was in those passed hits. Below the block lies a stack of factory rungs
431010434000, some written out as digits and some as runs (431010434000)^k, and each hit walked it digit by
digit. The rung is a frozen word, h(w X) = w h(X) for every nonempty X at a fixed 364 steps, and so are its
rotations that start with a nonzero digit (101043400043, 104340004310, 434000431010, 400043101043). The engine (twin's `py/geng.py`,
`frozen_unfolded`) now recognises a frozen word in digit form, crosses it in one step and folds it into a run token.
If the word's first i digits are followed by a run of its rotation, a v^n Y = u^n a Y, and the hit crosses all n
words at once. The slow hit at n ≈ 9.3·10^22 now takes 43 s instead of being linear in n (27 s at n = 10^5 before,
0.1 s now). Checks: on the stalled word at n = 3,000 and 20,000 the new and the old engine give the same tape (a
polynomial hash over all digits) and the same step count, and the 7th right-end event of the twin
1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA is unchanged. Resumed from phase 16,281, the run went on to phase 18,400
by 26 November, at about 10 phases a minute, after three more fixes. A chain of rungs and (10)^n units is now
crossed in a loop, not by recursion: a long chain had hit Python's recursion limit after phase 16,305. A run of any
rotation is crossed at once when it ends with the digits read so far, a (b a)^n = (a b)^n a with a b frozen. At
phase 16,349 a 28-digit frozen word had been matched against a run of 2.5·10^16 rungs one rung at a time. Last,
the ladder's transition cache is emptied when it passes 400,000 entries, because it grew by 250,000 entries a
minute and the process was killed for memory.

*Law phases (27 November 2026).* The run stalled again at phase 28,829. The eater there, 3 4 0^1 4 3 0^3 10 3 4 0^3
(10)^1 (43400010)^n with n ≈ 1.8·10^9, has a super-cycle of 33,549 hits for 9 units of fuel, but the block it leaves
ends in a lone 0^6 that is not a level, so the block map cannot cut it, and none of 87 rotations of the cycle is
regular. Measured hit by hit, the top hits between successive units of fuel repeat with a period of 18 units, each
period costs exactly 2^24 times the one before, the rest below gets 33 hits a period, and the word after a period is
a new 141-token block followed by the word before it, unchanged but for the fuel. That is the phase law the
unwinding already uses, with a = 2^24 and b = 0. The new `py/lsa_law.py` measures this on the region, checks it
exactly over three periods (the ratio, the rest count, every single step inside the periods, and the block
identity), and hands it to `lsa_phase` as a super-cycle; it first steps the region to the unit from which the law
holds. It is an observed law, checked each time it is used, not a symbolic proof like the regular super-cycles.
Checked on the stalled region: two periods by the law give the same hit count as the direct measurement. From
phase 28,820 the run passed 28,829 in minutes, with law phases at 28,830 to 28,835 and later ones.

*Emitter jumps (27 November 2026).* The run went on to phase 37,593, where the rest below the eater was to get
1.045·10^12 hits. That rest begins with an eater that leaves a frozen word behind it at every cycle: every 11 hits
it uses 6 units of its (100)^a fuel (a ≈ 9.6·10^13), gives the word below it 2 hits, and adds one more copy of the
frozen word u = 10400010104310403000 (h(u X) = u h(X), 494 steps) in front of it, e0 u^n e1 (100)^a Y →
e0 u^(n+1) e1 (100)^(a−6) h^2(Y). The ladder cut the copies of u into levels that pass every hit, so the eater got
all the hits one at a time (40,000 a second) and the process ran out of memory. The new `py/lsa_emit.py` runs the
eater on an opaque rest, finds the period with its inserted word, checks it over four periods, with every large
run made smaller, and with more copies of u in place, and then takes K periods at once as a run (u)^(n+K). The rest
below gets its 2K hits from the engine. Like the law phases it is an observed law, checked each time it is used; the
frozen word and the opaque rest are exact. Checks: on the stalled word with 2,000,000 and 1,234,567 hits, the jump
and the old engine give the same tape (a polynomial hash over all digits) and the same step count, in about 1.4 s
instead of 48 s and 30 s. All 1.045·10^12 hits now take 2 s.

## Pages

- [`pages/holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/explainer.html`](../../pages/holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/explainer.html)
- [`pages/holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/proof-status.html`](../../pages/holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/lean/check.sh
cd holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/py && python3 rules.py > ../lean/Rules.lean   # regenerate the Lean rules
python3 gmodel.py 3000000                                      # the recursion against the machine
gcc -O2 -o tmrun ../../../tools/c/tmrun.c && TMRUN=./tmrun python3 bscheck.py 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA 111010 F L 2000000
cd ../../../tools/py && python3 -m bbtools.ctl 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA 6
gcc -O2 -o wv ../../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/c/wv.c && ./wv 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA 3e6 0 1 > ref.txt && python3 ../../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/py/accel_check.py 2 ref.txt   # accelerator against direct simulation
python3 ../../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/py/calibrate.py 2 && python3 ../../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/py/accel_run.py 2 60 100 7                 # step constants; the accelerated run
cd ../../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/py && LSA_LOG=log.pkl LSA_CKPT=ck.pkl python3 lsa_run.py 2 3200   # the phases from visit 10^3200, logged
python3 lsa_laws.py log.pkl --ckpt ck.pkl                       # the laws between phases; the bottom word of the checkpoint
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LA_1RC1RE_1RD0RD_1LA1RC_1RF0LE_1RA---`](../1RB1LA_1RC1RE_1RD0RD_1LA1RC_1RF0LE_1RA---/README.md): rename A→D, B→A, C→B, D→E, E→F, F→C and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
