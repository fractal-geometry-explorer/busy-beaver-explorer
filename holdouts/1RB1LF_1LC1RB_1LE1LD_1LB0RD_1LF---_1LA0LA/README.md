# 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA

bbchallenge id 34090. A BB(6) holdout whose halting from blank tape is open (group G07).
Family: **nested base-4 counter on pairs (a recursion on words) with fuel, an eater and right-end events**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LF |
| B | 1LC | 1RB |
| C | 1LE | 1LD |
| D | 1LB | 0RD |
| E | 1LF | --- |
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
k Y's, the pair before them becomes blank too, and C and F fill two of the k + 1 blank pairs: `X O^(k-1) Y Y Y B>`.
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
`X Y^k`): this happens when the last level overflows, at steps 1,937; 4,828; 24,290; 26,031; 17,047,480,846; 19,980,179,600 in the first 2·10^10
steps (`rightvis`-style count: the head back at the right end after more than 1,000 steps away). What happens
then is not regular: the head comes back in A or D, pairs change parity (`01` pairs appear), blank stretches are
left inside the tape.
The event at step 17,047,480,846 came when all six blocks overflowed together (block lengths 24785, 6188,
1546, 381, 94, 20): the word behind the last block changed from `...6 0 3 4 <12> 3 0 0 0 0 0` to
`...4 6 3 0 4 1 0 4 1 0 0 3 3 0 0 0` (digits) and the counter went on. The next one, at step 19,980,179,600, was a
**reset**: 10^8 steps later the tape holds, from the left, the first block frozen in its crossed form
(`(111110)^26833`, shifted by one cell against the pairs to its right), a stretch of 17,802 blank pairs, and
right of it a new counter that uses the blank stretch as its wall, one pair per visit (14,602 blank pairs left at
step 2.018·10^10, 8,314 at 2.048·10^10). No wall visit of the old left end happens in that time.

**Where it can halt.** Only E reading 1. In the pair picture that needs a blank pair with `11` or `01` to its left
at the moment the head backs onto it from a blank cell, which the counter never produces; a right-end event can.
There are words of X and Y on which the wall visit halts: the shortest is `X Y^8 X X` (257 steps; Lean:
`pure_tape_halts`), and 8 (this machine) or 18 (the twin) of the 16,383 words of at most 13 pairs do. None of
them is a tape of the run from blank. So the pair structure alone cannot prove that the machine runs forever: the
answer depends on which words the right-end events leave behind, and those look irregular.

Near-twin: [`1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA`](../1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/README.md): the same table with C, D, E wired differently. The recursion G, the four
phases and their step counts are the same for both; the right-end events differ.

## Later pass: 10^13 steps, the reset followed, an accelerator that stalls

* **No halt in 10^13 steps** (trusted: `c/mrun.c` of
  [`1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB`](../1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/README.md), a direct
  simulator on blocks of 16 cells with a full table, about 3·10^9 steps a second; it finds the same right-end events as the earlier runs). At step 10^13 the tape reaches 313,099 blocks (about 5.0 million cells) to the left.
* **Right-end events**: after the two at steps 17,047,480,846 and 19,980,179,598 there is **none up to 10^13**
  (an event: the head back at the right end after more than 10^5 steps away).
* **After the reset** (step 19,980,179,598): the new counter eats the blank stretch (15,953 blank cells left at
  step 2.05·10^10, 2,069 at 2.1·10^10), then turns the frozen first block into blanks from its right end and eats
  those too (115,277 blank cells at 2.2·10^10, 20,945 left at 3·10^10). At 10^11 steps the tape is again a plain
  counter with the wall at the left end.
* **The carry as a call.** A level is `(1 0)^n` followed by one of four words of digits (`0000000`, `3 00000`,
  `0000 3`, `3 00 3`); a hit moves it one position on, the second and the fourth add one to n, and the fourth
  passes one hit to the rest R of the tape, which becomes G(X R). At the border of R the head crosses in the
  states `>D <F >B <D >D <F` (in at D, out at F, in at B, out at D, in at D, out at F): the same list at all 733
  hits of a first test, so a level does not need to know what R is.
* **An accelerator on levels** (strip a level, count the hits it passes on, as for
  `1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB`, which was decided that way) agrees with the recursion G on 3,000
  wall visits but then stalls: between two levels there are stretches of other digits, and some of them change
  from hit to hit (inner counters with their own fronts, for example `4 0 3 0 0 0 ...`), so they are neither levels
  nor constants. Their hits would have to be simulated one by one with the rest of the tape as a black box.

## Status

* **Lean (kernel)**, `lean/Rules.lean` (written by `py/rules.py`), for every count and every surrounding tape:
  the pair moves `reflect`, `flipX0/1`, `flipY0/1`, `turn0/1`, `digit1`, `digit`; the wall moves `bounce`,
  `cross`; the counter phases `phase1`, `phase2`, `phase4_in`, `phase4_out`; and `pure_tape_halts`.
* **Lean**: `lean/Blank.lean`: the halting configurations; no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* **Trusted**: `py/gmodel.py`: V = G on random words and on the run from blank tape; `py/blocksim.py` /
  `py/bscheck.py` (the earlier exact simulator on runs of `111010`). Direct simulation: no halt
  in 10^13 steps (`c/mrun.c` of the neighbour folder, see above; `tools/c/tmrun.c` to 2·10^10).
* **Trusted**: a closed tape language from windows of 6 cells confines the halt to a head with only 0s on its left
  (`python3 -m bbtools.ctl 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA 6`).
* **Open**: what the right-end events do in general, and so whether a halting word ever appears.

## Next steps

* The carry is a visit of the rest (`R' = G(X R)`), so the whole run is the iteration of one map on words, and the
  levels only set the clock. An accelerator that strips the regular levels was tried (see "Later pass"): it works
  until a stretch between two levels changes from hit to hit. What it needs next: treat such a stretch as a
  small machine of its own, simulated hit by hit with the tape to its right as a black box that answers calls
  (the crossing list `>D <F >B <D >D <F`), and with a table of the stretches seen so far to skip repeats. The
  next right-end event lies beyond 10^13 steps; only such an accelerator will reach it.
* Extend the recursion to the three ways a visit of the rest can come back (F, the regular one; A; D) and to tapes
  with `01` and blank pairs: that is the full macro machine, and the place to look for an invariant or for a halt.
* A mirrored CTL certificate (left and right swapped) would make the confinement a Lean theorem.

## Deep exact run

No halt in the first 6.60x10^17 steps: the macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with blocks of 6 cells ran
from blank tape to step 660,252,048,354,256,421. It is exact, and at this block size it agrees with the
direct simulator after 2,000,019,329 steps (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/deep.py run 240`, then `verify`).

## Dedicated pass: an exact accelerator on digits, through the right-end events

The code is shared by the twins and lives in [`1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/py`](py): `geng.py` (the recursion on digit words with rules found by
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
  about 3n: in the event after wall visit 114, `(1 0)^22` became the digit 69). The word at the next wall visit is
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
wall *and* the step number agree at every wall visit compared, visits 1 to 1,396 (3·10^6 steps) and visits 298,224 to 298,226 (step 100,001,215,143, after the reset): 1,399 visits, through all six early events,
with the outer wall advancing one visit at a time; and again, on the first 3·10^6 steps, with jumps of up to 7, 50
and 1,000 visits. The
recursion rules give the same word and the same step count as the plain recursion on a case that needs 2.3·10^7
recursive calls without them. Not done: an independent re-implementation, and a comparison beyond 10^11 steps
(out of reach of direct simulation), so the long run below is *exact by construction but only as trustworthy as
this one program*.

**The run from blank tape** (`python3 accel_run.py 1 100 100 8`, 45 s; exact numbers in `py/accel_run_1.txt`):

* events follow the wall visits 3, 14, 23, 114, 117, 107,452 (steps 47; 768; 1,729; 23,286; 25,147; 19,979,462,790); the last of these is the reset described above;
* after the reset the fuel `(1 0 0)^13367` (and two smaller runs) is eaten and a ladder grows: 171 levels at wall
  visit 10^100, 1,334 at 10^800, 2,660 at 10^1600. **No event between visit 107,452 and visit 6.354·10^2236**
  (step 6.999·10^4473; both numbers have 2,237 and 4,474 digits);
* the event after that visit is **not a reset**: the 3,713 levels of the ladder survive, the fresh rungs at the
  bottom are turned back into digits and fuel (the word shrinks from 54,438 to 47,140 tokens), and the wall goes
  on;
* the next event follows wall visit 4.233·10^2237 (step 3.105·10^4475). The simulator takes the head to the right end and
  starts back, but then meets a fuel run `(1 0 0)^331,196,833,750,789` under an eater: every 11 hits leave a
  20-digit rung behind, and the engine has no rule that emits such a word, so it would need 10^14 nested calls.
  The run stops there.

So: **no halt up to wall visit 4.233·10^2237, step about 3.105·10^4475**, if the accelerator is right (the earlier exact macro run
reached 6.60·10^17 steps). The halting question stays open: each event is a new chance to produce a halting word, the
events do not stop, and what they leave behind is only known by running them.

**Next steps** (in this order): (1) cycle rules that emit an arbitrary frozen word, not only `1 0` units, with
that word as a run token on the digit side and on the cell side (blocks whose period is not a divisor of 24);
(2) the walk through a run of rungs during an event as a rule (now one nested frame per rung, on cells); (3) the
event itself as a second recursion on digits: the return sweep is a transducer on the open frames, and with it
the whole machine would be one map on digit words, the place to look for an invariant or for a halt.

## Long accelerated run (16 November 2026)

**No halt up to wall visit 4.233·10^2237 (step about 3.105·10^4475). The run is now well inside the return sweep of
the eighth right-end event, past the point where it used to stall.**

*The old stall and the new rules.* During the return of the event, an eater emits the 20-digit rung
`1 0 4 0 0 0 1 0 1 0 4 3 1 0 4 0 3 0 0 0` every 11 hits on `(1 0 0)^331,196,833,750,789`. That would have been
10^14 nested frames. The twin's section describes the fix: frozen words emitted by cycle rules, and nested-frame
rules. `py/geng.py` was changed, and `py/validate_new.py` is new.

*Validation.*

* All 1,399 compared wall visits agree with direct simulation, words and step numbers.
* The eight events of the old run are reproduced digit for digit (visits and steps).
* 400 random cases plus eater and nested cases give the same words and step counts with the new rules as with the
  plain recursion.

*The runs* (`STACKMB=128 python3 py/accel_run.py 1 9000 100`, under `ulimit -v 3000000`):

* The run reaches the eighth event in 38 s.
* In the event's return sweep it gets past the old stall: 42,750 hooks against 23,831 before.
* It then goes on through the return sweep. The second run (2 h 35 min) took the cell runs left of the head from
  18,141 to 14,635, at 43,378 hooks. The first run (1 h) had reached 16,404.
* No halt, no new event and no unknown structure was met on the way.

*Why it is slow.* A sampling profile of the return (`SAMPLE=1`) shows that rule discovery is not the bottleneck:
`discover` and `rdiscover` are not among the top 40 functions. The time goes into visits:

* Each hook hands M = 1 to 9 visits of the 54,000-token word to the engine.
* One such call costs about 200,000 explicit operations and 30,000 rule jumps (about 3 s). Few hits reach each
  level, so few counts are large enough for a rule to pay off.
* The rate fell from about 180 to about 20 runs a minute.

Two overheads were cut: `try_rrule` now computes the shapes and counts of all prefixes once, and `frozen_prefix`
caches its answers. Both changes were validated: 1,399 and 1,422 wall visits agree with direct simulation, the
eight events are identical, and 400 random cases agree with the plain recursion. They gave little speedup.
A lower rule threshold (`THRESH=4`) was slower.

Next steps:

* Defer the visits of consecutive hooks, if the cells between two hooks do not read into the word (not checked
  yet). They could then be applied as one `gpow`, with a snapshot of the left part to roll back to if the batch
  hits an event.
* Or the event return as a transducer on the open frames.

Either would let the run finish this event and look for a halt in the word it leaves.

Trust: computations, exact by construction, validated only as far as direct simulation reaches (about 10^11 steps).
They were not re-derived independently.

## Level-stripping accelerator (22 November 2026)

**From a wall visit straight to the next right-end event.** A carry is a visit of the rest (R' = G(X R)), so the
ladder of levels only sets the clock. `py/lsa_*.py` turns that into arithmetic:

* *Levels as a mixed-radix counter* (`lsa_ladder.py`, `lsa_region.py`). A level is a segment `pre (1 0)^n post`
  with n symbolic and the rest of the word opaque. One hit on it is run symbolically; the states close after a few
  hits, which gives each level a cycle, the hits it passes on per cycle and their positions, and a cost a·n + b.
  The m-th pass of a level comes at its hit p(m − 1) + t, so a chain of levels needs an affine number of hits at
  the top (`first_pass`, proved in `lean/Accel.lean`). The bottom of the ladder is fed with `geng.hpow` in batches.
* *Eater super-cycles* (`lsa_eater.py`). With the fuel m symbolic, P hits on an eater give
  h^P(E[m] X) = Blk E[m − dm] h^c(X), for every X and every m above a small bound. The rest X gets c hits per
  super-cycle and is never looked at.
* *K blocks at once* (`lsa_phase.py`). The block Blk is itself a few levels, with an affine map x ↦ a·x + b. The
  hits that K super-cycles need from above, when the region below must still receive Z hits, are
  I_1 = a^(K−1)(aZ + b) + (aP + b)(a^(K−1) − 1)/(a − 1) (`blocks_closed` in `lean/Accel.lean`, for every K). The
  rest first takes its c·K hits in one `hpow`; if it has no event, the eater's leftover fuel and the new rest are
  the next region (the next *phase*). Counts too large to write down are kept as a mantissa and an exact exponent (`BigF`).

Kinds of eater met so far: ×1024 (on the twin), ×256 (3,633 or 2,283 hits, 27 units of fuel, 5 hits down), ×64 (730 hits, 4 units,
21 down), ×16 (39 hits, 11 units, 1 down), ×1 (11 hits, 6 units, 2 down). A block that is not regular falls back to
plain batches.

*Validation* (`python3 py/lsa_run.py 1 1600 [explicit] [file]`). From the word at the first landing past visit
10^1600 (between the sixth and the seventh event), the accelerator finds the seventh event at exactly wall visit
6.354265240826449…·10^2236 (all 2,237 digits), the visit the digit engine found by running every visit. With the
phase jumps off (`explicit`: only batches of hits) the same visit comes out in 128 s; with 7 nested phase jumps
(×256, ×16, ×1) in 9 s.

*Second pass, the same day.* Four changes, all checked against the old results:

* *Only the head of the word is read.* Each batch used to turn the whole bottom word into tokens and back (about
  200,000 tokens for the twin); now a region segments and inspects only a prefix and shares the rest of the list.
  A phase of the twin went from about 10 s to 2 s.
* *Cached transitions* (`fast_next` in `lsa_phase.py`). After a phase the word is the eater with its leftover fuel,
  then the rest. The way to the next phase reads only the rest up to the next big fuel F. It is computed once with
  everything after F opaque (a token that only counts the r hits it receives), for six values of F with the same
  residue mod 4 (F + 0, 4, 8, 12, 44, 4000), and is used only if all six agree with just F's count moving. The
  real tail then gets its r hits in one `hpow`. Anything else (the opaque part read, an event in the
  transition, a mismatch) takes the plain step. On the twin's first 700 phases the cached run and the plain run
  give the same 701st phase and the same total (exponent exact, mantissa to 15 digits). It runs at about 5 phases a
  second instead of one every 2 s.
* *Counts too large to write down* are now a float mantissa with an exact integer exponent (`BigF`), instead of
  sums c·2^e that grew with every phase. With the exact limit forced down to 1,000 bits, the seventh event comes
  out as 2^7430·1.413…, which is the exact visit to 16 digits.
* *A bug fixed in events below an eater:* one hit of the eater can pass several hits down, and the positions of
  the passes inside a super-cycle counted it once. This only mattered when an event falls inside a phase.

*The ×64 kind against plain batches* (`KMIN` raised so that no phase is jumped). Words cut from the twin's descent
(80 tokens, fuels set to 150 to 3,149, the first 45 or 70 tokens of the twin's word at visit 10^3200 appended as a
ladder) end in an event inside a ×64 phase of 107 super-cycles, after about 1.5·10^157 or 7.9·10^68 top hits. In
all 6 cases the event comes at the same top hit with and without the jump. Words of 200 tokens (no phase) agree
too.

*The return sweep of the eighth event.* A hook that hands the engine's visits of the whole word to the ladder
(`gpow` through a region) gave the same words and steps where it was sampled, but no real speedup in the return
sweep (18,135 to 15,799 runs of cells left in 2 h), so it is not part of this change. The eighth event's return is
still open.

Trust: computations, exact by construction; the accelerator agrees with the digit engine on the stretch it was
compared on. The Lean file covers the arithmetic only, not the symbolic runs that supply its constants.

## Pages

- [`pages/holdouts/1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/explainer.html`](../../pages/holdouts/1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/explainer.html)
- [`pages/holdouts/1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/proof-status.html`](../../pages/holdouts/1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/lean/check.sh
cd holdouts/1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/py && python3 rules.py > ../lean/Rules.lean   # regenerate the Lean rules
python3 gmodel.py 3000000                                      # the recursion against the machine
gcc -O2 -o tmrun ../../../tools/c/tmrun.c && TMRUN=./tmrun python3 bscheck.py 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA 111010 F L 2000000
cd ../../../tools/py && python3 -m bbtools.ctl 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA 6
gcc -O2 -o wv ../c/wv.c && ./wv 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA 3e6 0 1 > ref.txt && python3 ./accel_check.py 1 ref.txt   # accelerator against direct simulation
python3 ./calibrate.py 1 && python3 ./accel_run.py 1 100 100 8                 # step constants; the accelerated run
python3 ./lsa_run.py 1 1600                                     # level-stripping accelerator: the seventh event in seconds
LSA_CKPT=ck.pkl python3 ./lsa_run.py 2 3200                     # the twin from visit 10^3200 (checkpoints in ck.pkl, resumes from it)
```
