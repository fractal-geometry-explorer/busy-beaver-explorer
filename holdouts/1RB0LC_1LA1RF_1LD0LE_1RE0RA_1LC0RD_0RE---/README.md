# 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---

bbchallenge id 71372. A hierarchy of frozen segments (10)^a 11 (01)^b whose sizes grow level by level (43, 403, 893, …); the active end eats the last run of pairs 01 at a steady rate, 400 pairs per sample, and turns it into a growing reservoir of the word 1010101 at the far left.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 1RF |
| C | 1LD | 0LE |
| D | 1RE | 0RA |
| E | 1LC | 0RD |
| F | 0RE | --- |

## What it does

The tape at step 987,150,465 (66,000 cells):

    C> (01)^4 (1010101)^6123 (01)^7 [(10)^11 11 (01)^43] x9 (10)^11 11 (01)^86
       [(10)^83 11 (01)^403] x6 (10)^83 11 (01)^187 (10)^162 11 (01)^893 (10)^565 11 (01)^893
       (10)^565 11 (01)^1162 (10)^6 11 (01)^3523

The middle is frozen: identical at steps 8.39e8, 9.11e8, 9.87e8. Only the reservoir r (5323, 5723, 6123) and the
last run m (4323, 3923, 3523) change, by 400 per sample, and the tape grows 2000 cells to the left (heuristic).
Segment sizes grow by level (43, 403, ~900): nested levels, each presumably built when a drain runs out. The head
crosses runs of pairs in one go (`lean/Rules.lean`, four rules, kernel).

## Status

Open. Kernel: halting configurations, no halt in 10^4 steps (10^7 native), the four crossing rules, the walk of the
reflector Q (`lean/Walk.lean`), and the movers: the head crosses any run of them unchanged, so every bounce of a drain
or a rebuild is a lemma except where the head turns (`lean/Movers.lean`). On these lemmas an exact simulator reaches
1.5·10^18 steps without a halt (below). Halting needs F to read a 1, which happens only as `D> 1 0 1 1`, and only a
collision run cell by cell could do that. Every collision at the ends of the movers seen to 1.6·10^18 steps is a lemma
for all values of its gaps (`lean/Collisions.lean`, `lean/ZList.lean`); none halts. No regular invariant was found: CTL
by SAT up to 16×16 and 20×12 states, NGramCPS (widths 2-14, -H, -U) and RepWL fail.

## For later

1. Prove the drain step (one pair per round trip) as a rule with r and m as variables.
2. Done 22 November: the end of a drain starts a rebuild (see below).
3. Partly done 22 November: the movers are proved (`lean/Movers.lean`), the simulator on them is exact, and every
   collision at the ends of the movers seen to 1.6·10^18 is a lemma with its gaps as variables (`lean/Collisions.lean`).
   Still to do: an invariant, in terms of movers, that shows no other collision ever happens; in particular that a
   gap of one pair is never followed by another swept mover at the right end. A first abstract search for one
   (23 November, below) does not close, nor does one on blocks of movers; in block terms a rebuild maps each gap
   `g` to `3g`, `3g + 4` or `3g + 8` by a three-state transducer, with a rule for drain ends (observed on every
   consecutive transfer checked), with rules for drain ends and nesting; still to do: un-nesting (15 times to
   1.88·10^12 steps), and one composed theorem from `walkm` and the collisions at the ends of a gap.

## Reproduce

```sh
./tmrun 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 1000000000 records 100000000 | awk 'NR%2000==0' | tail -3
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/lean/check.sh
```

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 7.30x10^14 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.75x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 1,080 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 400
```

## When the last run is used up (22 November 2026)

**Short answer.** A rebuild, not a halt, every time it has been watched: 5 drain ends in direct simulation (to
2.2·10^9 steps) and 3 more in the accelerated run (to 6.0·10^14). The rebuild is a particle system, decoded below.
Whether some rebuild can end in a halt is still open.

**The tape as a list.** Read from the left, the tape is `(10)^3` blocks (the reservoir, the words `1010101`) and
then a list of blocks `(10)^n` separated by single `1`s, `10, n_2, n_3, ..., m`. In the drain each round trip moves one
pair from the last block `m` to the reservoir. When `m` reaches 1, the next trip does not come back to the left end.

**What follows: a reflector walks left and triples what it passes.** The head now bounces between the right end of
the tape and a reflector `Q`, one extra cell in a background of pairs (`L (01)^c 0 (01)^a E>` or the same with an
extra `1`):

* one bounce moves Q two cells left and the right end two cells right (`lean/Walk.lean`: `bounce0`, `bounce1`,
  `bounce2`, and `walk` for k double bounces, kernel);
* when Q passes a separator of the list (`001100` in the phase the head leaves there), the separator turns into a
  *mover* `11` that the head carries four cells to the right on every bounce (observed);
* so stuff Q has passed moves away from it at 4 cells per bounce while Q moves 2: the part of the list Q passes comes
  out stretched three times. Block by block, `n` becomes `3n` (n even) or `3n - 4`, `3n + 4` (n odd, alternating),
  for example `(11 43)` becomes `(29 133)` and then `(83 403)`, and the reservoir's `3`s become `(5 13)` or `(19 35)`;
* the walk ends when the first mover reaches the right end (which grows only 2 cells per bounce): on the next
  bounce Q is left behind as a *scar*, a stationary `00` or `11`, and a new Q starts near the right end;
* a later Q passes a `00` scar (it becomes a mover) and stops at a `11` scar. In the event at 1.4·10^8 the walks
  stop at 10631, 15634 and again at 10631; in the event at 1.79·10^9 at 54482, 54321 and again at 54321.

When the walks are over the head runs back to the left end and the next drain starts with a new last block.
`c/sweeps.c` prints the turning points of the head; during a rebuild its left turns are the positions of Q.
`c/parts.c` prints, at those times, where the tape has `00` or `11`: these are exactly the particles.

**Three kinds of rebuild have been seen.**

| drain ends at step | last blocks before | after | source |
|---|---|---|---|
| 9,061 | `5 5 6 1` | `16 11 6 111` | direct |
| 272,814 | `16 11 6 1`, reservoir 128 | `10 (11 43)^16 11 19 18 (101 61)^2 130 541 269 821 2335`, reservoir 83 | direct |
| 142,359,375 | `... 130 541 269 821 1` | `... (11 43)^9 11 86 (83 403)^6 83 187 162 (893 565)^2 1162 6 7228` | direct |
| 1,793,526,413 | `... (893 565)^2 1162 6 1` | `... (893 565)^2 1552` | direct |
| 2,230,168,743 | whole list, reservoir 11,198 | `10 (5 13)^388 5 37 (19 35)^5209 19 90 (107 379)^9 107 774 739 24448 6659 5707 81162 (19709 98389)^2 19709 158069 468864`, reservoir about 0, at 1.79·10^12 | accelerated |
| 6.48·10^12 | `... 81162 (19709 98389)^2 19709 158069 1` | `... 5707 563005 177397 4764477 4737114`, at 1.26·10^14 | accelerated |
| 6.05·10^14 | `... 563005 177397 4764477 1`, reservoir 5,205,977 | a rebuild that reaches back to `(107 379)^9`; not finished at 7.3·10^14 | accelerated |

A *short* rebuild only touches the last few blocks (1.79·10^9: `1162 6 1` becomes `1552` in 562,000 steps). A
*partial* one re-makes the right part of the list (1.4·10^8 and 6.5·10^12). A *full* one reaches the left end and
turns the reservoir itself into blocks, so a new reservoir starts from nothing (2.7·10^5 partly, 2.2·10^9
completely: 11,198 copies of `3` became `(5 13)^388 5 37 (19 35)^5209`). So the "frozen levels" of the 13 November
picture are made by rebuilds: each block value is a reservoir `3` or an older block tripled a number of times.

**Where a halt could come from.** The machine halts only when F reads a 1. B is entered only from A reading 0
(moving right, writing 1), so B reading 0 goes back onto that 1; F is therefore entered only through `A>0 1 x`, and
the machine halts exactly when `x = 1`. A is entered from B (onto the 1 just written) or from D reading 1, and D
from C (which writes the 1 the next A reads) or from E reading 1. So **every halt is the head in D, moving right,
on `1 0 1 1`**: a block of a single pair `01` between two extra `1`s, crossed by D. In 3·10^9 steps F is entered
63,295,957 times, always on a 0, in 22 different 17-cell windows (`c/fwatch.c`). The drains never meet this word;
the place to look is the rebuilds, where the last run is down to one pair and Q, scars and movers sit close together.

**Open.** An exact list-to-list map for a rebuild (the offsets where Q is born and where scars sit are not yet
written down as rules), and with it a proof that no rebuild produces `D> 1 0 1 1`. The Lean walk theorem covers Q
in a clean background; the collisions with separators, movers and scars are only observed. The accelerated rows of
the table rest on `rsim`'s jumps (not proved); in the middle of the long rebuild, at step 107,877,479,194, rsim's
tape and state equal those of a plain C simulator (822,161 cells; `rsim ... dump 1e11` against a direct run).

```sh
gcc -O2 -o blkev holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/c/blkev.c && ./blkev 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 3000000000 | grep -v mon
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/rsim_events.py 2e14 > ev.txt && python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/drain_ends.py ev.txt
gcc -O2 -o sweeps holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/c/sweeps.c && ./sweeps 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 142000000 407100000 200
gcc -O2 -o parts holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/c/parts.c && ./parts 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- $(./sweeps 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 1793600000 1793910000 40 | awk '$4=="min"{print $1}' | paste -sd,) 54200
gcc -O2 -o fwatch holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/c/fwatch.c && ./fwatch 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 3000000000
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/gen_walk.py     # writes lean/WalkRules.lean
```

## Movers: an exact simulator to 1.5·10^18 steps (22 November 2026)

**Short answer.** The rebuilds are now simulated exactly, not just watched: every bounce is a Lean lemma except the
few cells where something collides, and those cells are run one machine step at a time. From step 273,791 this
reaches 1.57·10^18 steps in five minutes without a halt, through the drain ends at 6.5·10^12 and 6.0·10^14. Its tape
equals that of the accelerated run above at 1.0·10^12 and 7.0·10^14 steps (57,654,285 cells), so its unproved jumps
were right that far. The rebuild that starts at 6.0·10^14 has not finished at 1.57·10^18. Whether a later collision
can halt is still open.

**Everything is a mover.** Read at a right-end turn (head in E on the blank), the tape is

    Y | movers g_k ... g_1 | E>        a mover at rest = 0 0 1 1 0 (01)^g   (g pairs of gap on its right)

The separators of the list, the separators Q has passed, and the reservoir's words (`g = 1`) are all movers; only
Q, the scars and the few cells at the left end are not. `lean/Movers.lean` (kernel):

* `left_all`: the left sweep, in state E on a 0, crosses any movers (gaps of at least one pair) and comes out on
  their left in state E on a 0;
* `right_gen`: the right sweep crosses them all again and comes out in state D, every mover four cells further
  right. After a one-pair gap it runs in state F for a while (`rm1`, `fm1`, `fm`), which changes only the first cell
  it writes;
* `bounce_gen`: so **any** bounce is the same, whatever happens left of the movers, as long as the head, sent in
  from the right in state E on a 0, comes back out in state D or F without looking right. The gaps between movers
  stay the same and the last gap shrinks by one pair;
* `bounce0m`, `bounce1m`, `walkm`: with Q on the left, Q's walk with movers in closed form (Q's gap grows by
  three pairs per bounce).

In a drain the same lemmas apply with the left end of the tape in place of Q: the whole list and the reservoir move
four cells right per trip while the left end grows by one word. So the drains and the rebuilds are one system,
and a bounce needs work only where the head turns: at Q (or the left end) and at the right end when the last gap
is under two pairs.

**The simulator.** `py/mover_sim.py` keeps the tape as `Y | movers | Z` (runs of pairs as counts, movers as a list
of gaps) and moves it a bounce at a time: k bounces at once by `walk` or `walkm` when Q is in a clean background;
`bounce_gen` when only the left end of the bounce is unusual (that end run cell by cell); and all cells one step at a
time otherwise, crossing runs of pairs with the four rules of `lean/Rules.lean`. Its only unproved part is its own
bookkeeping. Checked against direct simulation (`c/dump.c`), the whole tape and state are equal after 20,000
bounces (step 438,724,239) and after 203,633 bounces (step 29,361,299,373, 441,628 cells, past four drain ends).
Checked against the accelerated simulator `rsim` (`rsim MACHINE dump T`), the tapes are equal at steps
1,008,073,404,791 (2,227,034 cells) and 695,788,802,905,521 (57,654,285 cells, inside the rebuild that converts the
reservoir of 5.2 million words). To 10^15 it makes 25.8 million bounces: 18.0 million inside 1.3 million jumps, 7.8 million with a collision run
cell by cell, and 5.7 million times it opens up the rightmost mover to run it cell by cell. To 1.57·10^18 it makes
1.57 billion bounces, nearly all inside 3.8 million jumps: after 1.6·10^15 the rebuild is a long series of walks,
each Q walking left across the clean stretch the walk before it left behind, and passing a few movers.

| drain end (last gap down to one pair) at step | reservoir | list |
|---|---|---|
| 142,241,195 | 2,415 | `10 (11 43)^16 11 19 18 (101 61)^2 130 541 269 821 1` |
| 1,793,081,823 | 9,643 | `... (893 565)^2 1162 6 1` |
| 2,229,667,575 | 11,195 | `... (893 565)^2 1` |
| 6,481,607,828,757 | 468,863 | `10 (5 13)^388 5 37 (19 35)^5209 19 90 (107 379)^9 107 774 739 24448 6659 5707 81162 (19709 98389)^2 19709 158069 1` |
| 604,987,560,783,867 | 5,205,978 | `... 5707 563005 177397 4764477 1` |

(The steps differ from the table above by part of a round trip: there a drain end is the last left-end record,
here the right-end turn where the last gap reaches one pair.)

**Where a halt could still come from.** Inside the lemmas F always reads the first cell of a gap or the 0 that
starts the next mover, so the lemmas never halt. A halt can only come from a collision run cell by cell. To 10^13
steps there are 57 different such runs, all made of the same few pieces: the left sweep crossing a gap (`E0 <`) or
a mover (`C0 D1 A1 C0 D1 A1 C0 D0 ~ E0 <`), the right sweep passing a mover (`E1 D1 A0 B1 F0 ~`) or turning at
one (`E1 D1 A0 B0 A1 C0 D0 ~`, `D1 A1`), and the turns at Q and at the ends. In every one F reads a 0. What is left
is to show that no future collision is different: either an invariant of the lists, or a proof of each collision
family with its gaps as variables.

```sh
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/mover_sim.py check 203633   # compares with c/dump.c
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/mover_sim.py run 1.5e18     # drain ends, no halt (5 min)
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/gen_movers.py              # writes lean/MoverRules.lean
```

## Collisions with their gaps as variables (22 November 2026)

**Short answer.** Every collision the exact simulator runs cell by cell at the ends of the movers, up to 1.6·10^18
steps, is now a Lean lemma for every value of its gaps (`lean/Collisions.lean`, `lean/ZList.lean`, kernel). None of
them can halt, whatever the gaps. What stays open is whether a collision of another shape ever halts, and new shapes
do still turn up: two of the 20 first appear after 10^15 steps. The search for a regular invariant of the whole tape,
which would settle that, found none.

**How the lemmas are made.** `py/gen_collisions.py` runs `mover_sim.py` and groups the runs it makes cell by cell by
the (state, symbol) pairs they read. Up to 1.6·10^18 steps there are 46 families at the ends of the movers ("Z": the
right end, after the last mover is opened up; "macro": the left end of a bounce, at Q or at the left end of the
tape) and 43 whole-tape runs ("plain", 130 runs, made when no mover lies between the two places where the head
turns). For each of the 46 the first occurrence becomes a symbolic configuration: every run of pairs becomes
`(01)^(a+k)` with its own variable (`k` the least count the run needs), and whatever the run never reads becomes a
context. `bbtools.symtm` runs it to the end of the collision and writes the proof. They come down to 20 distinct
lemmas, for example

    0^inf 1 E> 0 R                                  ->  0^inf 1 0 0 1 1 F> R       (9 steps; 5,217,085 times)
    L 0 (01)^(a+1) 1 0 0 (01)^(b+2) E> 0 R          ->  L 0 (01)^(a+1) 1 1 0 0 1 1 0 (01)^b 0 D> R
    L 0 (01)^1 1 0 (01)^a 0 C> 1 (10)^(b+1) 1 (10)^(c+1) R
                                                    ->  L E> 0 0 1 0 1 1 0 (10)^a (10)^(b+1) 1 (10)^(c+1) R

The first is a drain trip turning at the left end of the tape: F comes out reading the first cell of the movers,
which is a 0 (`right_gen`). At the right end a collision can sweep back over any number of swept movers
`1 (10)^(g+2)`, then a last one `1 (10)^1` and blank tape; the lemmas stop at the second one, and `zlist` and `zend`
(`lean/ZList.lean`) take any list: each swept mover becomes a mover at rest. Here is the one place a halt was close:
on a swept mover with a gap of one pair the head reads `E1 D1 A0 B1` and F reads the next cell, which is the blank
only because that mover is the last. A gap of one pair anywhere else in that list would halt. In every list seen,
the gaps before the last are at least two pairs (three or more, in fact).

One family is left out: a run, once, at step 32,044,261, that crosses about 85 movers stored as cells, more than the
simulator's snapshot holds. The whole-tape runs are not generalised either.

**No regular invariant found.** A closed tape language would settle the question, and none was found:

* `tools/py/satctl.py` (two automata found by SAT, CaDiCaL): none with 6×6, 8×8, 10×10, 12×12, 16×16 or 20×12 states
  (16×16 took 32 minutes);
* NGramCPS (`tools/c/ngramcps.c`) with windows of 10, 12 and 14 cells: it reaches a halt in under 300 steps; the
  first step that leaves the real run glues a 1 onto its left window where the real tape is blank;
* RepWL (`tools/c/repwl.cpp`): it reaches a halt with blocks of 2 cells, and passes 2 million abstract
  configurations with blocks of 4 to 12;
* `c/runcps.cpp`, the same idea with runs of alternating cells as letters: it fails the same way, by gluing the end
  of the tape in where it is not, and with counts of the runs to each end it does not close (90 million
  configurations).

The reason is the same in each: the left end of the tape matters (drain trips turn there), and a window of cells or
runs forgets how far away it is. An invariant would have to be written in terms of movers.

```sh
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/gen_collisions.py 1.6e18 # writes lean/Collisions.lean (20 min)
holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/lean/check.sh                       # ALL CHECKED
```

## Toward an invariant in terms of movers (23 November 2026)

**Short answer.** Not found yet. Two things were measured, and a first abstract search in terms of movers was
built; it does not close.

**What the moving list looks like.** Sampled every 50 bounces to 1.06·10^13 steps (`py/gap_patterns.py`), the gaps
of the movers the head crosses, after the rightmost one, are always some gaps of three pairs or more followed by
some gaps of one pair (the reservoir's words, at the far end). A gap of two pairs, or a one-pair gap before a
longer one, never occurs. At every bounce where the rightmost gap is under two pairs, the next gap is 3, 4 or more.
So the one-pair gaps only reach the right end when everything in front of them is gone. When that happens
(1.4·10^8 steps, the reservoir of the drain that ends there) they are opened up one after another inside one
bounce, and no halt follows.

**An abstract search** (`py/mover_cps.py`). It runs `mover_sim.py`'s bounce on an abstract state:
* runs of pairs are capped at 6;
* the moving list and each block of movers at rest are queues with a few explicit gaps at each end and a middle
  taken from a learned graph of adjacent gaps;
* the static part of the tape below its top 12 items is a path in a learned graph of adjacent items;
* a block of movers at rest is crossed in one step by `left_all` and `right_gen` when the head meets it in E on
  a 0 (or comes back in D or F).

It fails, started at 4.2·10^9 steps, after about 2,000 states. One state leaves only `0 1 1 0 4` above the static
part, and the run that follows walks into it without end: the head crosses the movers of a block one cell at a
time, in states where `left_all` does not apply, and the abstract block can be as long as it likes. This is the
same loss as in the tape-level searches: the abstraction forgets how far the next turning point is. A version that
can close needs the static part written as mover-level items whose crossings are lemmas in every state the head
can meet them in, not only E on a 0.

```sh
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/gap_patterns.py 1e13    # gap patterns (10 min)
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/mover_cps.py 3e9        # FAIL after ~2,000 states
```

## Blocks of movers as items; the rebuild's tripling, gap by gap (23 November 2026)

**Short answer.** The tape is now a short stack of items (single cells, runs of pairs, and *blocks* of movers at rest,
each a list of gaps), and the head crosses a block in one step by a Lean lemma in every state it was seen to meet
one in (`py/block_sim.py`, `lean/BlockTail.lean`). On this stack the whole tape never has more than 21 items to
1.88·10^12 steps. In these terms a rebuild copies the gaps of one block into the next by a three-state transducer (`3g`,
`3g + 4` or `3g + 8`), with exact rules for a drain end in the middle of a gap and for nesting one level deeper; they hold on
every consecutive transfer checked to 1.88·10^12 steps. This is a step toward the list-to-list map for a rebuild
that is still open above: what is left is un-nesting, when an inner level's list runs out. A finite abstraction of the stack
does not close.

**The one-stack simulator.** At each right-end turn the tape is a stack; a bounce runs on it with these hooks:

* `left_all` (head in E on a 0 with a block on its left) and `right_gen` (head in D or F with the swept block on its
  right), as in `lean/Movers.lean`;
* a swept block that *ends* with one-pair gaps (the reservoir's words): the head crosses `k + 1` of them in
  `7(k+1)` steps and comes out in state F, leaving `1 1 0 0`, then `k` movers with one-pair gaps, then `1 0 p`
  (`tail_D`, `tail_F`, `ones_D_movers`, `ones_F_movers`, new; `p` is 1 from D, 0 from F);
* a swept block met in another state (seen once, in A) is opened from its far end, `W g` as cells (the definition
  of `swL`); pairs pushed onto a block join its first gap (`mv_pairs`).

Everything else runs cell by cell. `block_sim.py check` compares the tape with direct simulation: equal after 400,000
bounces (1.1·10^11 steps).

**Drains and rebuilds as blocks.** The leftmost block is some long gaps, then the reservoir (one-pair gaps). In a
rebuild the top of the stack is `… M[g …] X n M[f …]` (`X` a single cell, `n` pairs: Q and the gap between Q and the
first mover): each bounce takes one pair from `g`, flips `X`, adds three pairs to `n` and takes one from `f`
(`walkm` is two of these). When `g` runs out, `n` becomes a new gap at the far end of the right block and the next
gap of the left block starts; when `f` runs out, the activity moves one block to the right. The new gaps follow a
small transducer. A gap's transfer starts with `0 n0` above it: `n0 = 4` with the gap whole (S1), `n0 = 3` with one
pair already taken (S0), or `n0 = 2` after a drain end (S2). Each bounce adds three pairs to the run and flips `X`; if
the fuel `f` (the right block's first gap) outlasts the gap, the run joins the right block with three more pairs if
`X` is a 1 at the end, seven if it is a 0:

| state | g even | g odd |
|---|---|---|
| S1 | `3g + 4`, stay in S1 | `3g + 8`, go to S0 |
| S0 | `3g + 4`, stay in S0 | `3g`, go to S1 |
| S2 | `3g + 2`, go to S1 | `3g + 6`, go to S0 |

So an even gap gives `3g + 4`, and odd gaps give `3g + 8` and `3g` by turns (539 → 1617, 128 → 388, 59 → 185,
99 → 297, 9 → 27, 41 → 131; the reservoir's `1^n` becomes `(3 11)^n`). If the fuel is smaller than the gap, it runs
out after `f` bounces with the run at `n_e = n0 + 3f` (a drain end): a drain moves the run to the right end, one pair
in, two pairs out, per bounce, and the transfer starts again on the rest of the gap with new fuel. For even `f` it
starts in S2 with the gap `f + 3` pairs shorter and fuel `2 n_e + 7` (`166` → `339`, `354442` → `708891`); for odd
`f`, in S0 with the gap `f + 2` shorter and fuel `2 n_e + 6`. If the fuel block has more gaps `h, rest…` the rebuild
*nests* instead: the run freezes as an item `X (n_e + 3)` (X a 1 for even `f`), the left gap is left with `g − f − 1`
pairs, `h` becomes the new fuel (`2h` in S1 for odd `h`, `2h + 3` in S0 for even `h`) and `rest` the left block of
a transfer one level deeper (at bounce 10,769: fuel 2 in `M[2 809 1617 …]` gives `1 13 M[1617 388 …] 0 4 M[1618]`).

`block_sim.py rule 1.3e6` checks this on every pair of consecutive starts to 1.88·10^12 steps: 10,627 gaps copied
one at a time, 5,616 times two one-pair gaps at once (too short to show a start of their own), 6 drain ends and 11
nestings, all as predicted; 2 where the fuel ends with the gap (`f = g + 1`, not covered). Not checked: the 15 times
an inner level's left block runs out and its output joins the level above (un-nesting); their shapes vary, and a
rule for them is the missing piece of the rebuild map. The stretch is `walkm` (`lean/Movers.lean`); the two ends of a gap are collisions at Q, most likely the two
frequent families 4 and 5 of `lean/Collisions.lean` (not yet matched). None of this is one composed theorem yet. The
reservoir drains completely at bounce 1,283,663 (step 1.79·10^12, `B 1 M[1] 0 1 1 8 M[11228]`); eight bounces later
the block on the right merges back as one block of 11,232 movers:
`468865 158067 19707 98387 19707 98387 19707 81160 5705 6657 24446 737 772 (105 377)^n 88 (17 33)^n … (3 11)^n 8`
(`block_sim.py cycle`).

`block_sim.py` runs a stretch of a rebuild at once: two bounces are run and checked against the shape above, the
rest applied with the cost `s(t+2) = s(t) + 16` (`n` grows by six pairs, +24 steps; `f` loses two, −8). To 1.3
million bounces it skips 540,118 bounces in 5,399 stretches and gives the same step count as the plain run,
1,880,381,285,307.

**A finite abstraction does not close.** `py/block_search.py` runs the abstract bounce with pair counts capped at K
and each block a queue with explicit ends and a learned middle. With K = 6 there is no halt in 1.76 million abstract
tapes and no closure (it ran out of memory: small exact counts everywhere multiply). With K = 2 or 3 it reaches a
halt, and replaying it shows an artefact of the capping (`K+` plus one pair is `K+`, then minus one pair may be
`K−1`); every concrete version of the last tapes on that path runs on without a halt. Beyond the capping, the
abstraction forgets a correlation: it lets the reservoir be short while the block it feeds is small, but every mover
that leaves the reservoir lands in that block. A proof has to follow the rebuild as arithmetic on gap lists.

```sh
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/block_sim.py check 4e5    # tape equal to direct simulation
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/block_sim.py cycle 1.3e6  # reservoir lows, one-block moments (25 min)
python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/block_sim.py rule 1.3e6   # transducer, drain ends, nestings: all as predicted (15 min)
K=3 python3 holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/py/block_search.py       # FAIL: a capping artefact
holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/lean/check.sh                        # ALL CHECKED
```

## Pages

- [`pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/explainer.html`](../../pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/explainer.html)
- [`pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/proof-status.html`](../../pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---`](../1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---/README.md): rename A→D, B→E, C→B, D→C, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---`](../1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---`](../1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---/README.md): rename A→D, B→E, C→C, D→A, E→B, F→F; it is this table started in state D
- [`1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB`](../1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB/README.md): rename A→B, B→A, C→E, D→F, E→D, F→C and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
