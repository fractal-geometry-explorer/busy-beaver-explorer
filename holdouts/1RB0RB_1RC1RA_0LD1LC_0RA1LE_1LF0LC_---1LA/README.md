# 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA

bbchallenge id 25821. A six-state holdout of BB(6), sixth of the family of six starting `1RB0RB` (holdout indices
31–36). **Open.** The tape is a row of blocks of 1s separated by single 0s. At the right end a block of
words `111110` grows by two cells per round trip of the head. Left of it lies a *zone* of about a hundred cells that
every round trip rewrites: a pass coming from the right end cuts each block of three or more 1s in two and stops at
the first block of length 1. How deep the passes reach behaves like a counter, deeper passes being rarer and rarer.
The machine can halt only when a pass gets through everything and meets a block of length 1 at the very left end
of the tape. No halt in 3.3·10^11 steps. A pass reached the left end for the first time since step 5,043 near step
3.3·10^11; it did not halt. It left 134,619 pairs `10 1110` behind, which passes cannot cross, and a new zone started
at the right end.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 1RC | 1RA |
| C | 0LD | 1LC |
| D | 0RA | 1LE |
| E | 1LF | 0LC |
| F | --- | 1LA |

Relatives: `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA` (50378), `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA` (73071)
and `1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB` (117020, states renamed) have the same right sweep, the same pass and
the same block of `111110` words; the first two differ from each other in one transition, the third is the second with
its states renamed and another start state, and all three have another table for the pass (it stands on separators in
state D or E, here in state C).
They are different machines and separate halting questions. Machines 31 to 33 of the family share `A = 1RB 0RB` and
the plan "a pass from the right end that stops at a block of a certain kind; a halt only at the leftmost block", with
other passes.

## What it does

**Where it can halt** (a hand argument from the table). The only halting transition is F on 0. F is entered only from
E on 0, E only from D on 1 and D only from C on 0, all moving left, so a halt is exactly `0 0 1 C> 0`: the pass on a
separator, a block of length 1 left of it, and two 0s left of that.
Lean proves that this pattern halts (`halt_pass`, three steps). At all the snapshots below the 0s inside the tape
are single (observed, not proved; two 0s were seen only at the two ends of the tape), so the pattern can only form
at the left end: **a pass must reach the leftmost block while that block has length 1.**

**The pass** (`lean/Rules.lean`, all lengths, any surrounding tape). The pass moves left in state C from
separator to separator.

| left of the separator | what happens | theorem |
|---|---|---|
| a block of length k+3 | it is cut into k+1 and 1, the pass goes on | `pass_split` |
| a block of length 1, a 1 two cells further left | the separator left of the block is filled, F turns the head around | `pass_stop` |
| a block of length 1, then `0 0` | F reads 0: **halt** | `halt_pass` |

At the snapshots every block is odd except the leftmost one and the unfinished word at the right end, so the
pass does not meet a block of length 2.

**The block of words.** The pass crosses n words `111110` in 6n steps, turning each into `1110 10` and staying in
state C (`cross_left`); the sweep back in state A turns them into `111110` again, read one cell later
(`cross_right`). Both are proved for every n and every surrounding tape, so *these two crossings* do not depend on
the length of the block. Call a *trigger* a step at which the head visits a new cell on the right in state
C; the tape is then `REST (111110)^n 11111` with the head right of it, and the block gains a word
every three triggers.

**Arrivals at the left end** (real machine, `c/reduced.c` with nothing cut). The left end of the tape moves only
when a pass crosses the whole zone:

| trigger | step of the last new cell | what was seen |
|---|---|---|
| 1, 2, 3, 6, 27 | 13 to 1,464 | the tape is still short |
| 51 | 5,043 | five new cells; the zone goes on beside the left end |
| 403,962 | between 3.25·10^11 and 3.30·10^11 | five new cells; the sweep back leaves the 134,619 words of the block as `1110 10` instead of restoring them, and **a new zone and a new block of `111110` words start at the right end** |

The arrival at trigger 403,962 was predicted by the reduced system and by the zone run alone (below) before the real
machine got there; the blocks at the left end afterwards are the predicted ones. Since then the tape is `W (10 1110)^a
Z (111110)^n`: the old zone `W`, the stranded block, a new zone `Z` and the new growing block. The stranded block is
made of blocks of lengths 1 and 3, and a block of length 1 stops a pass (`pass_stop`): the passes of the new zone
cannot cross it, they can only use it up from the right. The same thing is seen at the start of the run, where a block
`(1 3)^9` left of the zone at step 10^4 is gone at step 6·10^7. At steps 3.3·10^11 to 3.5·10^11 the stranded block
still has all its 134,619 pairs and `W` has not changed: `W` is shielded until the block is used up.

Block lengths at some triggers (`c/snap.c`; `(5)^n` is n words, the first number of each line is the step):

    1,000,595        4 3 1 1 3 3 5 1 5 (1 3)^5 3 3 (1)^4 3 9 3 (1)^3 5 5 1 7 (5)^232 4
    1,000,058,399    4 3 1 1 3 3 5 (1)^3 3 1 (3)^3 5 3 1 3 (1)^5 5 3 1 3 1 3 7 7 (1)^3 3 (5)^7451 4
    325,000,618,367  4 5 7 5 (3)^4 5 7 3 3 5 1 3 1 3 3 1 3 9 (1)^3 3 5 1 7 (5)^134368 4
    330,000,028,864  2 1 1 5 5 3 7 3 1 3 5 7 3 1 3 3 1 5 1 3 (1)^3 3 1 1 5 1 1 3 9 1 5 (1 3)^134619 3 3 1 5 (1)^4 5 5 1 7 5 1 3 1 (1 3)^4 (1)^3 3 9 1 (5)^14336 4

**The reduced system** (`c/reduced.c`). Because the two crossings do not depend on n, one expects that deleting
words from the block at a trigger does not change what happens to `REST`. This is *not proved*: a round trip
consists of several partial passes, and nothing here excludes other ways of entering the block. It was checked by
running the real machine next to the reduced one for 20,000 triggers (`resetsim ... check`, from the folder of
`1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC`): (796,191,914 steps) the runs agree at every trigger except the arrival
of trigger 51, where `REST` differs (123 cells against 99). With the block cut to 10 words at every trigger
a trigger costs about 150 steps instead of a walk over the whole tape, and the reduced run goes far beyond the
real one:

| reduced run | result |
|---|---|
| started from the real configuration of trigger 1,000 |  |
| deepest pass, cells from the left end of the tape | 95 (trigger 1,003), 71 (1,039), 57 (1,807), 45 (4,963), 33 (9,163), 27 (38,395), 9 (40,975) |
| trigger 403,962 | arrival at the left end, five new cells, no halt (the real machine does the same) |

The real machine reached trigger 403,962 near step 3.3·10^11. Beyond this arrival the reduced run says nothing about
the machine: it strands a block of 10 pairs where the real machine strands 134,619, and that block is used up, not
crossed, so its length matters. (In the reduced run the 10 pairs are soon gone and a pass reaches the left end again
at trigger 509,436,585, without a halt.)

**The zone alone** (`c/zone.c`). The leftmost zone can be run by itself: `REST` followed by twelve words, a pass
arriving on the last separator, until the head leaves on the right; the cells left of the words are the next `REST`.
Started from the real `REST` of trigger 100, this model reaches the left end in its tick 403,863, which is trigger
403,962, and the head then sweeps back in another phase, leaving the words as `1110 10`: what the real machine does.
The model stops there, because its tape has only twelve words and the head is not back in the usual state at their
end.

## Status

Open. Proved in Lean (kernel): the halting pattern, the pass over a block and its stop, the two crossings of the
block of words. Observed, not proved: that 0s inside the tape are single (so that a halt needs the left end), that
the reduced system follows the real machine, and everything in the tables and snapshots above. Nothing is known that
keeps the
leftmost block from being a lone 1 when a pass arrives, and nothing that forces it.

## What is proved

| result | level | where |
|---|---|---|
| halts exactly when F reads 0 | kernel | `step_none_iff`, `lean/Blank.lean` |
| no halt in 10^4 / 10^7 steps | kernel / native | `blank_runs_kernel`, `blank_runs_native` |
| the halting pattern `0 0 1 C> 0` | kernel | `halt_pass`, `lean/Rules.lean` |
| the pass over a block and its stop, all lengths, any context | kernel | `pass_split`, `pass_stop`; generated by `py/gen_rules.py` |
| the crossings of `(111110)^n`, all n, any context | kernel | `cross_left`, `cross_right` |
| no halt in 3.3·10^11 steps; the arrivals at the left end and the stranded block | trusted | `c/snap.c`, `c/reduced.c` |
| the reduced system: the arrival at the left end at trigger 403,962, before the real machine got there | observed (rests on the unproved reduction) | `c/reduced.c` |
| the leftmost zone alone: reaches the left end at trigger 403,962 and leaves the blocks seen in the real tape | a model, checked at the real arrivals | `c/zone.c` |

## For later

* Prove the reduction: that every entry of the head into the block of words between two triggers is one of the two
  proved crossings. With that, a halt of the reduced system would be a halt of the machine, and a cycle of the
  reduced system a proof that it never halts.
* Prove that the 0s inside the tape stay single.
* The zone as a counter: a law for the depth of the passes and for what an arrival at the left end does to the
  leftmost blocks.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA/lean/check.sh
gcc -O2 -o snap holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/snap.c && ./snap 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA 1e6 1e9
gcc -O2 -o reduced holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/reduced.c
./reduced 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA C 11111 10 12000 1e18        # the real machine: arrivals at the left end
./reduced 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA C 11111 10 6e8 1000    # the reduced system
gcc -O2 -o zone holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/zone.c && ./zone 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA C C 11111 100 1e6 quiet    # the zone alone
```

## Pages

- [`pages/holdouts/1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA/explainer.html`](../../pages/holdouts/1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA/explainer.html)
- [`pages/holdouts/1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA/proof-status.html`](../../pages/holdouts/1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA/proof-status.html)
