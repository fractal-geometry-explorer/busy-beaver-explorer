# 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA

bbchallenge id 50378. A six-state holdout of BB(6), fourth of the family of six starting `1RB0RB` (holdout indices
31–36). **Open.** The tape is a row of blocks of 1s separated by single 0s. At the right end a block of
words `111110` grows by two cells per round trip of the head. Left of it lies a *zone* of about a hundred cells that
every round trip rewrites: a pass coming from the right end cuts each block of three or more 1s in two and stops at
the first block of length 1. How deep the passes reach behaves like a counter, deeper passes being rarer and rarer.
The machine can halt only when a pass gets through everything and meets a block of length 1 at the very left end
of the tape. No halt in 10^11 steps; the last time a pass reached the left end was step 178,267,564, and since then
the zone has started again further right, leaving a block of about 3,130 words between it and its old cells.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 1LC | 1RA |
| C | 1LF | 0LD |
| D | 0LE | 1LD |
| E | 1LA | 1LC |
| F | --- | 1LA |

Relatives: `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA` (73071), `1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA` (25821)
and `1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB` (117020, states renamed) have the same right sweep, the same pass and
the same block of `111110` words; `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA` differs from this machine only in what E
does on a 0 (`1LA` here, `1RA` there), a transition used only where two 0s stand side by side, which at the snapshots
means at the left end of the tape. The two runs differ only through their arrivals at the left end (observed);
`1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA` has another table for the pass.
They are different machines and separate halting questions. Machines 31 to 33 of the family share `A = 1RB 0RB` and
the plan "a pass from the right end that stops at a block of a certain kind; a halt only at the leftmost block", with
other passes.

## What it does

**Where it can halt** (a hand argument from the table). The only halting transition is F on 0. F is entered only from
C on 0, and C only from B on 0 or E on 1, all moving left, so a halt is `0 0 B> 0` or `0 0 E> 1`. B stands on a 0 with
a 0 on its left only after A read a 1 there (`0 A> 1 0`), and that cannot happen after the first step: A is always
entered either from the right, with a freshly written 1 on its right, or from the left, with a freshly written 1 on
its left. E is entered only from D on 0, moving left, so what remains is `0 0 1 D> 0`: the pass on a separator, a
block of length 1 left of it, and two 0s left of that.
Lean proves that this pattern halts (`halt_pass`, three steps). At all the snapshots below the 0s inside the tape
are single (observed, not proved; two 0s were seen only at the two ends of the tape), so the pattern can only form
at the left end: **a pass must reach the leftmost block while that block has length 1.**

**The pass** (`lean/Rules.lean`, all lengths, any surrounding tape). The pass moves left in state D from
separator to separator.

| left of the separator | what happens | theorem |
|---|---|---|
| a block of length k+3 | it is cut into k+1 and 1, the pass goes on | `pass_split` |
| a block of length 1, a 1 two cells further left | the separator left of the block is filled, F turns the head around | `pass_stop` |
| a block of length 1, then `0 0` | F reads 0: **halt** | `halt_pass` |

At the snapshots every block is odd except the leftmost one and the unfinished word at the right end, so the
pass does not meet a block of length 2.

**The block of words.** The pass crosses n words `111110` in 6n steps, turning each into `1110 10` and staying in
state D (`cross_left`); the sweep back in state A turns them into `111110` again, read one cell later
(`cross_right`). Both are proved for every n and every surrounding tape, so *these two crossings* do not depend on
the length of the block. Call a *trigger* a step at which the head visits a new cell on the right in state
B; the tape is then `REST (111110)^n 1111` with the head right of it, and the block gains a word
every three triggers.

**Arrivals at the left end** (real machine, `c/reduced.c` with nothing cut). The left end of the tape moves only
when a pass crosses the whole zone:

| trigger | step of the last new cell | what was seen |
|---|---|---|
| 1, 3, 8, 13, 37 | 14 to 2,599 | the tape is still short |
| 144 | 28,971 | six new cells; the zone goes on beside the left end |
| 9472 | 178,267,564 | three new cells; **the zone starts again at the right end** and the block, about 3,140 words long, stays behind |

Since step 178,267,564 the tape is `W (111110)^a Z (111110)^n`: the old zone `W` at the left end (about 100 cells),
the stranded block (a = 3,127 at 10^11 steps; the zones take or give back a word now and then), the new zone `Z` and
the new growing block. Passes that get through `Z` cross the stranded block and act on `W` as before: `W` is now a
counter that moves once per overflow of `Z`.

Block lengths at some triggers (`c/snap.c`; `(5)^n` is n words, the first number of each line is the step):

    100,014,733    4 3 1 9 (1)^5 3 7 1 3 (1)^3 3 5 3 1 1 (7)^3 1 1 (5)^2354 3
    200,006,232    8 (1)^5 5 5 1 1 17 1 7 3 (1)^3 7 3 5 1 5 3 (5)^3132 1 1 3 1 3 5 (1)^3 7 5 1 5 3 1 3 5 5 3 1 1 (5)^1079 3
    1,000,056,196  8 (1)^5 5 5 1 1 17 1 7 3 (1)^3 7 3 1 1 7 1 1 (5)^3129 1 9 (1)^4 5 3 5 1 1 3 3 (1)^3 11 1 3 5 5 3 1 1 9 (5)^6750 3
    100,000,018,588  8 (1)^5 5 5 1 1 17 1 7 3 (1)^3 7 5 5 3 1 1 (5)^3127 1 5 1 3 3 1 3 (1)^4 3 (1)^3 3 (3 1)^3 (1)^3 7 1 3 5 5 1 1 3 9 (5)^74465 3

**The reduced system** (`c/reduced.c`). Because the two crossings do not depend on n, one expects that deleting
words from the block at a trigger does not change what happens to `REST`. This is *not proved*: a round trip
consists of several partial passes, and nothing here excludes other ways of entering the block. It was checked by
running the real machine next to the reduced one for 20,000 triggers (`resetsim ... check`, from the folder of
`1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC`): the runs agree at every trigger except the arrival of trigger 9472,
where the block that stays behind has about 3,140 words in one run and 10 in the other; the comparison then goes on
with the stranded block as part of `REST`, and the runs agree again. With the block cut to 10 words at every trigger
a trigger costs about 150 steps instead of a walk over the whole tape, and the reduced run goes far beyond the
real one:

| reduced run | result |
|---|---|
| started from the real configuration of trigger 20,000 (stranded block at its real length) |  |
| deepest pass, cells from the left end of the tape | 86 (trigger 28,675), 84 (159,868), 68 (273,692), 50 (5,166,316) |
| up to trigger 1,073,741,824 | no deeper pass, no arrival at the left end, no halt |

Trigger 1,073,741,824 of the real machine is near step 2·10^18 (the step count is about twice the square of the
trigger count). The triggers of these depth records are those of `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA` plus
exactly 952 = 9472 − 8520: after their last arrivals the two machines rebuild the same zone.

**The zone alone** (`c/zone.c`). The leftmost zone can be run by itself: `REST` followed by twelve words, a pass
arriving on the last separator, until the head leaves on the right; the cells left of the words are the next `REST`.
Started from the real `REST` of trigger 200, this model reaches the left end in its tick 9,273, which is trigger 9472,
with the same new cells and the same blocks afterwards as the real tape. The head leaves on the right in state B after
an ordinary tick and in state A after the arrival of trigger 9472, the one after which a new zone appears at the right
end. Continued, the model has two more arrivals and **halts in tick 38,816** (counted from trigger 200): the last
arrival leaves a lone 1 as leftmost block, and the next pass to cross the zone halts. This is *not* a prediction for
the machine. The model counts passes that reach the old zone, and after trigger 9472 such a pass comes only when the
new zone lets one through: in the reduced run the 1st, 2nd, 4th, 8th, 16th and 32nd come at triggers 9475, 9476, 9484,
9532, 12,028 and 5,166,316, and the 64th has not come by trigger 3·10^8. The model needs 29,543 of them. Meanwhile the
stranded block shrinks (3,144 words just after the arrival, 3,127 at 10^11 steps), and what happens when the two zones
meet is outside the model. What the model does show is that an arrival can leave a lone 1 at the left end.

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
| the halting pattern `0 0 1 D> 0` | kernel | `halt_pass`, `lean/Rules.lean` |
| the pass over a block and its stop, all lengths, any context | kernel | `pass_split`, `pass_stop`; generated by `py/gen_rules.py` |
| the crossings of `(111110)^n`, all n, any context | kernel | `cross_left`, `cross_right` |
| no halt in 10^11 steps; the arrivals at the left end and the stranded block | trusted | `c/snap.c`, `c/reduced.c` |
| the reduced system: no halt and no arrival at the left end from trigger 20,000 to 1,073,741,824 | observed (rests on the unproved reduction) | `c/reduced.c` |
| the leftmost zone alone: reproduces the real arrivals; continued by itself it halts in tick 38,816 | a model, checked at the real arrivals | `c/zone.c` |

## For later

* Prove the reduction: that every entry of the head into the block of words between two triggers is one of the two
  proved crossings. With that, a halt of the reduced system would be a halt of the machine, and a cycle of the
  reduced system a proof that it never halts.
* Prove that the 0s inside the tape stay single.
* The zone as a counter: a law for the depth of the passes and for what an arrival at the left end does to the
  leftmost blocks.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/lean/check.sh
gcc -O2 -o snap holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/snap.c && ./snap 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA 1e8 2e8 1e9
gcc -O2 -o reduced holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/reduced.c
./reduced 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA B 1111 10 12000 1e18        # the real machine: arrivals at the left end
./reduced 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA B 1111 10 1e8 20000    # the reduced system
gcc -O2 -o zone holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/zone.c && ./zone 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA D B 1111 200 1e5 quiet    # the zone alone
```

## Pages

- [`pages/holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/explainer.html`](../../pages/holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/explainer.html)
- [`pages/holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/proof-status.html`](../../pages/holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB`](../1RB1RD_1LC0LC_1RD1LB_1RF0RE_0RA1RE_---1RB/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror

<!-- end of related machines -->
