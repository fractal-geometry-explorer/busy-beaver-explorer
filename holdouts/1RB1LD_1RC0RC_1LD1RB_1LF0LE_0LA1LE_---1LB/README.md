# 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB

bbchallenge id 117020. A six-state holdout of BB(6). Its table is that of `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA`
(73071) with the states A, B, C, D, E renamed B, C, D, E, A; started in its own state A it is that machine started in
state E, a different run. **Open.** The tape is a row of blocks of 1s separated by single 0s. At the right end a block
of
words `111110` grows by two cells per round trip of the head. Left of it lies a *zone* of about a hundred cells that
every round trip rewrites: a pass coming from the right end cuts each block of three or more 1s in two and stops at
the first block of length 1. How deep the passes reach behaves like a counter, deeper passes being rarer and rarer.
The machine can halt only when a pass gets through everything and meets a block of length 1 at the very left end
of the tape. No halt in 10^11 steps. Up to step 2.5·10^10 passes reached the left end eleven times without halting; at
the last of these, step 25,407,980,161, the zone started again further right, leaving a block of about 37,550 words
between it and its old cells.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1RC | 0RC |
| C | 1LD | 1RB |
| D | 1LF | 0LE |
| E | 0LA | 1LE |
| F | --- | 1LB |

Relatives: `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA` (50378), `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA` (73071)
and `1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA` (25821) have the same right sweep, the same pass and the same block of
`111110` words; 73071 has this machine's table before the renaming, so the two are the same system started from two
different configurations; 50378 differs from it in one transition and 25821 has another table for the pass.
They are different machines and separate halting questions. The first two of them belong to the family of six starting
`1RB0RB` (holdout indices 31–36).

## What it does

**Where it can halt** (a hand argument from the table). The only halting transition is F on 0. F is entered only from
D on 0, and D only from C on 0 or A on 1, all moving left, so a halt is `0 0 C> 0` or `0 0 A> 1`. C stands on a 0 with
a 0 on its left only after B read a 1 there (`0 B> 1 0`), and that cannot happen: B is always entered either from the
right, with a freshly written 1 on its right, or from the left, with a freshly written 1 on its left. A is entered
only from E on 0, moving left, so what remains is `0 0 1 E> 0`: the pass on a separator, a block of length 1 left of
it, and two 0s left of that.
Lean proves that this pattern halts (`halt_pass`, three steps). At all the snapshots below the 0s inside the tape
are single (observed, not proved; two 0s were seen only at the two ends of the tape), so the pattern can only form
at the left end: **a pass must reach the leftmost block while that block has length 1.**

**The pass** (`lean/Rules.lean`, all lengths, any surrounding tape). The pass moves left in state E from
separator to separator.

| left of the separator | what happens | theorem |
|---|---|---|
| a block of length k+3 | it is cut into k+1 and 1, the pass goes on | `pass_split` |
| a block of length 1, a 1 two cells further left | the separator left of the block is filled, F turns the head around | `pass_stop` |
| a block of length 1, then `0 0` | F reads 0: **halt** | `halt_pass` |

At the snapshots every block is odd except the leftmost one and the unfinished word at the right end, so the
pass does not meet a block of length 2.

**The block of words.** The pass crosses n words `111110` in 6n steps, turning each into `1110 10` and staying in
state E (`cross_left`); the sweep back in state B turns them into `111110` again, read one cell later
(`cross_right`). Both are proved for every n and every surrounding tape, so *these two crossings* do not depend on
the length of the block. Call a *trigger* a step at which the head visits a new cell on the right in state
C; the tape is then `REST (111110)^n 1111` with the head right of it, and the block gains a word
every three triggers.

**Arrivals at the left end** (real machine, `c/reduced.c` with nothing cut). The left end of the tape moves only
when a pass crosses the whole zone:

| trigger | step of the last new cell | what was seen |
|---|---|---|
| 1, 2, 4, 5, 8, 10, 32, 34 | 6 to 2,426 | the tape is still short |
| 2365, 2725, 12349, 21636, 29853, 38172, 43837, 49053, 49293 | 10,925,936 to 4,854,078,004 | two new cells each time; the zone goes on beside the left end |
| 62244 | 7,741,657,181 | one new cell; the zone goes on |
| 112740 | 25,407,980,161 | four new cells; **the zone starts again at the right end** and the block, about 37,550 words long, stays behind |

Since step 25,407,980,161 the tape is `W (111110)^a Z (111110)^n`: the old zone `W` at the left end (about 100 cells),
the stranded block (a = 37,550 at 10^11 steps), the new zone `Z` and the new growing block. Passes that get through
`Z` cross the stranded block and act on `W` as before (observed): `W` is now a counter that moves once per overflow of
`Z`.

Block lengths at some triggers (`c/snap.c`; `(5)^n` is n words, the first number of each line is the step):

    1,000,073,843    3 15 1 7 1 1 5 (1)^7 3 7 3 7 1 5 1 1 9 (5)^7450 3
    24,000,423,913   2 3 3 1 1 5 3 3 (5)^3 1 7 1 1 7 3 (1)^3 (5)^4 1 1 (5)^36512 3
    26,000,008,932   3 5 9 (1)^4 13 5 5 1 5 (1)^3 3 3 1 5 3 3 5 1 5 3 (5)^37553 1 1 5 (3)^3 7 1 1 3 (1)^4 3 1 3 1 9 7 1 7 5 3 (5)^5691 3
    100,000,658,196  3 5 9 (1)^4 13 5 5 1 5 (1)^3 3 3 1 5 3 5 3 1 1 9 (5)^37550 1 3 1 1 3 7 1 3 1 1 7 5 1 1 3 1 3 1 5 3 3 1 3 7 5 3 1 1 9 (5)^64366 3

**The reduced system** (`c/reduced.c`). Because the two crossings do not depend on n, one expects that deleting
words from the block at a trigger does not change what happens to `REST`. This is *not proved*: a round trip
consists of several partial passes, and nothing here excludes other ways of entering the block. It was checked by
running the real machine next to the reduced one for 20,000 triggers (`resetsim ... check`, from the folder of
`1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC`): (797,722,014 steps, three arrivals at the left end among them) the runs
agree at every trigger. With the block cut to 10 words at every trigger
a trigger costs about 150 steps instead of a walk over the whole tape, and the reduced run goes far beyond the
real one:

| reduced run | result |
|---|---|
| started from the real configuration of trigger 112,741, just after the last arrival (stranded block at its real length) |  |
| passes that reach the old zone | the 1st, 2nd, 4th, 8th, 16th and 32nd at triggers 112,743, 112,744, 112,752, 112,800, 115,296 and 5,269,584 |
| up to trigger 134,217,728 | no arrival at the left end, no halt |

The 64th such pass has not come by trigger 134,217,728, where this run was stopped: the old zone is visited more and
more rarely.

**The zone alone** (`c/zone.c`). The leftmost zone can be run by itself: `REST` followed by eleven words, a pass
arriving on the last separator, until the head leaves on the right; the cells left of the words are the next `REST`.
Started from the real `REST` of trigger 100, this model reaches the left end in exactly the triggers of the table
above (tick k is trigger k + 99), with the same new cells; it has one more arrival, at trigger 53,223, that adds no
cell. As long as the head leaves on the right in the usual state (C) the model is the machine seen from the zone, and
one tick is one trigger. At trigger 112,740 the head leaves in state B, and that is the arrival after which a new zone
appears at the right end. Continued by itself, the model has 36 more arrivals and **halts in tick 21,540,826**: the
last arrival leaves a lone 1 as leftmost block, and the next pass to cross the zone halts. This is *not* a prediction
for the machine. After trigger 112,740 the old zone gets a pass only when the new zone lets one through (table above),
the model needs 21,428,185 of them, the stranded block is being used up meanwhile, and what happens when the two zones
meet is outside the model. What the model does show is that an arrival can leave a lone 1 at the left end.

## The XOR sweep and the zone orbit (Lean, every length)

Read in pairs (`11` = 1, `01` = 0), the tape at a turn at the right end is a binary word whose last letter is the
pair under the head. `lean/Bits.lean` proves that one round trip of the head is exactly one **XOR sweep** of that word
(`mstep_ok`, for every word with a `00`; `4d + 12` steps, `d` the distance of the `00` from the head):

* find the rightmost `00`;
* flip the letter just left of it;
* replace every letter right of it by the XOR of itself and its right neighbour;
* append `11` at the right end.

A `00` only at the very left end of the word halts the machine (`mstep_halt`), and a word without `00` is a *reset*,
the pass running off the left end, which the pass machine of `lean/Sweep.lean` handles. So **a halt needs a pass that
reaches the left end of the tape**, now proved. The machine-independent facts are in `lean/Xor.lean`, the same file in
the folders of the four machines with this block:

| lemma | what it says |
|---|---|
| `zone_step` | **the leftmost-zone reduction.** The block of `111110` words is the word `110110…` at the head end of the reversed word (`blk`). For every length of the block, the sweep does to the rest of the word what the sweep of `pat n :: Z` does: the length enters only mod 3, through one letter. This is the model of `c/zone.c`, proved |
| `swr_append_ok` | a sweep that finds its `00` before a stretch of the word leaves that stretch untouched: a zone further left is **frozen** |
| `swr_halt_snoc` | a `00` at the very end of a prefix flips only the next letter |
| `swr_split` | a sweep through a stretch without `00` turns it into its XOR differences; what it does beyond depends only on the stretch's last letter (**pass-through**) |
| `xd_append` | the light cone: the XOR differences over a suffix depend only on that suffix |

`lean/Zone.lean` turns this into the **zone orbit**: a state `(n, Z, rest)` keeps only the count `n` of the block and
the rest of the word `Z`. `halts_iff_zone`: **the machine halts from blank tape iff the zone orbit halts.** Unlike the
reduced system of `c/reduced.c`, which cut the block to ten words, this one drops the block completely and is proved.
A sweep now costs the depth of its pass, not the length of the tape, so `lean/ZoneRun.lean` (compiled evaluation) runs
3·10^7 steps of the orbit: **no halt in the first 1.7·10^15 steps** (`blank_runs_zone`).

### Two zones

At zone step 3·10^7 (`lean/DumpState.lean` writes the state) the reversed word is: the block (n = 29,887,259),
a new zone of about 79 letters, the stranded block of 112,628 letters of period 3, and the old zone, the
last 54 letters (the leftmost cells of the tape).

The stranded block has no `00`, so by `swr_append_ok` a sweep that stops in the new zone leaves the block and the old
zone alone, and by `swr_split` a sweep that gets through the new zone (a *pass*) acts on the old zone through the
block's last letter only. Positions counted from the left end of the tape do not move under a sweep, and a letter can
change only through itself and its right neighbour (`xd_append`) or by the flip next to a `00`. So the cells that can
differ from a run of the block and the old zone *by themselves* spread from the new zone by at most one cell per sweep
that reaches the block, and **for as long as the block lasts the old zone sees exactly what it would see alone, one
tick per pass** (hand argument from the Lean lemmas; checked: after each of the 23 passes of the run below, the
leftmost 60 cells equal those of the run alone).

| run (trusted, `c/xs.c`, `c/z1.c` in the folder of `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`, from the Lean state) | result |
|---|---|
| the zone orbit for 3·10^10 more sweeps | no halt, no reset; 23 passes into the old zone, at block counts spread evenly over the decades (about 7 per factor of 10) |
| the old zone alone (`z1`), one tick per pass, while the block lasts | the old zone **resets in its tick 17,532**, with 95,097 letters of the block left: that is the next arrival at the left end, at the 17,532nd pass through the new zone |

The new zone is the same in `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`, `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA` and `1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB`: the depths of their sweeps over 10^9 steps have the same
histogram, and their passes come at the same block counts. Only the old zones and the stranded blocks differ.

So the next arrival at the left end, a reset and not a halt, comes at the 17,532nd pass, and nothing else happens at the left end before it. The new zone lets a pass through about 7 times per factor of 10 in sweeps; at that rate the arrival is about 10^2500 sweeps away (an extrapolation). What the reset does next is open.

## Status

Open. Proved in Lean (kernel): the halting pattern, the pass over a block and its stop, the two crossings of the
block of words; one round trip of the head is one XOR sweep of the word read in pairs, and a halt needs a pass that
reaches the left end (`mstep_ok`, `mstep_halt`); the length of the block of words does not matter beyond mod 3
(`zone_step`); the machine halts iff the zone orbit halts (`halts_iff_zone`). Compiled evaluation: no halt in the
first 1.7·10^15 steps. Trusted runs from the Lean state: the next arrival at the left end comes at the 17,532nd sweep that gets through the new zone, and it is not a halt. Nothing is known that keeps the leftmost block from
being a lone 1 when a pass arrives, and nothing that forces it.

## What is proved

| result | level | where |
|---|---|---|
| halts exactly when F reads 0 | kernel | `step_none_iff`, `lean/Blank.lean` |
| no halt in 10^4 / 10^7 steps | kernel / native | `blank_runs_kernel`, `blank_runs_native` |
| the halting pattern `0 0 1 E> 0` | kernel | `halt_pass`, `lean/Rules.lean` |
| the pass over a block and its stop, all lengths, any context | kernel | `pass_split`, `pass_stop`; generated by `py/gen_rules.py` |
| the crossings of `(111110)^n`, all n, any context | kernel | `cross_left`, `cross_right` |
| no halt in 10^11 steps; the arrivals at the left end and the stranded block | trusted | `c/snap.c`, `c/reduced.c` |
| the reduced system: no halt and no arrival at the left end from trigger 112,741 to 134,217,728 | trusted (cutting whole words keeps the block length mod 3, so between arrivals the cut is exact by `zone_step`) | `c/reduced.c` |
| the leftmost zone alone: reproduces all eleven real arrivals; continued by itself it halts in tick 21,540,826 | a model, checked at the real arrivals | `c/zone.c` |
| the pass machine: the `Sweep.lean` of `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA` with its states renamed, all lists; halting is exactly a question about its orbit from the first turn (step 3) | kernel | `mstep_sound`, `init_RT`, `lean/Sweep.lean`; `halts_iff`, `lean/Reduce.lean` |
| one round trip at the right end is one XOR sweep of the word (rightmost `00`, flip, XOR differences, `11`); a halt needs a `00` only at the left end | kernel | `mstep_ok`, `mstep_halt`, `lean/Bits.lean` |
| the zone reduction: the block of words enters only through its length mod 3; frozen zones; pass-through | kernel | `zone_step`, `swr_append_ok`, `swr_split`, `xd_append`, `lean/Xor.lean` |
| the machine halts iff the zone orbit halts | kernel | `halts_iff_zone`, `lean/Zone.lean` |
| no halt in the first 1.7·10^15 steps (3·10^7 steps of the zone orbit) | native | `zone_runs`, `blank_runs_zone`, `lean/ZoneRun.lean` |
| two zones: the old zone alone, exact while the stranded block lasts: it resets (the next arrival at the left end) in its tick 17,532, one tick per pass through the new zone, and does not halt before; 3·10^10 more sweeps of the orbit, 23 passes, no halt | trusted | `c/xs.c`, `c/z1.c` in the folder of `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`, from `lean/DumpState.lean` |

## For later

* A law for how often the new zone lets a sweep through (about 7 per factor of 10 in the runs), and what happens
  when the new zone reaches the old one.
* Formalize the two-zone argument (the old zone moves as if alone while the stranded block lasts) as a theorem about
  the zone orbit; today it is a hand argument from `swr_append_ok`, `swr_split` and `xd_append`.
* The zone as a counter: a law for the depth of the passes and for what an arrival at the left end does to the
  leftmost blocks.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/lean/check.sh
gcc -O2 -o snap holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/snap.c && ./snap 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB 1e9 2.4e10 2.6e10
gcc -O2 -o reduced holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/reduced.c
./reduced 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB C 1111 10 12000 1e18        # the real machine: arrivals at the left end
./reduced 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB C 1111 10 120000 1e18    # the reduced system
gcc -O2 -o zone holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/zone.c && ./zone 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB E C 1111 100 3e7 quiet    # the zone alone
(cd holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/lean && LEAN_PATH=$LEANLIB:../../../tools/lean/out:out lean DumpState.lean > /tmp/state.txt)    # after check.sh
gcc -O2 -o xs holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/xs.c && ./xs /tmp/state.txt 3e10 1000    # the zone orbit, 3·10^10 more sweeps
gcc -O2 -o z1 holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/z1.c && ./z1 /tmp/state.txt    # the old zone alone while the stranded block lasts
```

## Pages

- [`pages/holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/explainer.html`](../../pages/holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/explainer.html)
- [`pages/holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/proof-status.html`](../../pages/holdouts/1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA`](../1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B

<!-- end of related machines -->
