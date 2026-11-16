# 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA

bbchallenge id 73071. A six-state holdout of BB(6), fifth of the family of six starting `1RB0RB` (holdout indices
31–36). **Open.** The tape is a row of blocks of 1s separated by single 0s. At the right end a block of
words `111110` grows by two cells per round trip of the head. Left of it lies a *zone* of about a hundred cells that
every round trip rewrites: a pass coming from the right end cuts each block of three or more 1s in two and stops at
the first block of length 1. How deep the passes reach behaves like a counter, deeper passes being rarer and rarer.
The machine can halt only when a pass gets through everything and meets a block of length 1 at the very left end
of the tape. No halt in 10^11 steps; the last time a pass reached the left end was step 143,858,957, and since then
the zone has started again further right, leaving a block of about 2,810 words between it and its old cells.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 1LC | 1RA |
| C | 1LF | 0LD |
| D | 0LE | 1LD |
| E | 1RA | 1LC |
| F | --- | 1LA |

Relatives: `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA` (50378), `1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA` (25821)
and `1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB` (117020, states renamed) have the same right sweep, the same pass and
the same block of `111110` words; `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA` differs from this machine only in what E
does on a 0 (`1RA` here, `1LA` there), a transition used only where two 0s stand side by side, which at the snapshots
means at the left end of the tape. The two runs differ only through their arrivals at the left end (observed);
`1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA` has another table for the pass.
`1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB` is this machine's table with the states renamed, started in another state.
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
| 1, 4, 7, 12, 18, 24, 45 | 10 to 3,830 | the tape is still short |
| 2384 | 11,002,873 | one new cell; the zone goes on beside the left end |
| 8520 | 143,858,957 | four new cells; **the zone starts again at the right end** and the block, about 2,820 words long, stays behind |

Since step 143,858,957 the tape is `W (111110)^a Z (111110)^n`: the old zone `W` at the left end (about 100 cells),
the stranded block (a = 2,807 at 10^11 steps; the zones take or give back a word now and then), the new zone `Z` and
the new growing block. Passes that get through `Z` cross the stranded block and act on `W` as before: `W` is now a
counter that moves once per overflow of `Z`.

Block lengths at some triggers (`c/snap.c`; `(5)^n` is n words, the first number of each line is the step):

    100,016,469    2 7 1 3 1 (3)^3 9 1 3 1 3 (1)^3 3 5 3 1 1 (7)^3 1 1 (5)^2354 3
    200,006,748    3 1 1 17 (1)^3 5 5 (1)^4 3 3 5 1 1 5 1 7 3 5 1 5 3 (5)^2812 1 3 1 1 3 9 (1)^4 9 (1)^6 3 5 1 1 3 9 (5)^1753 3
    1,000,047,592  3 1 1 17 (1)^3 5 5 (1)^4 3 3 5 1 1 5 1 7 3 1 1 7 1 1 (5)^2809 1 9 1 3 3 7 1 3 5 5 (1)^5 (3)^3 9 1 7 3 1 1 (5)^6891 3
    100,000,377,992  3 1 1 17 (1)^3 5 5 (1)^4 3 3 5 1 1 5 1 7 5 5 3 1 1 (5)^2807 1 5 1 3 3 1 3 (1)^4 3 (1)^3 3 (3 1)^3 (1)^3 (3)^3 7 5 3 1 1 9 (5)^74478 3

**The reduced system** (`c/reduced.c`). Because the two crossings do not depend on n, one expects that deleting
words from the block at a trigger does not change what happens to `REST`. This is *not proved*: a round trip
consists of several partial passes, and nothing here excludes other ways of entering the block. It was checked by
running the real machine next to the reduced one for 20,000 triggers (`resetsim ... check`, from the folder of
`1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC`): the runs agree at every trigger except two arrivals at the left end:
trigger 45, where `REST` differs by six cells, and trigger 8520, where the block that stays behind has about 2,820
words in one run and 10 in the other; the comparison then goes on with the stranded block as part of `REST`, and the
runs agree again. With the block cut to 10 words at every trigger
a trigger costs about 150 steps instead of a walk over the whole tape, and the reduced run goes far beyond the
real one:

| reduced run | result |
|---|---|
| started from the real configuration of trigger 20,000 (stranded block at its real length) |  |
| deepest pass, cells from the left end of the tape | 91 (trigger 27,723), 89 (158,916), 73 (272,740), 65 (5,165,364) |
| up to trigger 1,073,741,824 | no deeper pass, no arrival at the left end, no halt |

Trigger 1,073,741,824 of the real machine is near step 2·10^18 (the step count is about twice the square of the
trigger count). The triggers of these depth records are those of `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA` minus
exactly 952 = 9472 − 8520: after their last arrivals the two machines rebuild the same zone.

**The zone alone** (`c/zone.c`). The leftmost zone can be run by itself: `REST` followed by twelve words, a pass
arriving on the last separator, until the head leaves on the right; the cells left of the words are the next `REST`.
Started from the real `REST` of trigger 100, this model reaches the left end in its ticks 2,285 and 8,421, which are
triggers 2384 and 8520, with the same new cells and the same blocks afterwards as the real tape. The head leaves on
the right in state B after an ordinary tick and in state A after the arrival of trigger 8520, the one after which a
new zone appears at the right end. Continued, the model has 19 more arrivals and **halts in tick 4,581,101** (counted
from trigger 100): the last arrival leaves a lone 1 as leftmost block, and the next pass to cross the zone halts. This
is *not* a prediction for the machine. The model counts passes that reach the old zone, and after trigger 8520 such a
pass comes only when the new zone lets one through: in the reduced run the 1st, 2nd, 4th, 8th, 16th and 32nd come at
triggers 8523, 8524, 8532, 8580, 11,076 and 5,165,364, and the 64th has not come by trigger 3·10^8. The model needs
about 4.6 million of them. Meanwhile the stranded block shrinks (2,824 words just after the arrival, 2,807 at 10^11
steps), and what happens when the two zones meet is outside the model. What the model does show is that an arrival can
leave a lone 1 at the left end.

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

At zone step 3·10^7 (`lean/DumpState.lean` writes the state) the reversed word is: the block (n = 29,991,481),
a new zone of about 79 letters, the stranded block of 8,397 letters of period 3, and the old zone, the
last 53 letters (the leftmost cells of the tape).

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
| the old zone alone (`z1`), one tick per pass, while the block lasts | the old zone has no reset and no halt in the 8,397 ticks; the block is then used up |

The new zone is the same in `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`, `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA` and `1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB`: the depths of their sweeps over 10^9 steps have the same
histogram, and their passes come at the same block counts. Only the old zones and the stranded blocks differ.

So nothing can happen at the left end before the new zone has let through 8,397 passes. It lets one through about 7 times per factor of 10 in sweeps; at that rate the block lasts for about 10^1200 sweeps. That rate is an extrapolation, not a proof, and what happens when the two zones meet is open.

## Status

Open. Proved in Lean (kernel): the halting pattern, the pass over a block and its stop, the two crossings of the
block of words; one round trip of the head is one XOR sweep of the word read in pairs, and a halt needs a pass that
reaches the left end (`mstep_ok`, `mstep_halt`); the length of the block of words does not matter beyond mod 3
(`zone_step`); the machine halts iff the zone orbit halts (`halts_iff_zone`). Compiled evaluation: no halt in the
first 1.7·10^15 steps. Trusted runs from the Lean state: nothing can happen at the left end before the new zone has let 8,397 sweeps through. Nothing is known that keeps the leftmost block from
being a lone 1 when a pass arrives, and nothing that forces it.

## What is proved

| result | level | where |
|---|---|---|
| halts exactly when F reads 0 | kernel | `step_none_iff`, `lean/Blank.lean` |
| no halt in 10^4 / 10^7 steps | kernel / native | `blank_runs_kernel`, `blank_runs_native` |
| the halting pattern `0 0 1 D> 0` | kernel | `halt_pass`, `lean/Rules.lean` |
| the pass over a block and its stop, all lengths, any context | kernel | `pass_split`, `pass_stop`; generated by `py/gen_rules.py` |
| the crossings of `(111110)^n`, all n, any context | kernel | `cross_left`, `cross_right` |
| no halt in 10^11 steps; the arrivals at the left end and the stranded block | trusted | `c/snap.c`, `c/reduced.c` |
| the reduced system: no halt and no arrival at the left end from trigger 20,000 to 1,073,741,824 | trusted (cutting whole words keeps the block length mod 3, so between arrivals the cut is exact by `zone_step`) | `c/reduced.c` |
| the leftmost zone alone: reproduces the real arrivals; continued by itself it halts in tick 4,581,101 | a model, checked at the real arrivals | `c/zone.c` |
| one round trip at the right end is one XOR sweep of the word (rightmost `00`, flip, XOR differences, `11`); a halt needs a `00` only at the left end | kernel | `mstep_ok`, `mstep_halt`, `lean/Bits.lean` |
| the zone reduction: the block of words enters only through its length mod 3; frozen zones; pass-through | kernel | `zone_step`, `swr_append_ok`, `swr_split`, `xd_append`, `lean/Xor.lean` |
| the machine halts iff the zone orbit halts | kernel | `halts_iff_zone`, `lean/Zone.lean` |
| no halt in the first 1.7·10^15 steps (3·10^7 steps of the zone orbit) | native | `zone_runs`, `blank_runs_zone`, `lean/ZoneRun.lean` |
| two zones: the old zone alone, exact while the stranded block lasts: no reset and no halt in its next 8,397 ticks (one per pass through the new zone); 3·10^10 more sweeps of the orbit, 23 passes, no halt | trusted | `c/xs.c`, `c/z1.c` in the folder of `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`, from `lean/DumpState.lean` |

### Exact reduction (Lean)

Reading the tape in pairs (`11` = 1, `01` = 0), `lean/Sweep.lean` defines a macro step `mstep` on binary words and proves it sound for every word; `lean/Reduce.lean` proves `halts_iff : HaltsFromBlank ↔ ∃ k, HaltsAt k`, i.e. the machine halts from blank tape iff the macro orbit halts. Unlike the reduced system above, this reduction is proved. `py/passmachine.py` is a Python transcription of `mstep` checked against direct simulation.

| result | level | where |
|---|---|---|
| The pass machine | kernel | `scanF_sound`, `apass_sound`, `mstep_sound`, `lean/Sweep.lean` |
| Halting is exactly a question about the orbit | kernel | `orbT_sound`, `halts_iff`, `lean/Reduce.lean` |
| No halt in the first 4·10^8 steps | native | `orbit_runs`, `blank_runs_orbit`, `lean/OrbitRun.lean` |

## For later

* A law for how often the new zone lets a sweep through (about 7 per factor of 10 in the runs), and what happens
  when the new zone reaches the old one.
* Formalize the two-zone argument (the old zone moves as if alone while the stranded block lasts) as a theorem about
  the zone orbit; today it is a hand argument from `swr_append_ok`, `swr_split` and `xd_append`.
* The zone as a counter: a law for the depth of the passes and for what an arrival at the left end does to the
  leftmost blocks.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA/lean/check.sh
gcc -O2 -o snap holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/snap.c && ./snap 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA 1e8 2e8 1e9
gcc -O2 -o reduced holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/reduced.c
./reduced 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA B 1111 10 12000 1e18        # the real machine: arrivals at the left end
./reduced 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA B 1111 10 1e8 20000    # the reduced system
gcc -O2 -o zone holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/zone.c && ./zone 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA D B 1111 100 1e7 quiet    # the zone alone
(cd holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA/lean && LEAN_PATH=$LEANLIB:../../../tools/lean/out:out lean DumpState.lean > /tmp/state.txt)    # after check.sh
gcc -O2 -o xs holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/xs.c && ./xs /tmp/state.txt 3e10 1000    # the zone orbit, 3·10^10 more sweeps
gcc -O2 -o z1 holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/c/z1.c && ./z1 /tmp/state.txt    # the old zone alone while the stranded block lasts
```

## Pages

- [`pages/holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA/explainer.html`](../../pages/holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA/explainer.html)
- [`pages/holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA/proof-status.html`](../../pages/holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB`](../1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E

<!-- end of related machines -->
