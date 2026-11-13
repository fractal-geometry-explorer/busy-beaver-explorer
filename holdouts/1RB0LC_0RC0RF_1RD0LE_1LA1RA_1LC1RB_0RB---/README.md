# 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---

bbchallenge id 104920. Group G01. **A list of frozen blocks with one growing block**, analysis only begun. Open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 0RC | 0RF |
| C | 1RD | 0LE |
| D | 1LA | 1RA |
| E | 1LC | 1RB |
| F | 0RB | --- |

## What it does

Sample the run when the head is in state E at the left end of the tape. Since step 9.1·10⁶ the tape has been

    E> (10)^2 (0100)^189 (10)^3 (0010)^633 (01)^2 (0001)^n  tail

with a short tail (`0^5 1^2`, `(001)^2 1`, `0^2 1^2`, empty, …). Only n changes:

    n = 13, 159, 363, 649, 1050, 1612, 2398, 3499, 5039, 7197, 10215, 14443, 20361, 28645, 40230   (step 1.93·10¹⁰)

which is a factor of 1.44 falling to 1.40 per event. The frozen blocks are what is left of earlier levels: the block
of `0100` grew 2, 4, 7, 11, …, 135, 189 and froze at step 432,110; the block of `0010` grew 27, 66, …, 452, 633
and froze at step 9.1·10⁶. At the last event the tail is `0^2 (10)^2 (0010)^7 0^2 1^2`, which may be the start of
the next level.

During one E-to-E pass the head sweeps the whole tape, and blocks are moved 14 copies at a time. For example,
sampled at the right end, the middle block (written `(1110)^j` during the sweep) loses 14 copies per B-event while
the block to its left gains 14.

The ratio is not constant and the tail changes from event to event, so the event map has more structure than a
single number. Neither the map nor the halting condition is known yet.

## What is proved

| level | result | where |
|---|---|---|
| kernel | the halting configurations (F1); no halt in 10⁴ steps | `lean/Blank.lean` (generated) |
| native | no halt in 10⁷ steps | `lean/Blank.lean` |
| trusted | the shape of the E-events up to 1.93·10¹⁰ steps | `py/events.py 2e10` |

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/lean/check.sh
python3 holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/py/events.py 2e10      # about 3 min
```

## Further work

More than a day. The next steps:

- Find a finer sampling (the right-end B-events look regular) and the exact rule for one sweep, with the tail.
- Understand when a level freezes and a new word starts (0100, then 0010, then 0001, and now perhaps a fourth level),
  and how halting (F1 read) could happen.

## Third pass

The macro simulator `c/msim.c` (a copy of the one in holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---, in
`../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/`; blocks of 4 cells; checked against the direct simulator at 10⁹ steps by `check_msim.py check`) runs
10¹⁸ steps from blank tape without a halt: `python3 ../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/py/check_msim.py run 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB--- 1e18` (2 to 5 minutes).
The frozen prefix is still there at 10¹⁵ steps (`… (0100)^633-type block, then a block of 40,231 copies`): the block
that was growing in the first analysis (n = 40,230 at 1.9·10¹⁰ steps) froze at 40,231 and a new level grows behind
it, as the tail `(10)^2 (0010)^7` suggested. So the levels so far froze at 189, 633 and 40,231 copies. The community
tracker describes the machine as "a recursive counter: the last block grows 7/5 per sweep; a halt needs a small
cluster of blocks fed a wrong carry" (rules simulated there to 2·10³² steps); 7/5 is the 1.40 measured here.

No pushdown certificate with a small DFA exists: the reduction of `bb6-1RB0LF_1RC0LB/c/pds.c` (one side of the tape
exact, the other a DFA, post* saturation) reaches a halt for every DFA with at most 6 states, on either side
(`TM=1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB--- ./pds 6 L`, then `R`; 1.5 minutes each).

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| right | 256,019,877 | 18,250 | 11 | 6 | 14 | 0.71 |
| left | 377,565,301 | 23,466 | 5 | 5 | 10 | 0.86 |
| right | 1,024,198,203 | 35,580 | 7 | 7 | 14 | 0.60 |
| left | 1,351,970,933 | 44,170 | 8 | 4 | 12 | 0.93 |
| right | 4,096,317,183 | 69,916 | 7 | 7 | 14 | 0.53 |
| left | 5,068,405,965 | 84,747 | 5 | 4 | 9 | 0.96 |
| right | 16,384,192,613 | 138,502 | 11 | 6 | 14 | 0.51 |
| left | 19,312,182,341 | 164,261 | 7 | 5 | 12 | 0.98 |

**Proposed family: F01, periodic blocks driven by a bounded engine** (frozen blocks, one growing block and a short tail).

The description is the smallest of the family: 9 to 14 level-2 tokens at every record from 3.8·10^8 to 1.9·10^10 steps. At the left-end records the tape is `(0010)^190 (01)^3 (0001)^633 001 (0100)^n` and a tail of at most 40 cells (n = 5,040, 10,216, 20,361, 40,231).

The macro simulator (blocks of 4 cells) at its last left-end record before 1.45·10^18 steps shows eleven blocks: 189, 633, 40,231, 8,119, 92,808, 5,890,878, 1,188,870, 19,851,057, 48,010,873, 11,795,335 and 284,041,139 copies. So a level ends with its block frozen and a new block started.

Within a level this is the F01 shape: one growing periodic block, a short tail, and frozen blocks that the sweeps cross. The list of frozen blocks is not bounded, so a closed set has to treat the frozen part as an arbitrary list; whether the sweeps allow that is the first thing to check.

Next step: The cheap test of F01: run the growing block symbolically, n = r + m·x with the tail from the finite set seen, and ask whether a class halts or freezes; the levels would then be a map on (tail, n mod m).

## The list of blocks up to 1.45·10^18 steps (F09, 13 November 2026)

The list of blocks, followed further with `c/msim_turns.c` and `py/phases.py` of `holdouts/1RB1RE_0RC0RF_1LC1RD_1RA0LE_0RA0LD_0RA---`
(left turns grouped by the long runs on the tape; `py/laps_1e16.txt` has the 144 groups up to 1.3·10^16 steps in which the
head turns at the left end with every long run on its right) and with two samples of the macro simulator at 5.8·10^17 and
1.45·10^18 steps. Everything here is observed in one run; none of it is proved.

Blocks in the order in which they stopped growing (copies of a four-cell word; the word of a block rotates as the head passes):

| copies when it stopped growing | about step | later |
|---|---|---|
| 189 | 432,110 | exact so far |
| 633 | 9.1·10^6 | exact so far |
| 40,231 | 1.9·10^10 | exact so far |
| 8,119 | 3.4·10^10 | exact so far |
| 92,784 | 2.5·10^11 | 92,784 at 3.7·10^11, 92,799 at 9.3·10^15, 92,808 at 1.45·10^18 |
| 5,890,876 | 4.2·10^14 | 5,890,876 to 5,890,878, back and forth |
| 1,188,875 | 1.1·10^15 | 1,188,875 at 1.1·10^15, 1,188,870 at 1.45·10^18 |
| 19,851,057 | 8.5·10^15 | 19,851,057 or 19,851,058 |
| 48,010,873 | before 5.8·10^17 | same at both samples |
| 11,795,336 | before 5.8·10^17 | 11,795,335 at 1.45·10^18 |

Two things are new compared with the sections above. First, the blocks that stopped growing are not all frozen: the fifth one
gains one copy every second lap, and the seventh loses copies slowly. So the earlier blocks are not constants of the run, and a
proof cannot treat them as fixed parameters. Second, the sizes at which blocks stop growing have no visible order (40,231, then
8,119, then 92,784, then 5,890,876, then 1,188,875): a block grows by a factor of at least 7/5 per lap for 1 to about 15 laps
and then stops. What makes it stop is not known; if it is a remainder of the block length, as the factor 7/5 suggests, the
machine is a Collatz-like counter with one more digit per level.

Reproduce the lap table (stopped by hand at 1.3·10^16 steps after 30 minutes):

    D=holdouts/1RB1RE_0RC0RF_1LC1RD_1RA0LE_0RA0LD_0RA---; gcc -O2 -o msim_turns $D/c/msim_turns.c
    ./msim_turns 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB--- 4 1.3e16 - 1 t | grep "[A-F]> " | python3 $D/py/phases.py /dev/stdin 200 20 | grep -E "^[0-9]+ x[0-9]+ [A-F]> \|"

## Pages

- [`pages/holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/explainer.html`](../../pages/holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/explainer.html)
- [`pages/holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/proof-status.html`](../../pages/holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC`](../1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/README.md): rename A→B, B→C, C→E, D→A, E→F, F→D and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
