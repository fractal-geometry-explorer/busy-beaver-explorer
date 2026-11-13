# 1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---

bbchallenge id 131976, group G08 (two-sided sqrt growth). Whether it halts from blank tape is **open**. Pages:
[`explainer.html`](../../pages/holdouts/1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---/proof-status.html), both built from
[`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 0RB |
| C | 1LD | 0RA |
| D | 0LE | 0LC |
| E | 1LB | 1LF |
| F | 1LD | --- |

## What it does

A bouncer over a list of counters. Both ends of the tape grow like the square root of the step count.

**Where it can halt.** Only in F reading a 1. F is entered from `A>1` (0LF) and from `E>1` (1LF), so the machine
halts exactly when `1 A>1` or `1 E>1` occurs. In the first 10^8 steps F is entered 27,487 times, always onto a 0,
in 22,690 of them inside `101[0]101` (`c/haltwatch.c`).

**The counters.** At the left end (`py/snapshots.py 3e7 L 50`, every 50th left-end record):

    404490 E>0 (01)^284 (10)^167 (01)^242 (10)^19 (01)^12 0 (01)^3 (10)^3 1
    432128 C>0 (01)^301 0 (01)^174 0 (01)^240 0 (01)^20 0 (01)^11 (10)^5 110101
    459974 E>0 (01)^318 0 (01)^182 0 (01)^237 (10)^23 1 (10)^11 (01)^6 00101

`(01)^a (10)^b` and `(01)^a 0 (01)^b` are the same pair of numbers with a different single-cell boundary, so the tape
is a list a, b, c, d, ... Per 50 left-end visits a grows by 17, b by about 8, c shrinks by about 3, d grows by about 4.
At the right end there are short irregular words. When a counter runs out the list is rebuilt: (185, 127, 110) at
step 136,230, (201, 124, 257) at step 284,618.

## What is proved (Lean)

Only the generated `lean/Blank.lean`: the halting configurations, no halt in 10^4 steps (kernel) and 10^7
(`native_decide`).

## Computed / observed

- No halt in 10^9 steps (`tools/c/triage.c`).
- The halt-entry counts (`c/haltwatch.c`) and the counter list (`py/snapshots.py`).

## Open, and next steps

- Find the exact update of one round trip on the list (which counters change, by how much, and how the boundary
  defects cycle); the rates 1/3, 1/6 per visit suggest the first counters are unary counters passing carries down.
- Describe the rebuild when a counter reaches 0. That is where the irregular right-end words come from and where a
  halt would happen, if it does.

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 256,031,852 | 39,174 | 12 | 11 | 23 | 0.53 |
| right | 265,922,464 | 39,822 | 9 | 12 | 21 | 0.53 |
| left | 1,024,049,454 | 77,665 | 7 | 11 | 18 | 0.50 |
| right | 1,041,449,125 | 78,345 | 11 | 11 | 22 | 0.50 |
| right | 4,096,092,650 | 149,242 | 13 | 11 | 21 | 0.59 |
| left | 4,418,819,154 | 152,716 | 14 | 9 | 20 | 0.57 |
| left | 16,384,720,828 | 335,801 | 11 | 15 | 26 | 0.39 |
| right | 16,610,321,653 | 337,961 | 15 | 15 | 27 | 0.40 |

**Proposed family: F06, block-list counters** (blocks of pairs with a base-3 counter, as in 1RB1RF_1LC0LB… (same table)).

The description grows slowly: 20 to 27 level-2 tokens at every record from 2.6·10^8 to 1.7·10^10 steps, and 11 to 46 runs in the macro simulator (blocks of 4 cells) at the sampled records up to 2·10^16 steps.

The machine shares its table with 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- (states renamed, some of the four mirrored; `related.json`), started in another state. On the screen the four runs show the same list of blocks at the same moments. For example near step 6.4·10^7 all four tapes read (mirrored) blocks of 3, 1,546, 39, 1,753, 117, 1,467 and 997 pairs `01` and then a last block, of 4,405 pairs in 1RB1RF_1LC0LB… and of 4,411 pairs here. The four last blocks differ by 2, 4 and 6 pairs and the records come at slightly different steps. This is an observation at the sampled records: it is not a proof that the runs correspond, and nothing about halting is carried over.

For 1RB1RF_1LC0LB… the right end is proved in Lean to be a base-3 counter on the separators of such a list (`bb6-1RB1RF_1LC0LB/lean/Counter.lean`). Those theorems are about that machine's table with its own state names; they apply here only after the renaming is carried through, which has not been done. A list of blocks with a base-3 counter is F06.

Next step: Carry the renaming through, so that the counter theorems of 1RB1RF_1LC0LB… become theorems about this machine, and state exactly how the two tapes differ (the last block and the left end).

## One run for four machines (F09, 13 November 2026)

Four holdouts have the same table up to renaming the states and mirroring the tape (`holdouts/related.json`), started in
four different states. Written in the states of 32883 (`1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---`):

| machine | id | start state in the table of 32883 | mirrored | first aligned trip: step, runs | first run |
|---|---|---|---|---|---|
| `1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---` | 32883 | A | no | 6, `[6]` | r + 4 |
| `1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---` | 40600 | D | yes | 1, `[2]` | r |
| `1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---` | 103746 | B | yes | 17, `[10]` | r + 8 |
| `1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---` | 131976 | E | no | 37, `[14]` | r + 12 |

A trip starts when the head, in state A of that table, steps onto a new leftmost cell; the tape is then a list of runs of
alternating cells, written as their lengths. `py/lockstep.py` of 32883 simulates two of the four runs and compares the
run lists trip by trip.

**Observed: the four runs are one run, shifted.** At every one of the first 527,004 trips, up to 2·10^12 steps, the four
tapes have the same run lengths except for the first run, and the first runs differ by constants: r for 40600, r + 4 for
32883, r + 8 for 103746 and r + 12 for 131976 (the last two need one trip more to get going, so their trip k + 1 is
compared with trip k of the others). No mismatch occurred. Output: `py/lockstep_2e12.txt` in the folder of 32883.

### What is proved, and what is missing

The four tapes differ only in the length of the first run, so the question is whether the machine can ever see that
length other than mod 4. The head touches the first run only by entering it from the right: it steps onto the last
cell of the run in one of the five states a left move leads to (A, B, C, D, F), and that cell is 0 or 1. That makes
ten entries. Each either bounces (the head looks at no more than the last 2 cells of the run and comes back out),
sweeps (the head goes to the left end, turns and comes back, and the outcome depends on the length mod 4), or halts
at once (F on a 1).

**Proved in Lean (kernel), `lean/Shift4.lean` in the folder of 32883, 24 theorems generated by `py/shift4.py`:** for every entry, the
outcome for a first run of n + 4 cells is the outcome for n cells with one more copy of a 4-cell word in the run:
same exit state, same cells left between the run and the head, same change of the run length. The bounces are
proved for any tape to the left of the cells they touch, the sweeps for every n of the form 4a + 5, 4a + 6, 4a + 7,
4a + 8. `py/shift4.py check` compares n with n + 4 by simulation for every n from 1 to 300: the outcomes agree for
every entry and every n of at least 3, and differ only for n = 1 and n = 2.

**What follows.** While the head is outside the first run, two tapes that differ only in that run make the same steps.
So the four runs stay shifted copies of each other, and the four machines halt together or not at all, **provided**
the first run of the shortest tape (the run of 40600) has at least 3 cells every time the head enters it (with at
least 5 cells every step of the argument is a Lean theorem; for 3 and 4 cells the sweeps rest on the script). That
proviso is the only thing missing. It is observed, not proved: `py/entries.py` finds that in the first 2·10^10 steps
the head enters the first run 57,701 times in the run of 40600, with at least 5 cells each time (5 at step 7, 7 at
step 16, 8 or more afterwards; `py/entries_2e10.txt`), and the first run gains 8 cells every three ordinary trips.

Why the proviso is not a local fact: a bounce takes 1 or 2 cells off the right end of the first run, and nothing in
the ten entries limits how many bounces can happen between two sweeps. In the real run there is at most one bounce per
ordinary trip (the carry at digit 1), so the run grows, but showing that for every trip needs the theory of the
transfers, which is not complete (section "Why the gap does not close yet" of the README of 32883). So the statement
"the four machines halt together" is not proved, and no page claims it.

The rules proved for one of the four tables hold for the other three after renaming, because rules do not depend on
the start.

Reproduce (from the folder of 32883, about 12 minutes each):

    python3 py/lockstep.py 0 3 2e12    # start A against start D
    python3 py/lockstep.py 4 1 2e12    # start E against start B
    python3 py/lockstep.py 0 4 2e12    # start A against start E
    python3 py/shift4.py check 300     # every entry, n against n + 4
    python3 py/entries.py 3 2e10       # first-run length at every entry, run of 40600 (5 minutes)


<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---`](../1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B
- [`1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---`](../../bb6-1RB1RF_1LC0LB/README.md): rename A→D, B→B, C→C, D→E, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---`](../1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/README.md): rename A→E, B→D, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
