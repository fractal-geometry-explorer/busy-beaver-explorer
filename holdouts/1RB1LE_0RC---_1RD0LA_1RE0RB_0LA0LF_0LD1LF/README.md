# 1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF

bbchallenge id 174393. One of the six-state holdouts whose halting from blank tape is open.  It is a
**nested counter**: the tape is a list of blocks of the word `100` separated by `1010`, and the head's trips
inside it follow a base-4 schedule, so that between two visits of the left end the first block loses 4 words, the
second 12, the third 48, then 192, 768 (a factor 4 per level), while the last blocks grow and split.  The left end
is visited only when the whole schedule has run through, ever more rarely (the "exp" side); the right part grows
like the square root of time.  **Decoded (24 Nov 2026): the walls between the blocks are the digits of a base-4
odometer** that the head counts up by one on every trip from the right end; the drain rates follow from the digit
rules, which are proved in Lean for every block length (`lean/Odometer.lean`).  An exact macro built on them
(`py/odometer/`) follows the run from blank tape to step 10^1520 with no halt, through the run-out of the first block at visit 8,516.  Whether it halts is still open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 0RC | --- |
| C | 1RD | 0LA |
| D | 1RE | 0RB |
| E | 0LA | 0LF |
| F | 0LD | 1LF |

## What it does

At each visit of the left end in state E the tape is `E>0 a^x1 s a^x2 s ... s a^xk 10`, where `a` is the word
`100` and `s` the separator `1010` (`0` in the table is an empty block, `1010 1010`).  The C simulation
(`holdouts/1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE/c/runs.c`, `E L`, decoded with `py/blocks.py`) gives:

| step | x1, x2, ... |
|---|---|
| 2,955,223 | 49, 197, 732, 215 |
| 3,483,951 | 45, 185, 684, 408 |
| 5,575,367 | 41, 173, 636, 216, 767 |
| 10,612,511 | 37, 161, 588, 24, 1536 |
| 15,750,503 | 33, 149, 540, 0, 1272, 1055 |
| 23,036,415 | 29, 137, 492, 0, 1080, 1824 |
| 55,290,199 | 25, 125, 444, 0, 888, 1056, 3071 |
| 134,559,087 | 21, 113, 396, 0, 696, 288, 6144 |
| 295,626,887 | 17, 101, 348, 0, 504, 0, 4512, 6527 |
| 445,328,159 | 13, 89, 300, 0, 312, 0, 3744, 9600 |
| 994,374,263 | 9, 77, 252, 0, 120, 0, 2976, 6528, 12287 |
| 1,853,456,559 | 5, 65, 204, 0, 0, 0, 2424, 4320, 21120 |
| 2,595,895,687 | 1, 53, 156, 0, 0, 0, 2232, 3552, 18048, 12287 |
| 2,899,284,633 | 0, 50, 144, 0, 0, 0, 2184, 3360, 17280, 15360 |
| 3,602,018,398 | 47, 132, 0, 0, 0, 2136, 3168, 16512, 12288, 12287 |
| 5,056,527,115 | 44, 120, 0, 0, 0, 2088, 2976, 15744, 9216, 24576 |
| 12,899,988,083 | 40, 108, 0, 0, 0, 2040, 2784, 14976, 6144, 12288, 49151 |

Read down the columns: the first block loses 4 words per visit, the second 12, the third 48, the fifth 192, the
seventh 768 (position counted with the empty blocks); the last blocks grow, and a new block appears from time to
time.  Between two visits of the left end the head shuttles between the walls `s` and the right end: in the turn
points of the run, the shortest trips are repeated four times for each trip one wall further left, four of those for
each trip two walls further left, and so on, like the digits of a base-4 counter.  Each trip to a wall moves it by
one word, which is where the factors 4 come from.  When the first block runs out (step 2,899,284,633) the second
one takes its place, and every block's rate moves down one level (2136, 2088, 2040: 48 per visit; 3168, 2976, 2784:
192).

### How it could halt

The halting transition is B1.  B is entered only by `A0 -> 1RB` and `D1 -> 0RB`, so the machine halts exactly when
A reads a 0 followed by a 1 (`A>0 1`) or D reads a 1 followed by a 1 (`D>1 1`).  On the tape described above two
adjacent 1s appear only briefly next to the moving head.

## The odometer (decoded 24 Nov 2026)

Look at the tape each time the head comes back to the right end (an *R-instant*; then it is always in state D on
the next-to-last cell).  The tape is

    L a^n1 w1 a^n2 w2 ... wk a^n(k+1) 1 D>1 0          (a = 100)

and every wall `w` has one of four shapes, which are the digits of a base-4 counter.  One trip of the head adds 1:
the head runs left over every wall showing 3 (which becomes 0: a carry), changes the first wall that is not a 3 to its
next shape, and runs back.  The last wall is the least significant digit.

| wall | digit | a carry makes it | block on its left | block on its right | steps |
|---|---|---|---|---|---|
| `1010` | 0 | `0` | +1 | +1 | 19 |
| `0` | 1 | `1110` | -2 | +2 | 31 |
| `1110` | 2 | `1` | 0 | +2 | 19 |
| `1` | 3 | `1010`, carry goes on | -2 | +1 | 4 |

plus 8 steps for every word of every block the head crosses (5 going left, 3 coming back).  Over a full cycle a wall
takes 3 words from the block on its left and gives 6 to the block on its right.

- **The left end** `10` is one more digit, a binary one: a carry turns it into `00` (first block +1), and the carry
  after that is a *visit of the left end*: the head runs to the left end and back (19 steps per word), every wall
  shows 0 again, the left end is `10`, the first block gets +1.  So a period between two visits is 2·4^k trips, and
  if no block runs out the period changes the blocks by **-4, -12, -48, ..., -12·4^(k-2), +12·4^(k-1)**: the
  countdown of the table above, derived.
- **The right end.** After a visit the head arrives at the right end in E or in C, alternately (it depends on the
  parity of the number of walls).  After an arrival in C the right end grows a new wall `1010` with a block of 5
  words, so a new least significant digit appears every second visit.
- **Run-outs.** When a block between two walls empties, the two walls become one wall `(1010)^r` of r merged walls.
  It is again a base-4 digit whose four shapes change only at its two ends (`(1010)^r`, `(1010)^(r-1) 1000`,
  `1110 (1010)^(r-1)`, `1110 (1010)^(r-2) 1000`, with block changes (0,+1), (-1,+2), (0,+1), (-2,+2) and carry on the
  last), with the same totals -3 and +6; so all blocks to its right move one level down and drain 4 times slower.
  When the *first* block runs out, it and its walls fold into the left end, which shrinks back to `10` over a few
  visits while the next block becomes the first one and counts down by 4.
- **Halting.** None of these steps writes `A>0 1` or `D>1 1`.  A halt needs a local shape that has not occurred: a
  run-out of a kind not seen yet, two short blocks side by side, or the like.  The question is now about the list of
  block lengths and the order in which blocks run out, not about the machine's cells.

Lean (`lean/Odometer.lean`, 24 theorems, generated by `py/odometer_lean.py` with `tools/py/bbtools/symtm.py`, for
all block lengths and any tape `L` on the left, with exact step counts): the three digit changes of a last wall
(`last_d0`..`last_d2`) and of a double wall (`last_e0`..`last_e2`), a carry from a last wall `1` or `11101000` into
each digit (`carry_*`), the four phases of a wall of r+2 merged walls for every r (`multi_0`..`multi_3_carry`), the
left end `10 -> 00` (`left_10`) and the new wall after an arrival in C (`spawn`).  Not in Lean: the visit of the left
end itself (its sweep of 19 steps per word is a zigzag that symtm's shift-rule search does not find) and the
induction over a whole carry chain; the macro below uses the rules for every chain.

### The exact macro (`py/odometer/`)

- `l1.py`: one trip, exactly, from an R-instant to the next.  Every block longer than 32 words is replaced by one of
  48..59 words with the same length mod 12, the trip is run cell by cell, the blocks are put back with their real
  lengths plus the change, and the step count is corrected by the per-word rate measured inside each block (8 or 19).
- `macro.py`: the carry rule of each wall shape is read off one such trip in a fixed context with four block lengths
  (they must agree; otherwise the shape is a *barrier*).  `jump` finds the largest m such that the next m trips touch
  no barrier, do not overflow the left end and keep every block at 16 words or more (all monotone in m), and applies
  them in closed form, the step count included (sums over the digit orbits).  Everything else is a single `l1` trip.
- `validate.py`: against the direct simulator `c/rtrips.c`.  To 5·10^10 steps: all 160,545 trips of `l1.trip` give
  the same tape, state and step count, and the macro gives the same configuration and step count at all 31 visits
  of the left end.  Two runs with different cut-down lengths and folding thresholds (16/48 and 24/96) agree on the
  first 200 visits (to 1.5·10^43 steps).
- `far.py`: the long run.  From blank tape to step **6.435·10^1520** (1,521 digits) through 8,776 visits of the left end,
  1,261 walls at the end, no halt (`data/odometer/summary.json`, the exact last configuration is kept in the project
  files).  Past the start-up the first block ran out at visits 22 (step ~10^8), 35 and 37 (~10^11), 437 (~10^77) and
  445 (~10^78).  After that the first block (32,316 words) counted down by exactly 4 per visit and **ran out at visit
  8,516 (step 2.304·10^1476)**, as predicted: it reached 18 words, folded with its wall into the left end, which
  shrank back to `10` in six visits (`10 a^14 (10)^6`, ..., `110`, `10`), and the next block, 106,032 words, became
  the first, again counting down by 4.  Its run-out is about 26,000 visits further on.  Nothing new happened at this
  run-out: the same folding as at visits 437 and 445.  The walls met at the left-end visits are `(1010)^r` for
  r = 1..14, apart from four transient shapes right after the early run-outs (`10110` twice and two folded blocks);
  the left end is `10` at 8,698 of the visits and takes a few transient shapes while folding after a run-out.  Each
  visit now costs about 10 s of the macro (~1,000 jumps).  The log lines of visits 6,713 to 6,742 were lost when the
  container restarted (the saved state was not; they are marked `?` in the project files' `visits.jsonl`).
- `sample.py`, `page.py`: the explainer's data and sections.

## Status

Open.  Lean (kernel): the odometer rules of `lean/Odometer.lean` (above).  Computed: the exact odometer macro, no
halt to 10^1520 steps.  Earlier: the shift rules of `lean/Rules.lean` (generated by `py/rules.py`): D runs right over the words `100` of a block (turning them into `001`), F runs left over them (into `010`), E runs left over separators `10`, B runs right over `001`; each for every number of copies and any tape around.  Computed: the table above (no halt in 1.5·10^10 steps).  `lean/Blank.lean`: the halting configurations
(`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`.  C
(`tools/c/triage.c`): no halt in 1,000,000,000 steps.

## For later

- The visit of the left end in Lean: its rightward sweep (19 steps per word) needs a shift rule with a travelling word
  that `symtm.py` does not find by itself.  With it and an induction over carry chains, the period map on the block
  list would be a theorem.
- Classify the run-outs: which local shapes can occur when a block between two walls (or the first block) empties,
  depending on the digits of its neighbours at that moment.  If they are always the `(1010)^r` walls and the left-end
  folding seen so far, the machine never halts; a closed set of shapes would be the non-halting proof.
- The same kind of structure (a base-4 counter and blocks shrinking by factors of 4) is in
  `holdouts/1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE` and its twin.

## Deep exact run

No halt in the first 5.10x10^19 steps: the macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with blocks of 6 cells ran
from blank tape to step 51,038,671,798,159,773,055. It is exact, and at this block size it agrees with the
direct simulator after 2,000,013,776 steps (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/deep.py run 240`, then `verify`).

## Pages

- [`pages/holdouts/1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF/explainer.html`](../../pages/holdouts/1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF/explainer.html)
- [`pages/holdouts/1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF/proof-status.html`](../../pages/holdouts/1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF/proof-status.html)

## Check

```sh
python3 holdouts/1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF/py/odometer/validate.py 3e9     # macro vs direct, ~1 min
python3 holdouts/1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF/py/odometer/far.py 600 /tmp/far  # 10 minutes of the long run
```

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_1RC0RF_0LD0LE_1RF1LC_0LB1LE_0RA---`](../1RB0LD_1RC0RF_0LD0LE_1RF1LC_0LB1LE_0RA---/README.md): rename A→D, B→F, C→A, D→B, E→C, F→E; it is this table started in state C
- [`1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF`](../1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D

<!-- end of related machines -->
