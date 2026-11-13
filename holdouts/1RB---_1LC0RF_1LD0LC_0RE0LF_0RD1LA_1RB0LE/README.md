# 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE

bbchallenge id 30773.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1LC | 0RF |
| C | 1LD | 0LC |
| D | 0RE | 0LF |
| E | 0RD | 1LA |
| F | 1RB | 0LE |

## Status

**Open.** A bouncer between a growing block and a wall of exactly 1,573 cells that changes every sweep like a counter (changes start at cell 44, carries reach 25 cells further about every three times as many sweeps); what happens when the carries reach the end of the wall is unknown.

## What it does

Once per sweep the head, in state C, is at the left end and the tape is

    C>0 (01101)^n  W          W: exactly 1,573 cells, every sweep (after 2·10^7 steps)

The block `(01101)^n` grows by about one word per sweep (n = 476 at 1.2·10^7 steps, 9,476 at 2·10^9, 29,726 at
2·10^10), and the right end of the tape never moves: `W` is a **wall of fixed length**. It is different at every
sweep (10,821 different walls between 2·10^7 and 3·10^9 steps), and `py/wall.py` shows how: comparing consecutive
walls, the changes always start at cell 44 of W and usually stop within a hundred cells, but now and then reach
further, and the deepest change so far moves out in steps of 25 cells at sweeps 274, 406, 2,296, 7,335, 20,772
(cells 252, 294, 319, 344, 369). That is the behaviour of a **counter written in the wall**, with digits about 25
cells wide and a base near 3 (each new depth is reached about three times later).

If that is right, the carries reach the end of the wall (cell 1,573, about 48 more digits) only after something
like 3^48 sweeps, far beyond any simulation, and what the machine does then (grow the wall, or halt) decides the
question. Decoding the digits would turn this into an exact statement.

## Results

- `py/view.py` (with `c/blocks.c`, `c/gaps.c`) prints the views of the run quoted above; `python3 py/view.py 2e10 3000` is the block view at the left end; `python3 py/wall.py 2e10` (with `c/walldump.c`) compares consecutive walls.
- Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.
- No macro rule is proved yet. Next step: decode the wall as digits, prove the increment with symtm, and work out what the carry does at the end of the wall.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.494; right: fixed,
exponent 0.0). After 1,000,000,000 steps: 34,610 cells visited (25,368 left of the
start, 201 right), 20,724 ones.

- left, step 972,937,536: `C>0 0^3 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^`
- left, step 988,768,470: `C>0 0^3 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^`

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 256,082,924 | 17,886 | 211 | 54 | 164 | 0.91 |
| left | 1,024,109,487 | 35,011 | 184 | 43 | 146 | 0.95 |
| left | 4,096,593,925 | 69,161 | 207 | 50 | 163 | 0.98 |
| left | 16,384,808,833 | 137,401 | 207 | 54 | 176 | 0.99 |

**Proposed family: F06, block-list counters** (a counter in a wall that is rebuilt longer at each overflow, with a growing block as its clock).

During the present epoch the description of the tape does not grow: 146 to 176 level-2 tokens at the four left-end records from 2.6·10^8 to 1.6·10^10 steps, and in the macro simulator (blocks of 5 cells) exactly 314 runs at each of 80 sampled left-end records from 3·10^7 to 10^16 steps. Only the block `(11010)^n` grows.

The wall is a counter with digits of 25 cells. After its first 44 cells, each of the first 40 digits has the form `x110 x110 x011 0011 0x11 0x11 0` at every one of 2,819 sweeps (steps 2·10^7 to 3·10^8): five free cells per digit. The first digit returns to the same contents every 8 sweeps, the first two digits together every 64 sweeps and the first three every 512 sweeps, taking 8, 64 and 512 different values (`py/digits.py`). The deepest digit changed by a sweep is digit 2 on 1,336 sweeps, digit 3 on 782, digit 4 on 326, digit 5 on 124, and so on down to digit 11 once.

The counter has overflowed before. At the left-end record at step 1,428,412 the tape was `(11010)^244` followed by about 240 cells that end in 16 eight-cell words. No new cell was added at the left end for the next three million steps, and at the next left-end record (step 4,487,735) the block was gone, a 25-cell word `0101100110111001100110111` stood 45 times in a row (new digits, all equal) and the tape ended in 30 eight-cell words. So the machine is a counter that is rebuilt longer when it overflows, with the block as its clock, and the next overflow is far beyond simulation. That is the shape of the counter families (F06), not of a bounded engine (F01): the wall is bounded only within an epoch.

Next step: Decode the five cells of a digit into a carry rule (a transducer on digits), prove it with `symtm`, and work out the rebuild; then the question is whether the rebuild can go wrong for some length of the block.

## Pages

- [`pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/explainer.html`](../../pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/explainer.html)
- [`pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/proof-status.html`](../../pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC`](../1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
