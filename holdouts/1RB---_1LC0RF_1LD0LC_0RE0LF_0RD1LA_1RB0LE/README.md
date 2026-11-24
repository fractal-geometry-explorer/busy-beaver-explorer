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

**Open.** A bouncer between a growing block and a wall of exactly 1,573 cells that is a counter. The counter is now decoded (section "The digit carry rule"): 46 digits of 25 cells, 15 trips of the head per sweep, and a carry table of 73 entries that reproduces every sweep to 2·10^10 steps; Lean proves that this table never needs an entry it does not have. Carries reach each further digit 3/8 as often, so they reach the end of the wall only after about 10^38 steps; what happens then is the open question. It shares its halting question with 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC, proved in Lean (section "One halting question for two machines").

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
- Lean (`lean/Lockstep.lean`, `lean/RightEnd.lean`): the run of 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC is this run with one word more at the right end, and the two machines halt together or not at all (below).
- The digit carry rule (`py/carry.py`, `lean/Carry.lean`, `py/endregion.py`): see the section below. The table is checked against the machine by simulation; its rules are not yet proved for the machine.

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

## One halting question for two machines (F09, 16 November 2026)

1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC is the table of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE read in a
mirror with the states renamed, started in state C. The two runs are one run, shifted. After 2 and 49 steps both are
at `C>1 1` on blank tape, except that the second run has the word `10001101` once more at the right end. From then
on, at every visit of the head in state C to the left end of the tape, the second tape is the first followed by
`10001101`: 270,284 visits in the first 10^11 steps of each run. The right end of the tape is made of these words, and in the second run there is one more of
them.

`lean/Lockstep.lean` (kernel only: `propext` and `Quot.sound`) proves why this is so. Its generated part is
`lean/FarEnd.lean`, written by `py/farend.py`. `Rel k n c c'` says that `c'` is `c` with k words `10001101`
inserted just right of a cell q, n cells right of the head, with blank tape beyond q in `c`. Every step keeps the
relation unless the head moves right from cell q. When the head moves right from q in state B, on a 1, it crosses
the k words and comes back one cell left of q in D, with `1 0 1` from q on and the k words after them. This takes
44k + 5 steps, for every k (`far_B`). The cell q then moves two cells to the right. Any other move right from q is
the excluded case (`Bad`). `trk` runs 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE and keeps track of n. The renaming
and the mirror are proved too (`halts_114265`). So:

* **`two_machines`**: suppose that in the run of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE from blank tape, after
  its first 2 steps, the head moves right from cell q only in state B on a 1. Here q is the rightmost cell visited
  so far (`Good30773`). Then 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE halts from blank tape if and only if
  1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC does.

**Proved (16 November 2026): the condition holds.** `lean/RightEnd.lean` (kernel only: `propext` and
`Quot.sound`) proves `Good30773` for every number of steps (`good30773`). It looked like a statement about the
rebuilds of the counter, but it is a local fact about the last four cells of the tape, q-3 to q. Keep only those four
cells and the state and forget everything left of them: with the head inside the window, the state, the cells left
of the head inside the window and the cells from the head to q; with the head further left, the four cells only, and
let the head come back in any state that a move right can produce (B, D, E or F). From step 2 on this
over-approximation has exactly 32 abstract configurations (30 with the head in the window, 2 outside it; whenever the
head is left of the window, the last three cells read `101`). None of the 32 moves right from q except in state B on
a 1, and the set is closed under a step (`closed`, by `decide`). `py/rightend.py` computes the 32. So:

* **`two_machines'`**: 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE halts from blank tape if and only if 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC does. No condition.

Before the proof, the condition was checked in the first 10^11 steps (`c/good.c`): the head moves right from q only
100 times, all before step 4.5·10^6, during the first rebuilds of the counter.

The note `F09-same-table-pairs.md` called this pair "not a shift". Its tapes differ in about 1,330 cells at the
counter end only when the two runs are compared at the same step. Compared at matching visits, they differ by one
word.

Reproduce (from the folder of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE):

    . /etc/profile.d/lean.sh && lean/check.sh
    python3 py/farend.py check                     # far_B by simulation for k = 0..4
    python3 py/rightend.py check                   # the 32 abstract configurations of RightEnd.lean
    gcc -O2 -o good c/good.c && ./good 1e11        # the condition (about 8 minutes)
    gcc -O2 -o lockstep c/lockstep.c && ./lockstep 1e11   # the two runs at every left-end visit (about 17 minutes)

### A second proof, in Coq (busycoq)

[`coq/Eqv_TailWord.v`](coq/Eqv_TailWord.v) proves the same equivalence on top of busycoq's definitions,
`TailWord.eqv : halts tm c0 <-> halts tm' c0`, independently of the Lean files: a model configuration read as a
configuration of either machine (the second with `10001101` after q), one model step = one step of both or the
far-end crossing (5 and 49 steps), and a window invariant of 28 abstract configurations checked by one `vm_compute`.
`Print Assumptions`: closed under the global context. It compiles in about 3 s with Coq 8.20.1, busycoq's version
(`sh coq/build.sh /path/to/busycoq` on busycoq's BB6 branch; [`coq/build.log`](coq/build.log)), and
with 8.18.0. It is ready for a pull request to busycoq, not yet submitted.

The explainers of both machines now walk through the argument with interactive parts: the two tables cell by cell,
the two runs drawn on one clock, the far-end crossing for k = 0..4 extra words, and the 28 window configurations
(follow the real run through them, or flip one transition and watch the check fail). Their engine,
[`py/pair/pair.js`](py/pair/pair.js), is tested by `node py/pair/test_pair.js` against the numbers
above; `python3 py/pair_page.py` writes the sections into both `status.json` files.


## The digit carry rule (F09, 24 November 2026)

**The wall, cell by cell.** From step 2·10^7 on, at every sweep,

    W = H  D_0 D_1 … D_45  E  (10001101)^30
    H    01100011000110001100110011010110011011100110      44 cells, the same at every sweep
    D_j  a110 b110 c011 0011 0d11 0e11 0                    25 cells: digit j, five free cells a b c d e
    E    139 cells, the same at every sweep so far (more counter, not yet used: below)

A digit is written below as its five free cells `abcde`. Of the 32 values, 28 occur.

**A sweep is 15 trips.** Between two visits to the left end the head goes from `H` into the digits and back to
cell 32 of `H` (12 cells left of digit 0) exactly 15 times. At the start of trip number p (p = 0 … 14) the cells of `H` are the same at every
sweep, so `H` is a fixed sequencer of 15 phases: trip p feeds carry **Y** into digit 0 if p is 1, 6 or 11, and
carry **X** otherwise. A carry reaching a digit rewrites it and passes a carry on to the next digit, or stops.
Five carries occur, X, Y, P, Q and R, and the whole rule is one table of 73 entries (`d > d'` for "the carry turns
d into d' and stops", `d > d':c` for "… and passes c on"):

| carry | entries |
|---|---|
| X | `00001>10001 00010>10010 00011>10011 00100>10100 00101>10101 00110>10110 01000>11000 01001>11001 01011>11011 01101>11101 01110>11110 01111>11111 10000>01000 10001>01001 10010>01010 10011>01011 10100>01100 10101>01101 10110>01110 10111>01111 11000>00100 11010>00110 11011>00111 11101>00010:Y 11111>00001:X` |
| Y | `00001>01001 00010>11111:P 00110>01110 00111>11010:P 01000>00100 01010>10000:X 01100>10111:Y 01111>00001:X 10001>00101 10011>11011 10100>00011:Y 10101>11101 11000>10100 11001>01101 11101>10010:Y 11110>01000:X` |
| P | `00001>00101 00011>11011 00100>00011:Y 00101>11101 01000>10100 01001>01101 01101>10010:Y 01110>01000:X 10000>00100 10010>10000:X 10100>10111:Y 10111>00001:X 11010>01110 11011>11010:P 11101>11111:Q 11111>01001:X` |
| Q | `00001>01101 00110>01000:X 01000>00011:Y 01111>00101:X 10011>11010:P 10101>11111:Q 11000>10111:Y 11101>10000:R` |
| R | `00001>11001 00110>11110 01000>10100 01111>10001:X 10011>00111 10101>00010:Y 11000>01100 11101>01010:Y` |

Carry X is plain binary counting in `a b c` (a lowest): it sets the lowest 0 and clears the 1s below it. When
`a = b = c = 1` the digit overflows to `a b c = 0 0 0`, and `d e` steps from 11 to 01 (passing X on) or from 01
to 10 (passing Y on). The other carries add more at once (Y mostly 2 or 3 to `a b c`, P 3 or 4, R always 3) and
move `d e` along when `a b c` overflows. We looked for a value of each digit, and an amount for each carry, that
every entry conserves, as in a numeral in base 8/3: for no base between 1 and 10^4 do the 73 linear equations
have a solution. So the counter is a finite transducer, not a numeral in a base.

**Checks** (`python3 py/carry.py trips|check|far|closure`):

* trip by trip, simulating the machine: all 4,500 trips of the first 300 sweeps are the table, and `H` is the same
  at the start of trip p of every sweep;
* sweep by sweep: the table predicts all 29,299 sweeps from step 2·10^7 to 2·10^10 (from the walls of
  `c/walldump.c`); in all of them `H` and `E` do not change;
* as a model, 10^6 sweeps from the wall at 2·10^10: every one of the 73 entries is used and no other is needed;
  the carries reach digit 17 once;
* **closure**: take the strings of digits whose first digit is in a set F_p (8 values for each trip number p) and
  whose neighbouring digits are among 240 allowed pairs. Trip p maps them into the strings of trip p+1 and never
  meets a pair (carry, digit) outside the table. **Lean** (`lean/Carry.lean`, kernel only, `decide`) proves this for
  strings of every length (`trip_good`), and that the model started from the 46 digits of the wall at step
  20,018,306 never gets stuck, for any number of trips, until a carry runs off the last digit
  (`wall0_never_stuck`). This is a theorem about the model; its link to the machine is the simulation above.

**How deep the carries go.** In the model, 3/4 of all trips change digit 0 only, 1/4 reach digit 1, 29/320 reach
digit 2, 43/1280 reach digit 3, and from there on each digit is reached by 3/8 of the trips that reach the one
before (ratios 2.6667 ± 0.001 from digit 4 to digit 10, in 1.5·10^7 trips). That is why the first k digits have
period exactly 8^k sweeps while deep changes are only 8/3 times rarer per digit. The carries pass digit 45 in
about one trip in (1280/43)·(8/3)^43 ≈ 6·10^19, which is about 4·10^18 sweeps and, with the block one word longer
every sweep, about 10^38 steps. That is when the end of the wall is first used.

**What the end of the wall does with a carry** (`python3 py/endregion.py`, an experiment on made-up walls). Set
digits 1 … 45 to `11111` (X turns each into `00001` and passes X on), run one sweep, set them back, and repeat.
The first carry only turns cell 0 of `E` from 0 to 1; the next ones count in binary in cells 0, 4, 8 of `E`, like
`a b c` of a digit: `E` begins with more digits in a form not used yet. At the 56th carry `E` is rewritten as a
whole, two more words `10001101` stand at the right end, and the right end moves 8 cells (the crossing `far_B` of
`lean/FarEnd.lean`). No halt in 400 such carries. Real carries arrive in the five kinds and from digits that are
not all `11111`, so this shows the kind of thing the end does, not what the run will do.

**Earlier counters.** The present counter is the fourth. Before it the right end moved nine times, and three times
the block was turned into a new counter: at about 3,200 steps (block of 7 words), 66,700 steps
(11 words) and 4.49·10^6 steps (246 words, which became the 45 equal fresh digits
`0101100110111001100110111` of the present wall). The last change began at step 1,445,347, when the head came back
to the left end in state D instead of C, having gone only about 30 cells into the old wall: the old counter
ended at its low end, not at its far end. The present counter cannot end that way as far as we can see: `H` is
the same at every sweep. Whether a carry reaching the far end can make the head turn the block into a fifth
counter, and whether that can go wrong, is the next question.

**Next steps.** (1) Prove the 73 entries for the machine (each is a finite run on one or two digits, but the head
crosses a cell up to 27 times in one trip, so the interface between digits needs care); with `trip_good` that gives
"no halt before a carry reaches E". (2) Decode `E` and the tail as digits, and find what ends a counter.

Reproduce (from this folder):

    python3 py/carry.py trips 300      # 4,500 trips, machine vs table (dumps the walls to 3·10^9 first, 15 seconds)
    python3 py/carry.py check          # 29,299 sweeps to 2·10^10 (dumps the walls first, about 2 minutes)
    python3 py/carry.py far 1e6        # the model alone (15 seconds)
    python3 py/carry.py closure        # the closure check
    python3 py/carry.py lean > lean/CarryData.lean
    . /etc/profile.d/lean.sh && lean/check.sh
    python3 py/endregion.py            # the end of the wall under 400 forced carries

## Pages

- [`pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/explainer.html`](../../pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/explainer.html)
- [`pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/proof-status.html`](../../pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/lean/check.sh
python3 holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/py/farend.py check                    # far_B by simulation, k = 0..4
python3 holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/py/rightend.py check                  # the 32 configurations of RightEnd.lean
python3 holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/py/carry.py trips 300                   # the carry table, trip by trip against the machine
python3 holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/py/carry.py check                       # the carry table, all sweeps to 2*10^10 (about 2 minutes)
python3 holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/py/farend.py > /tmp/FarEnd.lean       # regenerates lean/FarEnd.lean
gcc -O2 -o good holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/c/good.c && ./good 1e11            # the condition of Lockstep.lean, about 8 minutes
gcc -O2 -o lockstep holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/c/lockstep.c && ./lockstep 1e11   # the two runs at every left-end visit, about 17 minutes
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. In the first 10^7 steps of each, no configuration of this machine's run occurs in the other's at the same step, even up to a shift of the tape. Compared at matching visits instead, they are one run seen in a mirror, the second with one more word at the far end, and it is proved that the two halt together or not at all (Lean: `two_machines'`, Coq: `TailWord.eqv`; see the section "One halting question for two machines"). So these two are one halting question.

- [`1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC`](../1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
