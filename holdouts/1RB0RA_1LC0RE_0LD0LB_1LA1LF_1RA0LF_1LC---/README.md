# 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---

bbchallenge id 32883. Open. An exact **ternary counter**, least significant digit at the left end, whose digits are
pairs of long runs of alternating cells; each trip of the head from the left end and back adds one. The increment is
proved in Lean for every carry depth (kernel). When a run that the counter keeps shrinking runs out, a *transfer*
moves a long run to the right end, two cells per shuttle of the head; the shuttle is proved in Lean for every tail
and any number of shuttles (kernel), and so are the events at a run boundary. Not proved: the transfer as a whole
(it nests) and an invariant. Tapes with the residues of a real configuration but short runs do halt, so the
invariant must bound lengths from below; see "Why the gap does not close yet".

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1LC | 0RE |
| C | 0LD | 0LB |
| D | 1LA | 1LF |
| E | 1RA | 0LF |
| F | 1LC | --- |

## The tape as runs

Cut the tape into maximal runs of alternating cells (`0101...` or `1010...`): two neighbouring runs meet at a
doubled cell, `00` or `11`. So the tape is a list of run lengths, and the cells follow from the lengths (the first run
starts with 0). At the start of a trip (A at the left end of the visited tape) name the runs

    r0 r1 | x1 y1 | x2 y2 | x3 y3 | ...

Digit 0 is (r0, r1), digit k is (x_k, y_k). Its value is read from the lengths **mod 4**:

| value | digit 0 (r0, r1) | digit k (x_k, y_k) |
|---|---|---|
| 0 | (0, 3) | (2, 3), or (3, 3) while a decrement is pending |
| 1 | (2, 2) | (0, 2), or (1, 2) pending |
| 2 | (3, 1) | (1, 1), or (2, 1) pending |

("Pending": after digit k changes, x_k is one cell longer than the reading until digit k-1 next goes from 0 to 1,
which takes that cell; see the last row of the next table.) For example at step 10,000,025,550 (trip 30,932) the runs
are `82476 16507 | 82426 3897 | 36473 2653 | 33442 423 | ...`: digits 0, 2 (pending), 2, 0. Three trips later
(step 10,000,951,218) digit 0 has gone 0, 1, 2 and carried; the carry passed digits 1 and 2 and stopped at digit 3:
`82484 16511 | 82423 3899 | 36471 2655 | 33441 426 | 74 75 | ...`.

## One trip

Going right, A flips every cell it passes (`a_right`, `01 01` -> `10 10`); going left, B and C carry the pattern
one cell along (`b_left`, `c_left`). Every trip adds one to the counter:

| digit | change | runs |
|---|---|---|
| 0 | 0 -> 1 | r0 + 2, r1 + 3, x1 - 1 |
| 0 | 1 -> 2 | r0 + 5, r1 - 1 |
| 0 | 2 -> 0, carry | r0 + 1, r1 + 2 |
| k | 2 -> 0, carry | x_k - 2, y_k + 2 |
| k | 1 -> 2 | x_k + 2, y_k - 1 |
| k | 0 -> 1 | x_k - 1, y_k + 3, x_(k+1) - 1 (this is the pending decrement) |

A carry is a bounce: B meets the `00` at the start of x_k, goes back over y_(k-1) to the end of x_(k-1), turns
(B on a 1) and runs on through digit k. Where the carry stops the head turns and goes home; the left end grows by 4
cells per trip. The run lengths change by small steps, so the digit values stay readable; over one cycle of digit k
(3^(k+1) trips) x_k loses 4 cells and y_k gains 4; r0 gains 8 and r1 gains 4 every 3 trips.

## What is proved (Lean, kernel only, `lean/Counter.lean`)

The pieces of a trip, each for all lengths and every tape around it (`py/counter.py` writes them from
`tools/py/bbtools/symtm.py`):

| theorem | what | steps |
|---|---|---|
| `inc0` | digit 0 from 0 to 1: `0^inf A> (0101)^a+1 (1010)^b+1 101 10 R` | 8a+8b+26 |
| `inc1` | digit 0 from 1 to 2: `0^inf A> (0101)^a+1 01 (1010)^b+1 10 R` | 8a+16 |
| `out0` | digit 0 at 2, the carry leaves it | 4a+4b+12 |
| `carry` | the carry passes a digit at 2, `(0101)^c+2 0 (0101)^d+1 0` (e: the previous digit's d) | 4c+4d+8e+26 |
| `absorb1` | the carry stops at a digit at 1, `(0101)^c+1 (1010)^d+1 10` | 8c+12e+26 |
| `absorb0` | the carry stops at a digit at 0, `(0101)^c+1 01 (1010)^d+1 101`, next digit `10...` | 8c+8d+12e+44 |
| `home` | going home over a passed digit | 4c+4e+14 |
| `home0` | going home over digit 0; the left end grows by 4 | 4a+10 |

and chained by induction over the list of digits the carry passes: `carry_chain`, `home_chain`, and the whole trip
for **every carry depth** at once, `trip_stop1` (the carry stops at a digit at 1) and `trip_stop0` (at a digit at 0).
With `inc0` and `inc1` that is every kind of trip in the regular regime, with the exact tape after it and the exact
step count. The run-length table above is read off these statements (checked for random parameters by direct
expansion).

The minimum lengths these theorems need: r0 >= 7 and r1 >= 5 (or as in `inc0`, `inc1`), x_k >= 9 and y_k >= 5 for a
digit the carry passes, x >= 4, y >= 6 (stop at 1) or x >= 6, y >= 7 and the next digit starting `1 0` (stop at 0).

## How much of the run that covers

`py/rsim.py` is the machine on a run-length tape with the three proved sweep moves; it agrees with a plain cell
simulator on the step of all 17,669 trip starts in the first 4·10^9 steps. Classifying every trip start in the first
3·10^12 steps (726,270 trips): 725,254 (99.86%) are one of the four proved kinds (242,079 `inc0`, 242,079 `inc1`,
120,552 stop at 0, 120,544 stop at 1; `py/classify.py`). The other 1,016: the carry reaches the right end (98), a
run is too short for the theorems (269), or a digit has residues outside the table (648), and one is the first trip.
They belong to the irregular events of the next two sections.

## The events at a run boundary (Lean, kernel, `lean/Transfer.lean`)

Both passes flip every cell they cross (going right A0→1, B1→0, E0→1, A1→0; going left B0→1, C1→0), so the list of
runs changes only where the head turns or crosses a boundary going left. Write e for the number of cells of a run
that A crosses starting on a 0 (the run's length, minus one if the run starts with a 1, which A just erases). For
every surrounding tape:

| theorem | going | case | what happens |
|---|---|---|---|
| `loc_pass0` | right | e = 0 mod 4 | A takes the first cell (a 1) of the next run and goes on |
| `loc_pass3` | right | e = 3 mod 4 | A starts afresh on the first cell (a 0) of the next run |
| `loc_turn1` | right | e = 1 mod 4 | the head turns; the run is 1 longer, the next run 1 shorter |
| `loc_turn2` | right | e = 2 mod 4 | the head turns; the next run loses its first cell |
| `loc_cross` | left | B on a 0 with `0 1 0 1 0` to its left | the head goes on; the doubled cell moves 2 cells left |
| `loc_bounce` | left | C on a 1 with a 1 to its left | the head turns right (this is the carry's bounce); the left run loses its last cell |
| `loc_halt`, `loc_halt_stops` | left | B on a 0 with `1 1 0` to its left | F reads a 1 three steps later: **halt** |

The last line is the only way to halt: a run `1 0` of length exactly 2 between a `11` and a `00`, met from the right.
(Left runs of length 1 and 3 before a `00` behave differently again and are not in the table.)

## Transfers

x_k loses 4 cells per cycle of its digit, so it runs out. When a carry arrives at a digit whose x-run is down to 2
cells, the bounce does not go through: the head **shuttles** between the right end of y_(k-1) and the right end of
the tape. Example, the trip that starts at step 22,430 with `187 97 2 31 25 7 7` (`py/runs.py trace "187 97 2 31
25 7 7"` prints every turn):

    186 97 1 [A] 33 24  7  7        first shuttle: A enters the tail on a 1, i.e. with the phase shifted by one
    186 95 1 [A] 36 23  7  7        each shuttle takes 2 cells from the run 97 ...
    186 93 1 [A] 36 26  6  7        ... and turns at the first run of the tail that is not yet "saturated"
    186 91 1 [A] 36 29  5  7
    186 89 1 [A] 36 29  5  7  7     the right end makes a new run
    186 87 1 [A] 36 29  5 10  6
    186 85 1 [A] 36 29  5 13  5
    186 83 1 [A] 36 29  5 13  9     saturated: from here on only the last run changes, + 4 per shuttle
    ...
    186  1 1 [A] 36 29  5 13 173
    186 43 27 5 13 177               next trip start: the run 97 is gone, the digits are paired anew

(`[A]` stands for the head's cell, a 1, which is the first cell of the run written after it; the `1` before it is
a single 0 cell.) A run of the tail is
**saturated** when it starts with a 1 and its length is 1 mod 4 (`1 (0101)^a`): by `loc_pass0` A crosses it and
arrives at the next run in the same way. A run that starts with 1 and has length 2 mod 4 turns the shuttle once
(`loc_turn1`) and is then saturated (length + 3, the next run − 1); length 3 mod 4 takes two shuttles. At the right
end `7` becomes `7 7`, `10 6`, `13 5`, `13 9`, and then grows by 4.

**The shuttle lemma (Lean, kernel).** For every list of saturated runs `1 (0101)^(a_i+1)` (each at least 5 cells),
every last run `1 (0101)^z`, every m and every tape L to the left:

    L (10)^m 0 A> 1(0101)^(a_1+1) ... 1(0101)^(a_n+1) 1(0101)^z 0^inf
      -->  L 0 A> 1(0101)^(a_1+1) ... 1(0101)^(a_n+1) 1(0101)^(z+m) 0^inf

in exactly m (2S + 8z + 8) + 4m(m − 1) steps, S the total length of the n runs: 2m cells leave the moved run, 4m
arrive at the right end, nothing in between changes. `shuttle` is one shuttle (pieces `sh_right`, `sh_end`,
`sh_left`, `sh_turn`, chained by induction over the list in `right_chain`, `left_chain`, with the re-bracketing
`back_runs`); `shuttles` is the induction over m and `scst_eq` the step count. `py/transfer.py` writes the file.
Against a plain cell simulator: 200 of 200 random cases; five mutated statements (wrong z, step count, m, a longer
run, an unsaturated run) fail in 40 of 40 cases each (`py/validate.py`); in the real run the shuttle from step 1948
to 2156 of the trip above (runs 37 29 5 13, z = 4) takes 2·84 + 32 + 8 = 208 steps.

What is **not** a theorem: the shuttles before saturation as one rule for an arbitrary tail, the first and the last
shuttle (how the transfer is entered and how the digits are paired afterwards), and these complications, all seen
in the real run:

* **Transfers nest.** A shuttle of an outer transfer can turn at an inner run and become a complete inner
  transfer. Trip 2,225,395 (it ends at step 23,871,965,983,406) starts `... 93 109 2 31 21614 4 13 2824993`: the
  outer transfer moves the run 109 (about 55 shuttles); after five of them an inner transfer moves all of 21614
  (10,807 shuttles); then the outer one finishes, its last 44 shuttles saturated.
* **Merges.** A carry that arrives at an x-run of 1 cell joins three runs: `340 39 1 201 9 217` → `342 243 9 217`.
* After a transfer the pairs (x_k, y_k) have residues outside the table above (`186 43 | 27 5 | 13 177`) and return to
  it within a few carries. Over the first 10^14 steps the pairs take 14 of the 16 residue classes mod 4, and digit 0
  is at (2,3) or (3,2) for 16 trips each.

**The right end is the same counter one level deeper** (observed). The runs after a freshly deposited run go
through exactly the states the whole tape went through from the start: after trip 143 (`378 239 519`) the runs after
position 3 are `7`, `7 7`, `6 7`, `11 5`, ..., the first 125 states of the runs after position 1 from trip 1 on;
the same holds after position 5 from trip 571 (69 states) and after position 9 from trip 7,088 (35 states), three
times slower per level. So there is no separate right-end mechanism to describe; what is missing is the transfer.

## Do nearby tapes halt? Yes

The method of the sibling proofs (keep long counts free, track remainders, close the set) starts with this test.
`py/runs.py` builds a trip start from a list of run lengths (checked against the real run: 14,387 consecutive trip
starts, same next list and step count).

| change to a real trip start | tapes that halt |
|---|---|
| one run ± 2 (not the last two runs) | 90 of 2,510 (3.6%) |
| one run ± 1 (shifts the phase of everything to its right) | 74 of 1,698 (4.4%) |
| one run ± 4, ± 8, − 12, ± 40 | 1 of about 10,000 (a run of 5 cells cut to 1) |
| every run ≥ 8 replaced by a random length of the same residue mod 4, 8 to 56 | 0 of 1,834 |
| every run ≥ 4 replaced by the *smallest* length ≥ 4 of its residue | 20 of 2,692 |
| the same with 5 / with 6 (first 6,000 trips) | 13 of 3,114 / 2 of 3,463 |
| the same with 6 / 8 / 10 / 12 / 16 (all 14,388 trips of the first 10^9 steps, `py/minimal_test.py`) | 3 of 7,119 / 0 of 9,155 / 0 of 9,908 / 0 of 10,513 / 0 of 11,209 |

(Each tape is run for 20,000 to 100,000 moves of the run-length simulator, a move being a step or a whole sweep
of a run; "does not halt" means within that budget.) So the residues mod 4 are essential, and the lengths are
almost, but not quite, free: tapes with exactly the residues of a real trip start halt when several runs are at
their smallest values at once. With every long run at 8 to 11 cells none halted. Two examples, confirmed step by step on
a plain simulator (`py/validate.py`):

* `6 6 4 6 5 5 5 5 6 7` (the real `3106 1606 56 506 429 93 5 29 26 7` shortened) halts at step 5,943 after 27
  trips. Several x-runs are down to their minimum together, so transfers at different levels follow each other
  closely; one of them moves a run of only 13 cells, ends before the tail is saturated and leaves a last run of 5
  cells; later carries shrink it to 2, and the next transfer meets `... 18 2` and halts.
* `6 6 2 7 9 6 6 7 7 7 5` (the start of the real transfer at trip 2,205, `5870 1790 2 511 3425 326 110 39 23 11 5`,
  shortened) halts at step 1,005. With the real lengths elsewhere it halts only if the moved run 1790 **and** the
  run 326 are both cut to 6 cells; 10 cells for either is enough to avoid it.

A tape built from the digit table above alone can halt as well (`py/small_halts.py`: 56 of 3,456 two-digit tapes
at short lengths, the smallest `4 7 1 6 2 7`, which has an x-run of a single cell; none of 729 one-digit tapes).

## Why the gap does not close yet

1. **No invariant on residues alone.** A closed set of the kind "these residue patterns, all long runs free" does
   not exist in the simple form: the shortened tapes above have the residues of real trip starts and halt. An
   invariant has to bound lengths from below, and the bound is not a constant per run: in a transfer the moved run
   must outlast the saturation of the tail, and the number of shuttles that takes grows with the tail (up to 2 per
   run, plus whole inner transfers).
2. **A regular invariant did not stabilise.** Abstracting each run to its length if shorter than 8 and to its
   residue mod 4 otherwise, the set of windows of 3 consecutive runs at trip starts has 263 members after 10^14
   steps; new ones still appear at 1.4·10^12, 1.6·10^12 and 3.9·10^13 steps, each time a transfer happens in a new
   phase. A closed-tape-language search on windows of K runs (`py/closure/runcps.py`; the automaton format of
   `tools/lean/TM/CTL.lean`) reaches a halting abstract configuration for K = 2, 3 (thresholds 4 to 8) and
   exceeds 3 million configurations for K = 4: windows of runs forget which phase the far part of the tape is in.
3. **What holds in the real run** (`py/monitor.py`, every trip of the first 10^14 steps, 3,153,668 trips, 7
   minutes): no halt; D reads a 1 with a stretch of 2 cells 218 times and of 3 cells 21 times, never of 1; there
   are 168 transfers or nested levels of transfers with at least 3 shuttles, and every one ends with saturated
   shuttles (condition Q: at least 6, in the 84 replays of the first transfer `31 17 2 7`, which has 9 shuttles; at
   most 20 unsaturated shuttles in a level, 60 in one level that contains two inner transfers). Heuristically the moved
   runs are long because a y-run gains 4 cells per cycle of its digit while the x-run to its right, three times
   slower, has to lose all of its cells before the transfer happens.
4. **What a proof needs.** (a) The transfer as a rule: the shuttles before saturation are a second counter-like
   action on the tail (each shuttle changes one run by the `loc_` rules above), including nesting and merges, and the
   entry and exit; (b) the regular trips for the residue classes that occur after a transfer (the 648 trips above);
   (c) an invariant that says which lists occur, with the lower bound of point 1 in it, i.e. a statement that
   relates the length of each y-run to the size of the tail behind it; (d) its preservation by all of these. The
   self-similarity of the tail suggests an induction over levels. None of (a) to (d) is done; the smallest
   counterexamples show that (c) cannot be dropped.

Can the real run reach one of the halting tapes above? Not by anything seen: they need two or more long runs at
5 to 13 cells at the same time, while in the real run the moved run of every transfer of the first 10^14 steps is at
least 2·(unsaturated shuttles) + 12 cells long and the larger ones are thousands of cells long. That is evidence,
not a proof.

## Halting

The only halting transition is F on a 1. F comes from E on a 1 (after B wrote a 0 just left of it, so F reads that 0)
or from D on a 1, and D only from C on a 0. So the machine halts exactly if D reads a 1 whose left neighbour is a 1:
C, moving left, meets `1 1 0` (`loc_halt`). Call k the length of the alternating stretch that ends at D's cell; a
halt needs k = 1. In the first 10^14 steps D read a 1 63,281,275 times: k = 2 218 times, k = 3 21 times, never
k = 1. The regular trips cannot halt: the theorems above give their whole run.

## Status

Open. Kernel: halting configurations, 10,000 steps, the sweep moves (`lean/Rules.lean`), the counter's increment
for every carry depth (`lean/Counter.lean`), the run-boundary events and the shuttle lemma for every list of
saturated runs and every number of shuttles (`lean/Transfer.lean`). Native: 10^7 steps. Trusted: no halt in the
first 10^14 steps (3,153,668 trips, 23,850,932 cells, `py/rsim.py`); nearby tapes that halt (`py/validate.py`).
Heuristic: the counter reading, the description of transfers, nesting, merges, the self-similar right end,
condition Q.

## For later

* The saturation phase as a rule: a transducer over the list of runs (per run: residue and first bit decide 0, 1 or
  2 turning shuttles and what the next run loses), with the nested case, then entry and exit of a transfer.
* The regular trips for the residue classes that follow a transfer (same generator as `py/counter.py`).
* The invariant of point 4(c); a first step is to measure, per level, the moved run against the number of runs and
  the inner moved runs behind it over a long run (`py/monitor.py` has the per-level numbers).
* The closed-language search with a sharper abstraction (keep the phase of the far tape, e.g. the last state that
  crossed each run): real tapes with every long run cut to 8 to 11 cells never halted in the test above, so a
  regular invariant with "long" meaning 8 or more is not excluded.

Working notes with every step and number: `/mnt/project-files/g09-ternary/notes.md` (outside the repository).

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.554; right: sqrt,
exponent 0.389). After 1,000,000,000 steps: 76,685 cells visited (39,628 left of the
start, 15,538 right), 38,338 ones.

- left, step 976,307,423: `B>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 991,943,199: `B>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 929,547,037: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 976,138,013: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 256,006,223 | 39,174 | 12 | 11 | 23 | 0.53 |
| right | 265,795,225 | 39,814 | 9 | 12 | 21 | 0.53 |
| left | 1,024,016,481 | 77,665 | 9 | 11 | 20 | 0.50 |
| right | 1,041,212,414 | 78,337 | 11 | 11 | 22 | 0.50 |
| right | 4,096,159,323 | 149,238 | 13 | 11 | 21 | 0.59 |
| left | 4,418,528,067 | 152,708 | 14 | 9 | 20 | 0.57 |
| left | 16,384,274,375 | 335,797 | 9 | 15 | 24 | 0.39 |
| right | 16,609,519,102 | 337,953 | 15 | 15 | 27 | 0.40 |

**Proposed family: F06, block-list counters** (blocks of pairs with a base-3 counter, as in 1RB1RF_1LC0LB… (same table)).

The description grows slowly: 20 to 27 level-2 tokens at every record from 2.6·10^8 to 1.7·10^10 steps, and 12 to 47 runs in the macro simulator (blocks of 4 cells) at the sampled records up to 2·10^16 steps.

The machine shares its table with 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- (states renamed, some of the four mirrored; `related.json`), started in another state. On the screen the four runs show the same list of blocks at the same moments. For example near step 6.4·10^7 all four tapes read (mirrored) blocks of 3, 1,546, 39, 1,753, 117, 1,467 and 997 pairs `01` and then a last block, of 4,405 pairs in 1RB1RF_1LC0LB… and of 4,407 pairs here. The four last blocks differ by 2, 4 and 6 pairs and the records come at slightly different steps. This is an observation at the sampled records: it is not a proof that the runs correspond, and nothing about halting is carried over.

For 1RB1RF_1LC0LB… the right end is proved in Lean to be a base-3 counter on the separators of such a list (`bb6-1RB1RF_1LC0LB/lean/Counter.lean`). Those theorems are about that machine's table with its own state names; they apply here only after the renaming is carried through, which has not been done. A list of blocks with a base-3 counter is F06.

Next step: Carry the renaming through, so that the counter theorems of 1RB1RF_1LC0LB… become theorems about this machine, and state exactly how the two tapes differ (the last block and the left end).

## Pages

- [`pages/holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/explainer.html`](../../pages/holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/explainer.html)
- [`pages/holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/proof-status.html`](../../pages/holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/lean/check.sh
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/counter.py > /tmp/Counter.lean   # regenerates lean/Counter.lean
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/transfer.py > /tmp/Transfer.lean   # regenerates lean/Transfer.lean
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/validate.py                      # 2 minutes: tools vs the real run, mutations, halting tapes
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/runs.py trace "187 97 2 31 25 7 7"   # a transfer, turn by turn
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/monitor.py 1e14 /tmp/mon.json     # 7 minutes: transfers, windows, D reads
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/minimal_test.py 1e9 30000 6 8    # 8 minutes: shortened real tapes
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/small_halts.py 2                  # tapes from the digit table
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/closure/runcps.py 3 6            # closed-language search on windows of runs
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/rsim.py 1e12 100000
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/classify.py 3e12   # about a minute
gcc -O2 -o ev holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/c/ev.c && ./ev 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- 2000000000 L B 1 100000 12 | awk 'NR%100==0'
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---`](../../bb6-1RB1RF_1LC0LB/README.md): rename A→B, B→C, C→E, D→A, E→D, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---`](../1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---`](../1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E

<!-- end of related machines -->
