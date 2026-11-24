# 1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA

bbchallenge id 149962, group G08, family F08 (a counter beside a chaotic edge). Whether it halts from blank tape is
**open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LC | 0RE |
| C | 1RA | 1LD |
| D | 1LA | 1LC |
| E | 1RF | 0RA |
| F | --- | 0LA |

## What it does

**A small irregular zone at the left end, and a long regular body.** At the left end of the tape sits a *zone* of
about 300 to 500 cells with no visible order. Everything right of it, all the way to the right end, is one word of
period 10, `1011011011` (seen at rest), repeated: at step 10^9 the body is 19,860 of the tape's 20,246 cells. The head
shuttles between the zone and the right end:

- A **round trip** goes from the zone out through the body to the right end, adds one cell there and comes back. On
  the way the body is rewritten into two other forms of the same word and back, and it ends up shifted right by one
  cell. Lean proves that a round trip gives the same cells next to the zone **whatever the length of the body**
  (`trip`: 70n+143 steps through n+1 words), using one crossing rule each way (`body_right`, 58 steps a word with
  the word `010` travelling along; `body_left`, 12 steps a word).
- Between round trips the head works inside the zone. Now and then it extends the tape on the left: from step 554
  on, always in bursts of exactly 30 new cells (30, 60, 90 or 120). From step 664,330 on, the right end grows in
  bursts of a multiple of 7 cells between two left bursts (7 to 224 in the first 10^9 steps).
- Each round trip moves the boundary between zone and body by a few cells (in a burst of seven trips: +5, −4, +6,
  −2, −4, −1, −3, so the zone loses three cells to the body); the left bursts give it back. The zone's width wanders
  but has stayed between about 150 and 630 cells.

So the machine is a bounded-looking chaotic system (the zone) beside a mirror (the body) whose length does not
matter. The tape grows on both sides like the square root of the time.

```
cells from the left end at a right record (step 976,834,360, 20,246 cells):
  zone: 387 cells, irregular, ends ...10011011100110011001001101101110110110111
  body: (1110110110)^1984 1110110110 11  B> 0      (the form the body has when the head reaches the right end)
```

## The zone model

Because a round trip does not depend on the body's length, the body can be kept short. `c/zonemodel.c` runs the
machine and, at every right record, cuts whole words out of the body so that 31 remain. Checked against the real
machine on the first 30,000 right records (4.55·10^9 steps): the zone, the state and the exact step count (the cut
run's steps plus 70 per cut word per round trip) agree at every 1,000th record; with the `check` option the program
also verifies at every right record that the right end has the form `trip` ends with. It runs about as fast as the
real machine's first 10^8 steps, whatever the time: 10^7 right records take a few minutes.

## Halting

Only F reading a 0 halts. F is entered from E on a 0, E from B on a 1 and B from A on a 0, all moving right, so the
halt is a rightward run `A> 0 1 0 0` (Lean: `halt_A`, `halt_B`, `halt_E`). The body never contains two 0s side by
side, so a halt can only happen in the zone or at its border. **Whether the machine halts is whether the zone ever
does.**

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the crossings `walk_A`, `walk_C01`, `walk_C110`; the body
  crossings `body_right`, `body_left`; the round trip `trip` for every body length; the halting situations
  `halt_E`, `halt_B`, `halt_A`.
- Trusted computation (our C and Python):
  - `c/zonemodel.c` with nothing cut: no halt in 2·10^11 steps; zone width at most 521 cells.
  - `c/zonemodel.c` with the body cut to 31 words: no halt up to 42,000,000 right records, which is 8.8·10^15 steps of
    the real machine (tape about 6·10^7 cells); largest zone 633 cells; no right record failed the check after the
    first 1,000, and the cut configuration never repeated (Brent's method).
  - `py/trip_check.py`: from real configurations (right records 3,000 and 20,000) one whole round trip run
    symbolically with the body length as a variable takes 70n + c steps and uses only `body_left` and `body_right`.
  - `c/visits.c`: in the first 2·10^8 steps the machine is in state F 5,702,121 times, always on a 1.

## What is open, next steps

- That *every* round trip has the form of `trip` (observed at every right record checked, not proved). With it,
  the halting question is exactly the zone model's, and Lean could state the reduction.
- The zone itself: a deterministic system of a few hundred cells with no visible order. If its width is bounded,
  the zone model is a finite system and must eventually repeat (non-halting) or halt, but the number of possible
  zones is far too large for a repeat to be seen. A useful next step is a model of the zone's left burst (30 cells
  each time) and of how far into the zone the head reaches between bursts.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA/lean/check.sh
python3 holdouts/1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA/py/rules.py     # rewrites lean/Rules.lean
gcc -O3 -o /tmp/zonemodel holdouts/1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA/c/zonemodel.c
/tmp/zonemodel 0 30000 1000 check > real.txt; /tmp/zonemodel 30 30000 1000 check > cut.txt   # columns 4 and 8 agree
/tmp/zonemodel 30 100000000 1000000 check                                                       # the long run
DUMP=3000 /tmp/zonemodel 0 3000 100000000 > /tmp/r.txt && python3 holdouts/1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA/py/trip_check.py /tmp/r.txt
python3 holdouts/1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA/py/turns.py 3e6 50
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC`](../1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB`](../1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F; it is this table started in state C

<!-- end of related machines -->
