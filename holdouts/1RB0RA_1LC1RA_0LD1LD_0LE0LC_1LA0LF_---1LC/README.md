# 1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC

bbchallenge id 154944, a six-state holdout of group G05 ("Chaotic Fractal Type 1" on the community tracker).
**Open.** The tape is a row of *units* `(10)^x 00 (10)^y 110 0 1^w 0`. A unit that has blank cells to its left runs
a *phase*: each cycle moves one pair out of y, puts three pairs into x and two 1s into w, and uses six of the blank
cells. When y is 0 the unit *turns*: its x becomes a wall of 1s and its w-block becomes the blank cells of the unit
to its right, which now runs its own phase, and so on down the tape; when the blank cells run out the head comes
back and the wall becomes a new unit whose y is the old x. Lean proves the cycle and the phase at any depth, the
turn and the return, for all sizes. What happens where two units meet is known only from simulation, in several
hundred local cases. The run-length simulator `c/macro.c` (exact, tested against the plain simulator) runs
5.1·10^36 steps without a halt.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1LC | 1RA |
| C | 0LD | 1LD |
| D | 0LE | 0LC |
| E | 1LA | 0LF |
| F | --- | 1LC |

## What it does

**The unit and its phase.** Write `U x y w = (10)^x 00 (10)^y 110 0 1^w 0` and

    P x y w R  =  0^inf A>0 U x y w R

(head in state A on the cell left of the unit, blank to the left). Two returns of the head make one cycle:

    0^6 A>0 U x (y+1) w   ->   A>0 U (x+3) y (w+2)        in 8x + 4y + 30 steps

for every x, y, w and whatever is left of the six 0s and right of the unit. The unit grows by six cells to the
left. So k cycles need 6k blank cells: `0^(6k) A>0 U x (y+k) w -> A>0 U (x+3k) y (w+2k)` in
k(8x+4y+16) + 14k² steps.

**The same against a wall of 1s.** With 1s to its left instead of 0s (the head on the last 1) the unit runs a
slower cycle that takes two 1s from the wall:

    1 1 <A U (x+1) (y+1) w   ->   <A U (x+2) y (w+2)       in 8x + 4y + 30 steps

**The turn.** When y is 0 the unit cannot cycle. With nine blank cells to its left,

    0^9 A>0 U x 0 w   ->   1^(2x+10) <A  1 0 1^(w+4) 0      in 14x + 60 steps

(`<A`: the head on the last 1 of the wall). The head then erases `1 0 1^(w+4)` on its way right, and the unit to
the right finds itself with about w blank cells to its left: it runs its own phase with them. The whole machine is
this, nested: each unit that turned is a wall, its w-block the blank cells (the *gap*) of the next unit.

**The return.** When the gap is used up the head goes back left and the wall comes back as pairs:

    0^4 A>0 (10)^(x+1) 11 000   ->   A>0 U 1 x 2             in 4x + 16 steps

a new unit with x = 1 whose y is the old x. At the left end of the tape (level 0) the phase always completes,
since the blank is endless: a *main phase* `P 1 y w R` ends as `P (3y+1) 0 (w+2y) R`, turns into a wall of 6y+12
ones, and, if the trip to the right ends with `(10)^(3y+5) 11 000` at the left end, the next main phase is
`P 1 (3y+4) 2`.

**An example** (steps 4,305 to 5,625; `<A` events, the tape left of the head | right of it; `T^n` is `(10)^n`):

| step | left | right | what |
|---|---|---|---|
| 4,305 | blank | `T^43 00 110 0 1^30 0`, `0 T^4 110 0 1^3 0`, ... | level 0 has y = 0 |
| 4,864 | blank | `T^47 111 00 1^32 0` ... | three more visits of the left end |
| 4,967 | `1^96` | `1 0 1^34 0` ... | the turn: wall of 96 ones |
| 5,009 | `1^95 0011 0^31` | `1 0 111 0 T^3 110 0 1^3 0` ... | level 1 starts, gap 31 |
| 5,100 | ... `0^18` | `T^5 111 00 1^2 0`, `0 T^2 110 0 1^5` ... | level 1 has y = 0 too |
| 5,119 | ... `0^17 1^12` | `1 0 1^4 0` ... | its turn: level 2 starts with a gap of 1 |
| 5,173 | ... `0^15` | `T^5 11 0000`, `1 0 11 0000 110 0 1^7` | back at level 1 |
| 5,205 | ... `0^11` | `10 000 T^4 110 0 1^2 0` ... | the return: level 1 is the unit x = 1, y = 4, w = 2 |
| 5,276 | ... `0^2` | `T^5 110 T^3 110 0 1^4` ... | the gap of level 1 is used up |
| 5,425 | blank | `T^47 11 000`, `1 00 T^6 00 T^2 110 0 1^6 0` ... | back at level 0 |
| 5,625 | blank | `10 000 T^46 110 0 1^2 0` ... | the return: main phase y = 46 |

**Main phases.** The phases at the left end that start with x = 1:

| # | step | y |
|---|---|---|
| 1 | 173 | 4 |
| 2 | 1,225 | 14 |
| 3 | 5,625 | 46 |
| 4 | 42,717 | 142 |
| 5 | 372,173 | 430 |
| ... | | y -> 3y + 4 |
| 17 | 101,751,156,863,558,057 | 229,582,510 |
| 18 | 1,215,921,296,438,434,289 | 488,413,207 |
| 19 | 4,724,209,949,575,115,755 | 1,465,239,625 |
| ... | | y -> 3y + 4 |
| 37 | 6.236·10^35 | 567,663,852,794,517,601 |

From the second on y -> 3y + 4, **except from 17 to 18**: 488,413,207 = 3·229,582,510 + 4 - 200,334,327. In that
trip the unit of level 1 did not stop when its gap was used up: it went on against the wall of level 0 with the
slower cycle, 200,334,327 times, each time taking one pair of the wall for itself. So y -> 3y + 4 is not a law of
the machine, and the previous closed form for y_n is wrong after n = 17.

**Where units meet.** How a unit is entered, how it freezes when the gap runs out, and when it goes on against
the wall depends on a few cells at the joints: the gap left over (0 to 5 cells), w = 2 or 3, x = 0, and so on.
Classing every arrival of the head at a left turn (E reads 0, writes 1, A goes on to the left) by the cell runs
around it (lengths above 4 as "long"; above 9 for the run left of the head) gives 387 classes in 1.5 million such
events up to 10^28 steps, the same 387 as up to 10^20. No description of all of them has been written, so there is
no macro machine on the list of units yet.

**Halting.** The only missing transition is F reading 0. F is entered only from E reading 1, and E only from D
reading 0. So a halt is a left sweep (C keeps a cell, D turns a 1 into 0, alternately) that finds `0 1 0` just left
of a cell C passed: for example a sweep arriving in C on the right end of `(10)^2 1^m` with m odd. With m even
the same sweep passes. Whether it halts is a question about the parities at the joints of the units.

## Status

Open.

**Lean (kernel)** — nothing here depends on `native_decide`:
- `cyc_ee`, `cyc_eo`, `cyc_oe`, `cyc_oo` (`lean/Rules.lean`), `cycle`, `phase` (`lean/Phase.lean`): the cycle and
  the phase at the left end of the tape.
- `g_cycle`, `g_q`, `g_turn`, `g_ret` (`lean/Gap.lean`, written by `py/gen_gap.py` with `bbtools.symtm.prove`): the
  four rules above with any tape on both sides.
- `lean/Levels.lean`: `cycle_gap`, `phase_gap` (k cycles with 6k blank cells, closed step count); `cycle_ones`,
  `phase_ones` (k+1 cycles against a wall of 2k+2 ones, in (k+1)(8x+4y+24) + 6(k+1)² steps, ending on the cell left
  of those ones, whatever it holds); `turn`; `ret`; `main_to_turn` (`P 1 y w R` reaches the wall of 6y+12 ones in
  `pcost 1 y + 42y + 74` steps); `main_from_ret` (`A>0 (10)^(x+1) 11 000 R` at the left end reaches `P 1 x 2 R`).

**Lean (native_decide)** (`lean/Reach.lean`, written by `py/gen_reach.py`):
- `reach_173`, `reach_1225`, `reach_5625`: blank tape reaches `P 1 4 2 R0`, `P 1 14 2 R1`, `P 1 46 2 R2`.
- `turn_173`, `turn_1225`, `turn_5625`: each of these phases reaches its wall (36, 96, 288 ones) at steps 735,
  4,967 and 38,359; `phase_493`.

The bounded runs of `lean/Blank.lean` (no halt in 10^7 steps) are as generated.

**Computed (trusted)**: `c/macro.c` keeps the tape as runs of 0, 1 and `10`, crosses a run in one move with the
machine's six shift rules, and jumps over k cycles of a unit (the two rules of `phase_gap` and `phase_ones`).
It runs 5,135,031,925,650,943,510,945,361,186,015,609,585 steps (5.1·10^36, 37 main phases, 495 million moves,
8 seconds) without a halt; its counters are 64-bit, which is the limit. `py/test_macro.py`: the whole tape equals
the plain simulator's at 20 stops up to step 2,971,093; the main phase starts (step, y, a fingerprint of the tape)
equal the plain simulator's up to 3.3·10^6 steps; with and without phase jumps they agree up to 10^15 steps (and, in
a four-minute run not part of the test, up to 1.3·10^18, which includes the odd phase 18). `c/phases.c` is the
plain simulator of the first pass (2·10^11 steps).

**Heuristic**: the table of main phases beyond the third, the account of the trip from phase 17 to 18, the
example, and the count of 387 local cases.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/lean/check.sh
python3 holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/py/gen_rules.py      # rewrites lean/Rules.lean
python3 holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/py/gen_gap.py        # rewrites lean/Gap.lean
python3 holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/py/gen_reach.py      # rewrites lean/Reach.lean
python3 holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/py/test_macro.py     # macro.c against the plain simulator
gcc -O2 -o macro holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/c/macro.c && ./macro 36
```

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine and bounded runs (generated) |
| `lean/Rules.lean`, `lean/Phase.lean` | the cycle and the phase at the left end (first pass) |
| `lean/Gap.lean` | cycle, wall cycle, turn, return with any tape around them (generated by `py/gen_gap.py`) |
| `lean/Levels.lean` | `U`, `QC`, `PG`; the phases with closed step counts, `turn`, `ret`, the two level-0 corollaries |
| `lean/Reach.lean` | blank tape to the first three main phases and their turns (generated by `py/gen_reach.py`) |
| `c/macro.c` | run-length simulator with phase jumps |
| `py/test_macro.py` | its tests |
| `c/phases.c` | plain simulator printing the main phase starts |

## Pages

- [`pages/holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/explainer.html`](../../pages/holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/explainer.html)
- [`pages/holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/proof-status.html`](../../pages/holdouts/1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC/proof-status.html)

## For later

1. Write the macro machine on the list of units. The moves inside a unit are proved; what is missing is the
   joints: entering a unit after a turn (`1^(2x+10) <A 1 0 1^(w+4) 0` followed by each kind of next unit),
   freezing when fewer than six blank cells are left (gap 0 to 5, in each half of the cycle), and going on against
   the wall. `bbtools.symtm.prove` proves each one as soon as it is stated (as in `py/gen_gap.py`); the 387
   classes of left turns are the list to work through, most of them the same rule at different small sizes.
2. With that, state a reduction theorem (halts iff the macro machine reaches a halting joint), then look for the
   parity invariant at the joints that keeps C away from `0 1 0 1^odd`.
3. Counters beyond 64 bits in `c/macro.c` to pass 5·10^36.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LE_0RC1RC_0RD0RB_1RE0RF_1LA0LE_---1RB`](../1RB1LE_0RC1RC_0RD0RB_1RE0RF_1LA0LE_---1RB/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
