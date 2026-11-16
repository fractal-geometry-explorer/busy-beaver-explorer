# 1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD

bbchallenge id 65208. One of the six-state holdouts whose halting from blank tape is open. Its run looks chaotic on a tape that grows roughly logarithmically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 0RC | 0RB |
| C | 1RD | 1RF |
| D | 1LA | 0LE |
| E | 0LD | 0LB |
| F | --- | 0RD |

## Status

Open. Proved in Lean (kernel): the halting configurations and the first 10,000 steps (`lean/Blank.lean`, 10^7 with
`native_decide`); the run-length frame map of `bbtools.listframe` for the first 10^6 frames (`lean/Frames.lean`,
`native_decide`, with `no_halt_of_total`: if the frame map is defined forever, the machine never halts); and the
law of the counter at the right end for every size (`lean/Odometer.lean`, below). C: no halt in 30,000,000,000 steps.

## What it does

The right part of the tape is a chain of counters, each counting the overflows of the one before it; the crossing
profile, the number of times the head moves from each cell to the next one (`c/cross.c`, 10^9 steps, cells -174 to
398), shows them as stretches of constant ratio:

| cells at 10^9 steps | crossings | part |
|---|---|---|
| 355 to 398 | ×1/3 every 4 cells going right (172,414 at 355 … 57,470 at 359 … 1 at 398) | the **odometer**, base 3, 4-cell digits (proved) |
| 319 to 354 | ×2 every 6 cells going right (13,xxx at 331-336, 26,xxx at 337-342, 51,7xx at 343-348, 103,4xx at 349-354) | a binary counter with 6-cell digits (observed) |
| 302 to 318 | ×1/3 every 4 cells going right (370,307 at 302 … 13,730 at 314) | another base-3 stretch (observed) |
| -174 to 302 | up to about 10 million, several bumps | not decoded |

**The odometer (proved).** Read the cells right of its low end four at a time: `0111` = 0, `0000` = 1, `0110` = 2
(lowest digit nearest the head). A visit in state B adds one in base 3: trailing 2s become 0s, the first other digit
goes up by one, and the visit always comes back out in state D. Blank tape reads as `0000 0000 …`, an endless row of
digits 1, so a carry always stops and the odometer never overflows; it just gains a digit 2 at its top when a carry
reaches the blank tape. `lean/Odometer.lean` proves this for every number of digits (`o_carry`, `o_inc0`, `o_inc1`,
`o_inc_blank`) from three token rows (`lean/VisitR.lean`). In the run, the cells right of 359 are entered only in
state B, and all 51,723 of those visits up to step 10^9 are these three rows, from step 367,121,349 on
(`c/vislaws.c`). Each such visit comes from the binary stretch to its left, so the odometer counts the carries
that leave that stretch.

**Where it could halt.** Only F0 halts; F is entered only from C reading 1 (`1RF`), 5,555,291 times in the first
10^8 steps, always onto a 1 (then `0RD`). Halting needs C to read 1 with a 0 to its right; that is a local pattern that
the run avoids millions of times, but no CTL window up to 8 cells proves it.

## How far it was run

- Direct C simulation (`c/longrun.c`): 30,000,000,000 steps, no halt; at the end cells -186 to 512 (699 cells), 302 ones.
- The frame map (`py/frames.py`, `bbtools.listframe`) is checked for 10^6 frames in Lean.
- No macro-level accelerator.

## Open questions

- The rest of the tape (cells -174 to 302 at 10^9): which counters it holds and how they feed the chain on the right.
- Why C never reads 1 with a 0 to its right.

## Scripts

- `c/cross.c`, `c/longrun.c`, `c/d1ev.c`, `c/vislaws.c` (as in 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---).
- `lean/VisitR.lean` was written by `py/gen_visit2.py MACHINE H65208 R py/odometer_rows.jsonl Machine "the first
  1,000,000,000 steps"`, the rows by `c/vislaws MACHINE 1000000000 R 359 4 > py/odometer_rows.jsonl`;
  `lean/Odometer.lean` by hand.
- `py/frames.py`: the frame map (`lean/Pieces.lean`, `lean/Cases.lean`, `lean/Frames.lean`).

## Earlier notes

- `bbtools.macro` with blocks of 3 / 6 cells needs one macro step per about 3 / 6-7 steps over 10^7 steps;
  `bbtools.cycles` (k = 4) finds no linear cycle in 10^7 steps; CTL windows up to 8 cells do not close (group scan).

## First look

Growth class **fixed/power** (left: fixed, exponent 0.054; right: power,
exponent 0.16). After 1,000,000,000 steps: 576 cells visited (174 left of the
start, 393 right), 281 ones.

- right, step 547,646,528: `1 0^2 1^3 0^2 1^2 0^5 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0^2 1^2 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0 1 0^2 1^3 0^2 1^2 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0^4 1^2 0^2 1^2 0 1 0^2 1^2 0 `
- right, step 909,086,150: `1 0^2 1^3 0^2 1^2 0^5 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0^2 1^2 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0 1 0^4 1^2 0^2 1 0^2 1^2 0^4 1^2 0 1 0^2 1^2 0^4 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0 1 0^2 1^2 0^4 1^2 0^4 1^2 0^2 1^2 0^4 1^2 0^4 `

## Pages

- [`pages/holdouts/1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/explainer.html`](../../pages/holdouts/1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/explainer.html)
- [`pages/holdouts/1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/proof-status.html`](../../pages/holdouts/1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD/lean/check.sh
```
