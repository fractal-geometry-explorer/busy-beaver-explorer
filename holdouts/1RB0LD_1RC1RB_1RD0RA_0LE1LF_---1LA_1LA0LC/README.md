# 1RB0LD_1RC1RB_1RD0RA_0LE1LF_---1LA_1LA0LC

bbchallenge id 21414, group G08. Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1RC | 1RB |
| C | 1RD | 0RA |
| D | 0LE | 1LF |
| E | --- | 1LA |
| F | 1LA | 0LC |

## What it does

A two-sided bouncer. At the left end the tape reads `(01)^k₁ 1 (01)^k₂ 1 (01)^k₃ …`: a list of numbers k, most
of them odd (3 is the most common), with rare defects such as `10100`. Going right, B turns each `1010` into `1101`,
so at the right end the list is written in the words `1110`, `1101`, `1011`, `0111`; going left, D turns `1101`
back into `0101`. The far part of the list is carried along almost unchanged, but near the left end the stretches
merge and split irregularly from trip to trip.

The machine halts only when E reads a 0; E is entered from D reading a 0, so `0 D> 0` halts, and `0 0 A> 1`,
`0 C> 1 1` lead there.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the two sweeps (`right_B`, `left_D`) and the halting
  situations (`halt_D`, `halt_A`, `halt_C`).
- `c/visits.c` (trusted, our code): in the first 2·10⁸ steps the machine is in state E 17,398,306 times, always on a 1.

## What is open, next steps

The question itself. A description of how the list changes at its left end (which numbers merge, which split)
would be the first step; it looks irregular.

**Later**: set aside after the first pass.

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 256,013,964 | 25,212 | 98 | 363 | 389 | 0.04 |
| right | 256,092,768 | 25,214 | 126 | 350 | 408 | 0.04 |
| left | 1,024,070,510 | 50,578 | 205 | 704 | 787 | 0.03 |
| right | 1,024,417,160 | 50,580 | 254 | 671 | 801 | 0.03 |
| right | 4,096,225,724 | 100,220 | 371 | 1,277 | 1,539 | 0.03 |
| left | 4,096,366,028 | 100,222 | 364 | 1,359 | 1,572 | 0.03 |
| right | 16,384,148,932 | 201,719 | 800 | 2,605 | 3,171 | 0.02 |
| left | 16,384,432,541 | 201,727 | 729 | 2,769 | 3,217 | 0.02 |

**Proposed family: F11, defect gases and irregular zones** (two periodic backgrounds, (10) and (1101010), with a number of domains proportional to the tape).

The number of pieces is proportional to the length of the tape at every scale: 389, 787, 1,572 and 3,217 level-2 tokens at the left-end records at 2.6·10^8, 10^9, 4.1·10^9 and 1.6·10^10 steps, for 25,212, 50,578, 100,222 and 201,727 cells (one token per 63 or 64 cells each time). No block holds more than 4% of the tape.

Seen from the left end the tape is stretches `(10)^k` separated by single 1s, and stretches of a second word `(1101010)^k` between them: two periodic backgrounds with domain walls and point defects, in number proportional to the tape. That is a defect sea (F11), not a list of counters (the stretches have no bounded number and no visible order) and not a bounded description.

Next step: A particle table: the kinds of walls between the two backgrounds, how a sweep moves each and what happens when two meet.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_1RC1RB_1RD0RA_0LE1LF_---1LA_1LA0LC/lean/check.sh
python3 holdouts/1RB0LD_1RC1RB_1RD0RA_0LE1LF_---1LA_1LA0LC/py/rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LD_1RC1RB_1RD0RA_0LE1LF_---1LA_1LA0LC/py/turns.py 3e6 50   # the list at the left end
```
