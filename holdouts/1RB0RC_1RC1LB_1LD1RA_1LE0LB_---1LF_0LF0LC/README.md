# 1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC

bbchallenge id 71477. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1RC | 1LB |
| C | 1LD | 1RA |
| D | 1LE | 0LB |
| E | --- | 1LF |
| F | 0LF | 0LC |

## What it does

The head reaches a new cell at the left end only rarely (16 times in 10^10 steps, each about 7.7 times later than the
one before). At those moments, with `t = 1110`, `u = 111100` and `t^k` written as k, the tape is a short prefix and
layers of periodic words:

    step 1,519,748:  01111111111100 2u14u1(u15u1)^5 uu2u1u4u1(u2uu4u1)^19 ...
    step 11,381,069: 0111111100 1u5u1(u15u1)^15 uu2u1u4u1(u2uu4u1)^56 ...

The repeat counts grow about 2.8 times per epoch (outer layer 2, 5, 15, 40, 114; inner 6, 19, 56, 159, 446), as
does the width. The left 6 to 8 cells change only when the head comes back to the left end, and cycle through
patterns made of `11` and `01` pairs, like a small counter.

## Status

Open, reduced to the left end. The only halt is E reading a 0.

- Lean, kernel: any halt from blank tape is in state E on a 0 with blank tape to its left (`halt_left_blank`,
  `lean/HaltLeft.lean`, from the windows-of-4 certificate `lean/CTL4.lean`); three shift rules (`lean/Rules.lean`);
  halting configurations, 10^4 steps (`lean/Blank.lean`). `native_decide`: 10^7 steps.
- By hand (not machine-checked): the leftmost written cell holds 1 while the head is right of it, so the only way to
  halt is F reading that leftmost 1 (then C, D, E walk onto blank cells and E halts).
- Computed: no halt in 10^10 steps (`c/leftedge.c`); F reached the second cell 4 times (reading 1), the leftmost never.

## Notes for later

- Decode the left-end counter: which prefixes the epochs produce, and whether one of them lets F reach the leftmost
  cell. A proof would be an invariant on the left prefix plus the Lean edge result.
- Prove the hand argument in Lean (an `Edge.lean` like `bb6-1RB1RA_1LC1LD/lean/Edge.lean`).

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| right | 256,165,914 | 23,445 | 2,267 | 1,981 | 72 | 0.10 |
| left | 664,325,733 | 31,981 | 4,601 | 2,582 | 24 | 0.00 |
| right | 1,024,120,904 | 37,510 | 3,279 | 3,453 | 37 | 0.17 |
| right | 4,097,166,363 | 83,045 | 6,452 | 7,224 | 56 | 0.08 |
| left | 5,128,930,040 | 88,957 | 12,800 | 7,182 | 26 | 0.00 |
| right | 16,384,141,312 | 186,485 | 17,607 | 15,782 | 63 | 0.10 |

**Proposed family: F01, periodic blocks driven by a bounded engine** (a few periodic layers of long period and a short left end).

With repeats of single words only the tape looks irregular (33,389 level-1 tokens for 186,485 cells at 1.6·10^10 steps), but the words repeat in groups: with groups counted once the description is 24 to 72 level-2 tokens at every record from 2.6·10^8 to 1.6·10^10 steps. For example at the left-end record at step 5,128,930,040 the whole tape is `0 1^9 0 (0111)^25 [100 1^3 0 1^4 0 (0111)^16]^316 100 1^3 0 1^4 0 (0111)^11 100 1^3 0 1^4 0 (0111)^4 1 [0 (0111)^3 100 1^4 0 (0111)^5 100 1^3 0 1^4]^1245 00 111`: two layers and about twenty short pieces.

A few periodic blocks of long period (76 and 52 cells in the example; 28 cells for a third layer seen at the right-end records) and a bounded rest is the F01 shape. The README's layers that grow about 2.8 times per epoch are these blocks.

Next step: The F01 closure with the layers as blocks; the README already confines a halt to the leftmost cells, so the tail classes to track are those of the left end.

## Pages

- [`pages/holdouts/1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/explainer.html`](../../pages/holdouts/1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/explainer.html)
- [`pages/holdouts/1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/proof-status.html`](../../pages/holdouts/1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/lean/check.sh
```
