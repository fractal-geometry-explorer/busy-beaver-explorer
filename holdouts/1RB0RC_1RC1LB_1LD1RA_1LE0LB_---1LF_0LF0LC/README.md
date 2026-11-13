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

## Pages

- [`pages/holdouts/1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/explainer.html`](../../pages/holdouts/1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/explainer.html)
- [`pages/holdouts/1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/proof-status.html`](../../pages/holdouts/1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC/lean/check.sh
```
