# 1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE

bbchallenge id 111805. One of the six-state holdouts whose halting from blank tape is open. Family: **solid block and alternating stretch trading places**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 0RD |
| C | 1LD | 1RB |
| D | 0LE | 0LC |
| E | 1RA | 0LF |
| F | 1LD | 1LE |

## Status

Open. Lean: only the generated files (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by
`native_decide`). C: no halt in 10^9 steps.

## What it does

At every side switch after step 10^4 (1,139 up to 10^9) the tape has two parts: at the right end `1^m 0 1 0 1 ...`
(solid block, then alternating), at the left end `0 1 0 1 ... 0 0 1^m` (alternating, then the solid block at the
right end). The trip from right to left carries the block across intact (569 of 569) in ≈ 2·m·r steps (r the
alternating length). The trip back gives new sizes; the block lengths at the last right-end visits are erratic
(1112, 1862, 868, 2199, 429, 2793, ...). `py/phases.py` checks all of this on a `tmrun ... records` log.

Halting: A on a 1; A is entered only from E on a 0, so a halt is exactly `0 F>1`. Growth: a trip ≈ 2mr ~ w²
steps, a few cells per round trip, so width ~ t^(1/3) (3,430 cells at 10^9).

## Later

1. Find the rule for the trip back (how the new block length depends on m and r), e.g. by tabulating it from
   small two-part tapes with a direct simulation.
2. Prove the carrying trip as a rule with `bbtools.symtm` (one pair across the block, then an induction).

## First look

Growth class **power/power** (left: power, exponent 0.339; right: power,
exponent 0.338). After 1,000,000,000 steps: 3,430 cells visited (1,887 left of the
start, 949 right), 2,712 ones.

- left, step 968,879,862: `C>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 986,249,063: `C>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 969,151,590: `1^2351 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0`
- right, step 986,470,009: `1^2479 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0`

## Pages

- [`pages/holdouts/1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE/explainer.html`](../../pages/holdouts/1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE/explainer.html)
- [`pages/holdouts/1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE/proof-status.html`](../../pages/holdouts/1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE 1000000000 records 100000 > /tmp/rec.txt
python3 holdouts/1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE/py/phases.py /tmp/rec.txt
```
