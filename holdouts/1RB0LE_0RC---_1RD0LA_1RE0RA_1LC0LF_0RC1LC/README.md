# 1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC

bbchallenge id 36703, a six-state holdout of group G05 (growth class fixed/sqrt). **Open, and not yet analysed into
a macro machine.** Proved so far: no halt in the first 10^7 steps (Lean, `native_decide`); the C simulator finds no
halt in 10^9 steps.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 0RC | --- |
| C | 1RD | 0LA |
| D | 1RE | 0RA |
| E | 1LC | 0LF |
| F | 0RC | 1LC |

The machine halts only on B reading 1, that is after `A>0 1`.

## What it does (observed)

The left end of the visited tape stops moving early. The right end grows like the square root of the step count.
`py/view.py` prints the tape each time the head, in state C, reads a 0 on the leftmost visited cell. It cuts the
tape right of the head into 4-cell words, using the offset that gives the most `0011` words.

- **Before about step 396,000** the tape is mostly 1s with scattered 0s. This is a different regime that has not
  been looked at in detail.
- **From step 396,499 on** the tape reads, left to right:
  - a few cells;
  - a run of `0110` and `0010` words next to the left end, which behave like a counter (their pattern changes
    between visits);
  - a background of `0011` words (`.`) with sparse `0001` defects (`o`), alone or doubled (`oo`), at gaps that
    grow roughly linearly along the tape.

  For example, at step 7,742,585:

      [0110]x18 [0010] [0110]x4 [0101] ......................oo......................o........oo....

- Between visits to the left end, the head bounces. It goes out to the right end, which moves right by a couple of
  cells per bounce, and back to turning points at the defects. The defects drift left from bounce to bounce.
  Visits to the left end are rare: steps 396,499, 396,541, 465,987, ..., 7,166,889, 7,742,585, 22,969,011,
  86,874,709. The last gaps between visits grow by a factor of about 4.

## Status and evidence

- **Lean** (`lean/Blank.lean`, generated):
  - the halting configurations (kernel);
  - no halt in the first 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- **Computed (trusted)**: `tools/c/triage.c` finds no halt in 10^9 steps.
- **Heuristic**: the structure above, seen with `py/view.py` up to 1.5·10^8 steps.

The symbolic shift rules of `bbtools.symtm` do not cross the `0011` background in one move. The head zigzags
inside the words, so the crossing needs a hand-made rule over two or more words.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC/lean/check.sh
python3 holdouts/1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC/py/view.py 1.5e8 2.3e7     # about a minute
```

## Pages

- [`pages/holdouts/1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC/explainer.html`](../../pages/holdouts/1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC/explainer.html)
- [`pages/holdouts/1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC/proof-status.html`](../../pages/holdouts/1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC/proof-status.html)

## For later

This needs several days, starting from scratch.

1. Find the exact bounce:
   - the head's run over the `0011` background in each direction (it zigzags, so try words of 8 or 12 cells);
   - what happens at an `o` and at an `oo`;
   - how the right end grows.
2. Describe the configuration at a turn of the head as a list of defect gaps, and find the map from one turn to
   the next. Check it against `py/view.py`.
3. Find what the `0110`/`0010` counter counts, and how a visit to the left end changes it.
4. Understand the early regime before step 396,000, or show that it can be skipped: prove one exact configuration
   at step 396,499 by a bounded run, and start the macro machine there.
