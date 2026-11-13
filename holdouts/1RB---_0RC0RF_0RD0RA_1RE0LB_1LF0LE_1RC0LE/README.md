# 1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE

bbchallenge id 21494.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 0RF |
| C | 0RD | 0RA |
| D | 1RE | 0LB |
| E | 1LF | 0LE |
| F | 1RC | 0LE |

## Status

**Open.** A bouncer whose first block grows by one cell per sweep; behind it a region of defects in the 1010... background, moved one cell at a time by a zig-zagging head, grows about logarithmically and looks irregular.

## What it does

Read the tape as the gaps between consecutive 1s. The background is gap 1 (`1010...`), and the defects are gaps
of 2 (`00`, now and then 3). Each time the head, in state F, is at the left end of the tape with the background
there, the tape is

    1^n0  2  1^n1  2  1^n2  2 ...  2  1^nk          (gap list; 1^n = n gaps of 1, 2 = a defect)

and from one such moment to the next (a *round*, about 3,500 steps at n0 = 800) the first block grows by one
(`n0`: 801, 802, 803, ...). In a round the head runs across the first block, then zig-zags slowly (a few cells
forward, a few back) through the defect region, moving one or two defects by a cell, and returns. The first
blocks behind it barely move (7, 12, 24 then 6, 13, 25 and so on, a ±1 wobble), the later ones change at random
looking. The number of defects grows very slowly, about logarithmically: 16 at 10^5 steps, 21 at 10^6, 26 at
10^8, 28 at 10^9; the right end of the tape grows with it (a few hundred records in 10^8 steps, against 13,000 at
the left).

So the machine is a sweeping bouncer whose far end is a slowly growing, irregular region of defects. What the
defect region does over long times, and whether a defect pattern that halts (A reading 1) can form there, is not
understood.

## Results

- `py/view.py` (with `c/blocks.c`, `c/gaps.c`) prints the views of the run quoted above; `python3 py/view.py 1e9 3000` is the gap view at the left end.
- Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.
- No macro rule is proved yet. Next step: find the rule by which a sweep moves the defects (the zig-zag), then the induced map on the gap list.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.528; right: fixed,
exponent 0.045). After 1,000,000,000 steps: 44,247 cells visited (31,864 left of the
start, 426 right), 22,110 ones.

- left, step 970,092,477: `E>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 985,770,725: `E>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/explainer.html`](../../pages/holdouts/1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/explainer.html)
- [`pages/holdouts/1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/proof-status.html`](../../pages/holdouts/1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC0RF_0RD0RA_1RE0LB_1LF0LE_1RC0LE/lean/check.sh
```
