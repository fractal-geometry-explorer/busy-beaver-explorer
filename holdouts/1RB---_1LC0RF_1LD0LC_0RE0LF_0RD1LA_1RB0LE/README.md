# 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE

bbchallenge id 30773.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1LC | 0RF |
| C | 1LD | 0LC |
| D | 0RE | 0LF |
| E | 0RD | 1LA |
| F | 1RB | 0LE |

## Status

**Open.** A bouncer between a growing block and a wall of exactly 1,573 cells that changes every sweep like a counter (changes start at cell 44, carries reach 25 cells further about every three times as many sweeps); what happens when the carries reach the end of the wall is unknown.

## What it does

Once per sweep the head, in state C, is at the left end and the tape is

    C>0 (01101)^n  W          W: exactly 1,573 cells, every sweep (after 2·10^7 steps)

The block `(01101)^n` grows by about one word per sweep (n = 476 at 1.2·10^7 steps, 9,476 at 2·10^9, 29,726 at
2·10^10), and the right end of the tape never moves: `W` is a **wall of fixed length**. It is different at every
sweep (10,821 different walls between 2·10^7 and 3·10^9 steps), and `py/wall.py` shows how: comparing consecutive
walls, the changes always start at cell 44 of W and usually stop within a hundred cells, but now and then reach
further, and the deepest change so far moves out in steps of 25 cells at sweeps 274, 406, 2,296, 7,335, 20,772
(cells 252, 294, 319, 344, 369). That is the behaviour of a **counter written in the wall**, with digits about 25
cells wide and a base near 3 (each new depth is reached about three times later).

If that is right, the carries reach the end of the wall (cell 1,573, about 48 more digits) only after something
like 3^48 sweeps, far beyond any simulation, and what the machine does then (grow the wall, or halt) decides the
question. Decoding the digits would turn this into an exact statement.

## Results

- `py/view.py` (with `c/blocks.c`, `c/gaps.c`) prints the views of the run quoted above; `python3 py/view.py 2e10 3000` is the block view at the left end; `python3 py/wall.py 2e10` (with `c/walldump.c`) compares consecutive walls.
- Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.
- No macro rule is proved yet. Next step: decode the wall as digits, prove the increment with symtm, and work out what the carry does at the end of the wall.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.494; right: fixed,
exponent 0.0). After 1,000,000,000 steps: 34,610 cells visited (25,368 left of the
start, 201 right), 20,724 ones.

- left, step 972,937,536: `C>0 0^3 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^`
- left, step 988,768,470: `C>0 0^3 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^`

## Pages

- [`pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/explainer.html`](../../pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/explainer.html)
- [`pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/proof-status.html`](../../pages/holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE/lean/check.sh
```
