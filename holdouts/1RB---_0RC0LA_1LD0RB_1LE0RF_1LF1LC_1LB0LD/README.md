# 1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD

bbchallenge id 19442.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 0LA |
| C | 1LD | 0RB |
| D | 1LE | 0RF |
| E | 1LF | 1LC |
| F | 1LB | 0LD |

## Status

**Open.** A bouncer: the block at the left end grows by one word every two sweeps, and a chaotic, never-repeating wall in the middle eats the previous block (m = 1461 down to 1455 in 2·10^10 steps).

## What it does

Each time the head, in state F, is at the left end of the tape, the tape reads (`py/view.py`, block view)

    F>0 (110111)^n (110)^4  [wall: 15-25 short runs]  (011111)^m  [fixed tail of about 40 cells]

The head sweeps from the left end across the block `(110111)^n` into the *wall*, a stretch of short runs of the
same 6-cell word with defects (`1^8 0 1^5 (011)^2 ...`), rewrites it and comes back; `n` grows by one every two
rounds (521 at 7.4·10^7 steps, 10,521 at 1.8·10^9, 34,521 at 1.9·10^10). Behind the wall a second long block
`(011111)^m` (a rotation of the same word) is worn down extremely slowly by the wall: m = 1461, 1459, 1458, 1457,
1456, 1455 at 7·10^7, 1.7·10^8, 4·10^8, 1.2·10^9, 2.6·10^9, 1.9·10^10 steps, with ±1 back-and-forth. The wall
never repeats exactly (33,482 different walls in the rounds of the first 5·10^9 steps), so it is not a finite-state
wall.

This block `m` was itself the growing block before: until 6.9·10^7 steps the tape read `F>0 (110111)^n (1)^11 ...`
with n growing to about 1,465, and then the wall jumped to the left end, the old growing block became the block
behind the wall, and a new growing block started. So the machine is a bouncer whose wall slowly eats the previous
block; when `(011111)^m` is gone (at this pace, after an enormous time) the wall will meet the fixed tail. The
wall's dynamics looks chaotic and nothing is known about where it leads.

## Results

- `py/view.py` (with `c/blocks.c`, `c/gaps.c`) prints the views of the run quoted above; `python3 py/view.py 2e10 4000` is the block view at the left end.
- Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.
- No macro rule is proved yet. Next step: a description of the wall (it may be a counter in some encoding) and of how it eats the old block.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.58; right: fixed,
exponent 0.063). After 1,000,000,000 steps: 54,647 cells visited (41,298 left of the
start, 22 right), 36,972 ones.

- left, step 970,481,411: `E>0 1 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 `
- left, step 986,158,421: `E>0 1 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 0 1^5 `

## Pages

- [`pages/holdouts/1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD/explainer.html`](../../pages/holdouts/1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD/explainer.html)
- [`pages/holdouts/1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD/proof-status.html`](../../pages/holdouts/1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---`](../1RB0LE_1RC0LD_1RD1RA_1RE0RB_0LA0RF_1LE---/README.md): rename A→F, B→E, C→A, D→B, E→C, F→D and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---`](../1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---/README.md): rename A→F, B→D, C→E, D→A, E→B, F→C and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
