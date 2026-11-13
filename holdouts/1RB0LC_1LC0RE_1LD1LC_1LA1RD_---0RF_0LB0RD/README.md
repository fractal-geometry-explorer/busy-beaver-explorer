# 1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD

bbchallenge id 100296.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LC | 0RE |
| C | 1LD | 1LC |
| D | 1LA | 1RD |
| E | --- | 0RF |
| F | 0LB | 0RD |

## Status

**Open; only a first look.** The structure is described below, its rules were not derived.

## What it does

At every moment the head, in state A, is at the left end of the tape (12,927 times in the first 10^9 steps), the tape
is a list of blocks of 1s separated by single 0s: `A>0 1^a1 0 1^a2 ... 0 1^ak`, or the same with the head on the first
1 (`gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD 1000000000 at A L 50000000`). For example, step 1,095: `A>0 1^3 0 1^6 0 1^11 0 1^21 0 1^5`.

The first two blocks run through a short cycle (with the head on a 0, the first block is 2, 4, 5, 3, 2, ...), and each cycle changes the blocks
further right; now and then a change carries through and rewrites the tail of the list (step 1,919:
`3 6 12 44 5`; step 4,022: `2 4 8 26 18 15`). It behaves like a counter whose digits are blocks of growing, irregular sizes.
At step 809,445,816 the list has 17 blocks, `5 9 10 20 60 ... 8967 763`.

Next steps (not done): derive the rules of one sweep for a general list, check them against the run, and find the map
or invariant they define.

## Results

- `tools/c/tmrun.c` as above: the block-list shape at every left-end visit in state A (trusted).
- Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.484; right: fixed,
exponent 0.012). After 1,000,000,000 steps: 31,044 cells visited (26,214 left of the
start, 17 right), 31,010 ones.

- left, step 765,789,609: `C>0 1 0 1^5 0 1^7 0 1^18 0 1^34 0 1^71 0 1^82 0 1^114 0 1^304 0 1^1012 0 1^1186 0 1^2167 0 1^3201 0 1^4736 0 1^4316 0 1^8967 0 1^763`
- left, step 802,190,534: `C>0 0 1^4 0 1^8 0 1^28 0 1^30 0 1^33 0 1^106 0 1^167 0 1^615 0 1^910 0 1^1649 0 1^1908 0 1^2557 0 1^7290 0 1^4316 0 1^8967 0 1^763`

## Pages

- [`pages/holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD/explainer.html`](../../pages/holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD/explainer.html)
- [`pages/holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD/proof-status.html`](../../pages/holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD/lean/check.sh
```
