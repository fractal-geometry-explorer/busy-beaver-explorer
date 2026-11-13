# 1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB

bbchallenge id 92364. One of the six-state holdouts whose halting from blank tape is open (group G07, family: **one growing block of 1s beside a slowly growing disordered region**).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 1RE |
| C | --- | 0LD |
| D | 1LE | 1LD |
| E | 0RA | 0LF |
| F | 1LF | 0LB |

## What it does

The tape is one huge block of 1s at the left (growing) end and a disordered region to its right. Each sweep the head
leaves the disordered region, runs left through the block of 1s (Lean: `cross_ones_left`, any length), turns at the
left end in state E (`E>0 1^N ...`) and runs back (`cross_ones_right`). The block gains about one cell per visit:
N = 4,748 at step 2.6·10^7, 14,358 at 2.2·10^8, 28,334 at 8.7·10^8, 43,506 at 2·10^9, over 45,734 visits of the left
end. The disordered region is where all the work happens; at 2·10^9 steps it is about 1,500 cells of short runs
(`0 1 0 1 0 1 0 1 0^2 1^2 0 1^4 0 1 0 1 ...`) and it grows slowly. Its contents never repeat (45,734 distinct
contents at the 45,734 visits), so it is not a finite-state controller in disguise.

## Status

Open. Lean: the halting configurations and 10^7 steps (`lean/Blank.lean`), and the two crossings of the block of
1s for every length (`lean/Shifts.lean`, kernel). Simulation: no halt in 2·10^9 steps.

## Second look: a counter-like region next to the block

Diffing consecutive visits of the left end (state E, `E>0 1^N ...`) **from the right**: the region changes only in
a prefix next to the block, and the far part stays fixed for long stretches, as the low digits of a counter whose
least significant end touches the block. Over the 17,520 visits up to 3·10^8 steps (N grew to 16,663, the region to
1,203 cells), the length of the changed prefix is at least 10 cells in 95% of the visits, at least 20 in 56%, 40 in
31%, 80 in 14%, 160 in 4%, 320 in 0.4% and 640 in 0.01%: deep "carries" are rare, as in a counter. The commonest
moves are a handful of fixed rewrites of the cells next to the block, each with its own change of N, e.g.

    0101010100           -> 010101011             N + 2   (3,337 times)
    01001110100          -> 010011011101          N + 0   (1,378 times)
    0101010111101110100  -> 010101010011011101    N + 2   (764 times)
    010101011110110100   -> 010101011110111101    N + 1   (597 times)

but unlike a counter the deep changes rewrite long stretches into contents that never recur, so the region is not
a fixed-word counter; N drifts (it also loses cells, e.g. 927 -> 919 in one visit at step 1,321,637).

## Next steps

* Treat the region as a word and the block as a number: find the finite set of rewrites at depth up to ~20 (they
  cover most visits) and the rule that decides which applies; the deep rewrites may then be compositions of a small
  set of moves (a "carry" that passes through words rather than digits).
* A simulator with N symbolic (the block is crossed by shift rules in both directions) would run the region alone,
  much faster.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.512; right: fixed,
exponent 0.025). After 1,000,000,000 steps: 32,607 cells visited (23,545 left of the
start, 343 right), 31,699 ones.

- left, step 969,744,264: `E>0 1^29968 0 1 0 1 0 1 0 1^4 0 1^4 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1^3 0 1 0^2 1^2 0 1^4 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1^2 0^2 1 0 1 0 1 0 1 0^2 1^3 0 1 0^2 1 0 1^2 0 1 0 1 0^2 1^2 0 1^3 0 1 0^2 1^2 0 1^3 0 1^3 `
- left, step 985,375,186: `E>0 1^30191 0 1 0 1 0 1 0 1^4 0 1^3 0 1 0 1 0 1 0 1^4 0 1^3 0 1^3 0 1^2 0 1 0^2 1^2 0 1^4 0 1^2 0 1^3 0 1^2 0 1^2 0 1 0^2 1 0 1 0 1 0 1 0 1^2 0^2 1^3 0 1 0^2 1 0 1 0 1 0 1^2 0 1 0 1^2 0^2 1^3 0 1 0 1 0 1 0 1 0^2 1^3 0 1 0^2 1^3 0 1^4 0 1 0^2 1 0 1 0 1 0 1 0 1^2 0^2 1 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/explainer.html`](../../pages/holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/explainer.html)
- [`pages/holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/proof-status.html`](../../pages/holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB/lean/check.sh
```
