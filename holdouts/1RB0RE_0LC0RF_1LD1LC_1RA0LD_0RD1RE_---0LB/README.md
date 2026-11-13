# 1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB

bbchallenge id 180438. Open. A **nested drain/copy counter** on three long blocks: at each visit of the left end one word `10111` of the
right block becomes a `00111` and a `100` on the left (phase A, proved); then the `100` block is poured into a new
block at the far right, two words for one (phase B, proved); then the left block is recycled as the next right
block. Each round the blocks are about twice as long.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 0LC | 0RF |
| C | 1LD | 1LC |
| D | 1RA | 0LD |
| E | 0RD | 1RE |
| F | --- | 0LB |

## The tape as words

At the left end, in state D, the tape reads `0 0 1^5 (00111)^a (100)^c (10111)^b` + a short tail, e.g. step
315,712,461: `0 0 1^5 (00111)^1475 (100)^1476 (10111)^3922 1 0 0 1^4 0 1^4 0 0 1 0`. Moving right the same blocks
appear rotated (`11001`, `001`, `01111`).

## Phases

| phase | tape | change | steps | proof |
|---|---|---|---|---|
| A | `0^inf D>0 0 1^5 (00111)^a (100)^(a+1) (10111)^(b+1) R` | a+1, c+1, b-1 per visit | 28a+55 | `grow` |
| B | `0^inf D>0 0 1^5 (00111)^a (100)^(c+4) (111100)^e 0 0^inf` | a+2, c-2, e+1 per two visits | 32a+24c+50e+178 | `pour` |

(Lean, kernel, for all values and, in `grow`, any tape R: in phase A the head never goes past the first word of the
right block, so the tape grows at the left only.)

When the right block is empty, phase B starts; when the middle block is empty, the left block is rewritten as
`(01111)^a` and becomes the right block of the next phase A. Recycled blocks: 566 words (step 3.37e6), 5,368
(2.85e8), 10,769 (1.75e9). From the 1.75e9 round on the far-right block of the previous round stays on the tape
(`(100111)^2702`), and phase B is replaced by a slower one in which a small counter of short `(001)` and `1 1 1`
pieces forms between the middle block and `(111001)^e`, which is eaten a word every few visits (step 4.6e9:
`(00111)^14275 (100)^10789 1 1 1 0 0 1 0 0 1 1 1 0 0 (10011)^3 (100)^4 (111001)^2005`).

## Halting

The only halting transition is F on a 0; F is entered only from B on a 1 (B writes 0 and moves right). In all phases
seen the cell F reads is a 1 inside the words.

## Status

Open. Kernel: halting configurations, 10,000 steps (`lean/Blank.lean`), phases A and B (`lean/Rules.lean`, from
`py/rules.py`). Native: 10^7 steps. Trusted: no halt in 10^10 steps (`c/ev.c`). The recycling step and the slow
phase B of later rounds are from simulation only.

## For later

* Prove the recycling step (it crosses the whole left block) and the end of phase B as rules; then the round map.
* Find the rules of the small counter in the later rounds.
* This machine and 1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE work the same way (drain one block into another,
  recycle, repeat at a larger size, with a small counter appearing at the fourth level).

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.46; right: sqrt,
exponent 0.615). After 1,000,000,000 steps: 52,423 cells visited (33,516 left of the
start, 6,210 right), 28,979 ones.

- left, step 971,060,506: `D>0 0 1^5 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^`
- left, step 986,716,579: `D>0 0 1^5 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^2 1^3 0^`
- right, step 977,566,375: `1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 `
- right, step 993,433,435: `1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 `

## Pages

- [`pages/holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/explainer.html`](../../pages/holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/explainer.html)
- [`pages/holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/proof-status.html`](../../pages/holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/lean/check.sh
gcc -O2 -o ev holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/c/ev.c && ./ev 1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB 2000000000 L D 1 100000 12 | awk 'NR%300==0'
```
