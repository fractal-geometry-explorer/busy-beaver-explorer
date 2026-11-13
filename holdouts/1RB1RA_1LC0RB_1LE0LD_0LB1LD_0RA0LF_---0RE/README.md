# 1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE

bbchallenge id 46435. Open. A **nested drain/copy counter**: a few long blocks `(010)^a` are poured, one after the other, into a final
block `(01011)^b` (b gains 7 cells per 2 pairs drained); when all are poured, the final block is copied back out as
new `(010)` blocks and the next level starts, roughly eight times larger. The two main phases are proved in Lean as
one-cycle rules for all block sizes.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RB |
| C | 1LE | 0LD |
| D | 0LB | 1LD |
| E | 0RA | 0LF |
| F | --- | 0RE |

## The tape as words

At the left end of the tape (head on the new leftmost cell) the tape reads, apart from a few cells at each end,

    (010)^a1 1 1 1 ... (010)^ak 1 1 1 (01011)^b 0 1

e.g. step 33,886,934: `0 0 1 1 0 1 0 0 1 0 1 1 (010)^888 1 1 1 0 1 0 0 1 0 1 1 (010)^906 1 1 1 (01011)^981 0 1`.
During a rightward sweep the same blocks show up as rotations of the words (`001`, `00111`, `11100`, `10011`).

## Phases

| phase | tape at the left end | one cycle | proof |
|---|---|---|---|
| drain | `0^inf E>(011)^4 (010)^(a+6) 111 (01011)^(b+1) 0 1` | a-4, b+14, 16 visits, 168a+224b+2978 steps | `drain`, `lean/Rules.lean` |
| split | `0^inf B>0 0 (110101)^c 1101 (100)^(d+3) 10 111 (01011)^(b+1) 0 1` | c+1, d-2, b+2, 4 visits, 32b+50c+24d+228 steps | `split`, `lean/Rules.lean` |
| feed | `(110101)^c 1 1 [short (010) blocks] (010)^e 111 (01011)^b` | c-1, b+~5; the short blocks count | simulation |

(Both rules are for every value of the variables, kernel-checked; `py/rules.py` writes `lean/Rules.lean`.)

When the last `(010)` block is empty the next one to its left drains; when none is left a long copy phase writes the
final block back as a fresh `(010)` block of the same length. Levels seen (the tape at each copy):

| step | tape |
|---|---|
| 5,355 | `(010)^12 111 (01011)^13` |
| 284,266 | `(010)^107 111 (01011)^108` |
| 19,588,355 | `(010)^906 111 (01011)^907` |
| 1,255,481,375 | `(010)^7265 111 (01011)^7265` |
| 6,126,135,498 | `(110101)^3634 1 1 (010)^14532 111 (01011)^14531` |

At the fourth level the split phase appears: the block being drained gives half of itself to a new block
`(110101)^c` at the left end (c reached 3,634) and the other half to the final block; then in the feed phase the
`(110101)` block is fed back one word every few sweeps through a small counter of short `(010)` blocks, which looks
like the whole process again at a small scale. At step 9,775,936,642: `(110101)^2158 1 1 (010)^4 1 1 (010)^4 ...
(010)^14520 111 (01011)^21906`.

## Halting

The only halting transition is F on a 0, and F is entered only from E reading a 1 (moving left). In every phase above
the cell F then reads is a 1 inside the words; a halt needs a phase boundary that puts F next to a 0, which has not
happened in 10^15 steps (accelerated simulator below).

## Copy phase and the accelerated run

The copy phase is now a proved rule (`copy` in `lean/Rules.lean`, kernel): one visit of the right end,

    L (01111)^(n+2) (010)^(m+1) 0 1111 (00111)^(m+1) B> 0^inf   --28m+55 steps-->   same with n-1, m+1

for every n, m and every tape L. A feed round (32b+34c+24d+3813 steps, found by `bbtools.symtm`) is too long for the
kernel to check in reasonable time and memory, so it is described here but not in Lean.

`c/hsim2.cpp` is a block macro simulator that takes a linear jump over k cycles only after checking the cycle
symbolically for every larger count, summing the step count exactly. `py/cmpc.py 5e10` checks it against plain
simulation (`c/dump.c`): state and all 357,144 cells agree at 50,000,245,146 steps. It runs to 1.05e15 steps with no
halt. Final-block size at each copy (heuristic reading of its output):

| b | step |
|---|---|
| 13 | 5.4e3 |
| 108 | 2.8e5 |
| 907 | 1.96e7 |
| 7,265 | 1.26e9 |
| 14,531 (after split) | 6.1e9 |
| 33,000 | 1.67e10 |
| 83,545 | 1.66e11 |
| 375,963 | 3.37e12 |
| about 3.0e6 | 2.15e14 |
| about 6.0e6 (after split) | 5.4e14 |
| 6,015,471 | 1.05e15 |

At 1.05e15 the tape is `(011101)^1503867 (001)^6015471 01110 (10110)^6015471`. The ratios depend on which phase
starts, so the level map looks Collatz-like; its exact form is not derived.

## Status

Open. Kernel: halting configurations and 10,000 steps (`lean/Blank.lean`), the drain and split cycles
and the copy cycle (`lean/Rules.lean`). Native: 10^7 steps. Trusted: no halt in 10^15 steps (`c/hsim2.cpp`, checked
cell for cell at 5e10 by `py/cmpc.py`). The feed phase and the transitions between phases are described from
simulation only.

## For later

* Prove the feed round (split it into shorter pieces the kernel can check) and the phase transitions as rules, then the level map
  as a function of the block sizes.
* The feed phase has a small counter in the middle; find its rules (it may be the same machine one level down).
* `python3 -m bbtools.cycles` with block size 15 accelerates the run with proved cycles; a long run of it would show
  the next levels.

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.638; right: sqrt,
exponent 0.46). After 1,000,000,000 steps: 53,968 cells visited (8,338 left of the
start, 31,625 right), 29,068 ones.

- left, step 500,184,998: `E>0 1^2 0 1 0 1 0 1^2 0 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0 1^3 0 1 0 1^2 0 1 0 1^2 0 1 0 1^`
- left, step 515,991,454: `E>0 1^2 0^2 1 0 1^2 0 1 0^2 1 0 1^3 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 0 1^2 0 1 `
- right, step 970,063,711: `0 1 0^2 1^4 0 1^4 0^2 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^`
- right, step 985,818,289: `0 1 0^2 1^4 0 1^4 0^2 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^4 0 1^`

## Pages

- [`pages/holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/lean/check.sh
gcc -O2 -o ev holdouts/1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE/c/ev.c && ./ev 1RB1RA_1LC0RB_1LE0LD_0LB1LD_0RA0LF_---0RE 2000000000 L B 1 100000 12 | awk 'NR%200==0'
```
