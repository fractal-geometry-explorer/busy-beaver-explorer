# 1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF

bbchallenge id 13552.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 1RC | 1LC |
| C | 1LD | 1RE |
| D | --- | 0LA |
| E | 1RE | 0RF |
| F | 1RA | 0LF |

## Status

**Open.** The macro structure below is read off long runs (heuristic: not yet stated as rules or proved); no
decision. Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## What it does

The two machines `1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF` and `1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF` differ only
in E0 (1LE or 1RE) and look alike. Next to the left end the tape is `(01)^4 (10101001)^n` followed by a long stretch
built from the words `10`, `01`, `0110`, `1001` (e.g. `(10)^10 010110100101 (10)^3 01100101100110 (1001)^3 ...`). The
block count n grows in long cycles, by about 50 per cycle (16, 65, 33, 82, 133, 183, ... at successive samples: it
also drops when a cycle restructures the boundary), and the stretch behind it changes only near its left end. The
halt is D0, reached only if the head reads a 0 in state D, which has not happened in 10^9 steps.

## For later

Find the cycle: what one long cycle does to n and to the boundary words; then whether the stretch behind is a
counter that can feed D a 0.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.525; right: fixed,
exponent 0.049). After 1,000,000,000 steps: 23,775 cells visited (18,423 left of the
start, 531 right), 12,567 ones.

- left, step 971,416,712: `B>0 0^2 1 0 1 0 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 `
- left, step 987,198,650: `B>0 0^2 1 0 1 0 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 `

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 256,132,772 | 10,390 | 177 | 24 | 98 | 0.95 |
| right | 288,785,204 | 10,846 | 95 | 27 | 90 | 0.97 |
| left | 1,024,087,802 | 23,968 | 3,025 | 382 | 139 | 0.74 |
| right | 2,797,177,046 | 33,802 | 72 | 24 | 72 | 0.99 |
| left | 4,096,047,796 | 49,202 | 12,699 | 1,581 | 90 | 0.48 |
| left | 16,384,178,554 | 83,440 | 2,441 | 298 | 118 | 0.94 |

**Proposed family: F11, defect gases and irregular zones** (a growing block (01101010)^n and behind it a zone written in the pairs 01 and 10; borderline F01).

At the left-end records the tape is `0^3 101 (01101010)^n` followed by a zone written in the pairs `01` and `10`. The block grows (n = 1,230 at 2.6·10^8 steps, 9,822 at 1.6·10^10). The zone has 98, 139, 90 and 118 level-2 tokens at the left-end records at 2.6·10^8, 10^9, 4.1·10^9 and 1.6·10^10 steps, so it did not grow on this screen. It does contain long waves: at 4.1·10^9 steps one 64-cell word is repeated 390 times inside it, at 1.6·10^10 steps 69 times, which is why the count of cells outside short repeats swings between 177 and 12,699.

On these numbers alone the machine fits F01 (two periodic blocks and about a hundred irregular tokens). It is put in F11 with its sister 1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF, whose zone of the same kind grows, because the zone is the engine and it is a word over two letters with no bound known. The two machines differ in one transition (E on 0) and their runs are different: nothing is claimed about one from the other. If a closed-set test is wanted, this is the one of the two to try.

Next step: The same reading of the zone as a binary word; in this machine also the life of one wave (the 64-cell word), from its birth to its end.

## Pages

- [`pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF/explainer.html`](../../pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF/explainer.html)
- [`pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF/proof-status.html`](../../pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF/lean/check.sh
```
