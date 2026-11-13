# 1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF

bbchallenge id 111009.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 1RC | 1LC |
| C | 1LD | 1RE |
| D | --- | 0LA |
| E | 1LE | 0RF |
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

Growth class **fixed/sqrt** (left: sqrt, exponent 0.519; right: fixed,
exponent 0.037). After 1,000,000,000 steps: 19,947 cells visited (14,708 left of the
start, 1,070 right), 10,929 ones.

- left, step 972,080,027: `B>0 0^2 1 0 1 0 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 `
- left, step 987,886,051: `B>0 0^2 1 0 1 0 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 0^2 1^2 0 1 0 1 `

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 256,392,705 | 11,364 | 955 | 133 | 466 | 0.40 |
| right | 1,002,910,013 | 19,970 | 229 | 58 | 210 | 0.96 |
| left | 1,024,171,037 | 20,208 | 283 | 35 | 138 | 0.96 |
| right | 1,033,700,217 | 20,278 | 221 | 52 | 223 | 0.97 |
| left | 4,096,535,933 | 41,868 | 2,417 | 302 | 1,119 | 0.86 |
| right | 6,122,920,685 | 48,724 | 290 | 75 | 294 | 0.98 |
| left | 16,384,435,612 | 85,732 | 7,101 | 918 | 3,202 | 0.74 |

**Proposed family: F11, defect gases and irregular zones** (a growing block (01101010)^n and behind it a zone without period, written in the pairs 01 and 10, that grows).

At the left-end records the tape is `0^3 101 (01101010)^n` followed by a zone that is a sequence of the pairs `01` and `10` without a period. The block grows (n = 2,438 at 10^9 steps, 7,909 at 1.6·10^10), and so does the zone: 466, 138, 1,119 and 3,202 level-2 tokens at the left-end records at 2.6·10^8, 10^9, 4.1·10^9 and 1.6·10^10 steps (955, 283, 2,417 and 7,101 cells outside every repeat). In the macro simulator (blocks of 8 cells) the tape has up to 25,746 runs by 10^13 steps.

The zone is not bounded and has no block structure of its own, so this is not a bounded engine (F01) and not a list of counters (F06). It belongs with the irregular zones of F11. The sister machine 1RB0LB_1RC1LC_1LD1RE_---0LA_1RE0RF_1RA0LF differs in one transition (E on 0) and its zone stayed small on the same screen; the two runs are different and nothing is claimed about one from the other.

Next step: Read the zone as a binary word (`01` and `10` as two letters) and look for the rule that rewrites it once per round; a cellular-automaton rule is the first thing to test.

## Pages

- [`pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/explainer.html`](../../pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/explainer.html)
- [`pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/proof-status.html`](../../pages/holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_1RC1LC_1LD1RE_---0LA_1LE0RF_1RA0LF/lean/check.sh
```
