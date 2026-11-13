# 1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD

bbchallenge id 180739. One of the six-state holdouts whose halting from blank tape is open (group G13). Family: **array of (10)-counters behind a growing (10) run**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1LC | 1LB |
| C | --- | 1LD |
| D | 1RA | 0RE |
| E | 1RD | 0LF |
| F | 1LE | 0LD |

## What it does

Write a for the pair 1 0. Each time the head is at the left end in state E, the tape reads E>1 a^N 1^2 0 1^2 0 a^K 1^2 0 &hellip;: a long run of N pairs, two markers, a second long run of K pairs, and then many shorter runs of pairs, each followed by a marker 1^2 0 or 1 0^2. At step 2,157,249 N = 527 and K = 385; at step 19,526,315 N = 1,052 and K = 964.

So the tape looks like an array of counters, each a run of pairs, and the two kinds of markers look like a bit attached to each counter. The head sweeps the whole array; how one sweep changes the counters is not yet worked out.

### Halting

The machine halts when it reads a 0 in state C (C0 is the halting transition). C is entered from B on a 0 (B0 = 1LC), so a halt needs 0 B>0 reached moving left, which needs two adjacent 0s. Inside the word the only double 0s are in the markers 1 0^2.

## Phase 2 results

`lean/Rules.lean` proves three shift rules for every n (D and A over `(10)^n`, E over `(01)^n`).
`py/leftcounter.py` checks the left-end counter: at F-left samples `F>0 0 a^n X Y W` (a=10, P=110, Q=100), (X,Y)
cycles (P,P) (Q,P) (P,Q) (Q,Q) (P,aP) (Q,aP), with n going up by 7 per cycle; in 10^9 steps 981 transitions follow it
(164 cycles), and 4 at the start do not; the last n is 1151. The rest of the tape W changes too and has no map yet.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel) and 10^7 (`native_decide`). C: no halt in 10^9 steps. Lean (`lean/Rules.lean`, kernel): the shift rules `shiftD`, `shiftA` (over `(10)^n`, leaving `(01)^n`) and `shiftE` (over `(01)^n`, leaving `(10)^n`), for every n and any surrounding tapes. Trusted: the left-end six-step counter (`py/leftcounter.py`). The full map is not found.

## Later

1. Sample at E-left and at the right end; write each tape as a list of (pair count, marker) and find the sweep rule.
2. Check whether the two long runs N and K grow linearly in the number of sweeps and what feeds them.
3. Look at what happens when a counter between markers reaches 0 (the only place a double 0 could meet B).

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| right | 256,000,097 | 114,381 | 2,011 | 5,728 | 6,654 | 0.02 |
| right | 1,024,003,651 | 419,103 | 6,763 | 21,218 | 24,137 | 0.01 |
| right | 4,096,008,437 | 1,661,759 | 26,591 | 84,911 | 96,613 | 0.00 |
| right | 16,384,032,961 | 6,668,265 | 103,396 | 341,205 | 387,336 | 0.00 |

**Proposed family: F11, defect gases and irregular zones** (a working zone at the right end that moves right and leaves a frozen irregular sea behind).

This machine stopped being a bouncer early in the run. The last new cell on the left (cell −1,973) was reached before step 6.4·10^7, and since then the head has stayed near the right end: in the eight successive doublings of the step count from 6.4·10^7 to 1.6·10^10 its greatest distance from the rightmost visited cell was 19,277, 24,350, 25,882, 29,767, 35,564, 39,489, 41,342 and 37,190 cells (`c/front.c`), while the right end moved from cell 54,852 to cell 6,666,290, in proportion to the steps (about 0.4 cells per 1,000 steps).

What is left behind is frozen and does not compress: 24,137, 96,613 and 387,336 level-2 tokens at 10^9, 4.1·10^9 and 1.6·10^10 steps for 419,103, 1,661,759 and 6,668,265 cells (one token per 17 cells each time). It is runs `(10)^k` and `(01)^k` with k mostly below 40, separated by single cells. The first 4,400 cells (`(10)^1153 111 (01)^1054 …`) are the same at the three records.

So the description is not bounded and the tape is not a list that is swept: it is an irregular sea written once by a zone of some tens of thousands of cells at the right end. F11. The zone itself is where a proof would have to work; its depth grew by a factor of about 2 while the tape grew by a factor of about 120.

Next step: Describe the working zone: the tape within 50,000 cells of the right end at successive records, compressed, to see whether it is a counter of slowly growing length that is carried along.

## Pages

- [`pages/holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/explainer.html`](../../pages/holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/explainer.html)
- [`pages/holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/proof-status.html`](../../pages/holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/lean/check.sh
python3 holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/py/leftcounter.py 1000000000
```
