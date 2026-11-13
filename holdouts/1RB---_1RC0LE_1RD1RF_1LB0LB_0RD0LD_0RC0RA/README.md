# 1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA

bbchallenge id 165799.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1RC | 0LE |
| C | 1RD | 1RF |
| D | 1LB | 0LB |
| E | 0RD | 0LD |
| F | 0RC | 0RA |

## Status

**Open.** Phases of transfer between long runs of period-6 and period-9 words; the frozen runs it leaves behind shrink by ratios close to 3/2, the mark of a Collatz-like map (not extracted).

## What it does

The tape is built from long runs of a few periodic words, mostly `100010000` (period 9), `000100`/`000001`
(period 6) and `000010001`, separated by short markers such as `1 000 10101` or `01 00000 1`. Watching the head,
in state D, at the left end of the tape (`py/view.py 2e9 1500 blocks D L 9`):

- The work is a slow **transfer** between the first two runs: every second visit one period-6 word leaves the first run
  and one period-9 word joins the second (`(000100)^5207 ... (100010000)^870` at 5.5·10^8 steps,
  `(000100)^4534 ... (100010000)^711`, then `^3784 / ^1461`, `^3034 / ^2211`, ... `^34 / ^5211`: 750 per 1,500
  visits).
- When the first run is used up a new phase starts with different words (`(000001)^715 (01)^3 (000001)^714
  (000010001)^4533` at 8.1·10^8, the two period-6 runs growing by one every two visits each while the period-9 run is
  spent), and so on through a short cycle of phases; each phase leaves a marker and a run behind it.
- Further right the tape is frozen history: runs of `010000100` of lengths 133, 88, 58, 38, 15 (ratios close to
  3/2) and runs of `100010000` of lengths 908, 302, 200.

The ratios near 3/2 between consecutive frozen runs suggest that the phases implement a Collatz-like map (a value
multiplied by about 3/2 per phase, with a remainder deciding the next phase), as in other BB(6) holdouts, but the
exact map has not been extracted.

## Results

- `py/view.py` (with `c/blocks.c`, `c/gaps.c`) prints the views of the run quoted above; `python3 py/view.py 2e9 1500 blocks D L 9` is the block view of the transfer phases.
- Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.
- No macro rule is proved yet. Next step: prove the transfer round with symtm, list the phases and their transitions, and extract the induced map (it may give an exact halts-iff statement).

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.444; right: fixed,
exponent 0.0). After 1,000,000,000 steps: 73,042 cells visited (46,778 left of the
start, 32 right), 40,382 ones.

- left, step 969,934,502: `B>0 0^6 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^`
- left, step 985,586,922: `B>0 0^6 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^5 1 0^`

## Pages

- [`pages/holdouts/1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA/explainer.html`](../../pages/holdouts/1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA/explainer.html)
- [`pages/holdouts/1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA/proof-status.html`](../../pages/holdouts/1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1RC0LE_1RD1RF_1LB0LB_0RD0LD_0RC0RA/lean/check.sh
```
