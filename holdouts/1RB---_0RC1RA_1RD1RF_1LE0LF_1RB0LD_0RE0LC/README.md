# 1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC

bbchallenge id 87823.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 1RA |
| C | 1RD | 1RF |
| D | 1LE | 0LF |
| E | 1RB | 0LD |
| F | 0RE | 0LC |

## Status

**Open.** The counter passes are described and checked against the simulator over 10^8 steps (`py/passes.py`); the
rare rebuilds of the left part are not understood, so there is no decision. No halt in 2·10^10 steps.

## What it does

Look at the tape every time the head, in state D, stands on the blank cell just right of it, and read it in two-cell
symbols P = `01`, Q = `11`, aligned to the right end. Group the symbols as P^p Q^q, written `p.q`. The right part of
the tape is then

`... digit W^n digit W^n ... digit W^n end`

with the background word W = `2.2` (`01011111`), the four digit values a = `2.5`, b = `2.1`, c = `3.4`, d = `4.3`,
and end = `1.0` or `3.0` (alternating). One pass (the head runs left in a zigzag, turns, and runs back to the right
end) does this:

- the lowest digit steps a → b → c → d → a;
- a digit steps exactly when the digit to its right made the step d → a or a → b (a carry); the pass ends at the
  first digit whose step is b → c or c → d;
- the W runs change length by at most one per pass; over a full digit cycle a run grows by one, and the runs roughly
  double from one digit to the next (3, 8, 16, 33, 67, 133, 266, 535 at step 2.9·10^7).

So each digit moves half as often as its right neighbour: a binary counter written with four-valued digits.

A carry that leaves the top digit enters an irregular left part with other groups (`2.3`, `2.6`, `3.5`, `6.8`, ...).
Ten times so far (steps 38, 107, 251, 394, 726, 1,603, 1,979, 5,272, 39,576 and 29,787,121) the head went all the way
to the left end of the tape in state C, and the whole tape was rebuilt. After the tenth rebuild the tape is a row of
two-digit counters separated by `2.3` groups (`... 2.3 W^68 b W^67 b W^405 ...`), and new `2.3` groups are born at the
right end and travel left; the passes there follow further rules that were not derived. No eleventh visit to the left
end happens before step 2·10^10.

The machine halts only if state B reads `1 1` (possibly after some `1 0` pairs), which would have to happen in one
of the irregular parts; in the counter passes it does not.

## Results

- `py/passes.py [STEPS]`: checks the digit rule at every pass against `tools/c/tmrun` (10^8 steps: 4,133 passes, 2,480
  of them in the regular form, all following the rule; the others have no digit right of the last other group) and
  lists the visits to the left end (trusted).
- `./tmrun M 20000000000 at C L 100`: the ten visits to the left end, none between 29,787,121 and 2·10^10 (trusted).
- Lean (`lean/Blank.lean`): no halt in 10^7 steps; C (`tools/c/triage.c`): none in 10^9.

## For later

The whole pass is a finite-state rewriting of the P/Q word (once right to left, once left to right). Deriving that
transducer exactly (including the groups `2.3`, `3.5`, `2.6`, `6.8` and the ends `4.0`) is the next step; a nonhalting
proof then needs a description of all tapes that the rebuilds can produce.

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.029; right: sqrt,
exponent 0.522). After 1,000,000,000 steps: 52,296 cells visited (37 left of the
start, 38,610 right), 37,690 ones.

- right, step 970,815,087: `1^7 0 1 0 1 0 1 0 1 0 1^5 0 1 0 1^3 0 1 0 1 0 1^5 0 1 0 1^3 0 1 0 1 0 1^5 0 1 0 1 0 1^13 0 1 0 1 0 1 0 1^7 0 1 0 1^3 0 1 0 1^3 0 1 0 1^7 0 1 0 1^7 0 1 0 1 0 1^9 0 1 0 1^7 0 1 0 1^3 0 1 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1^3 0 1 0 1^5 0 1 0 1^5 0 1 0 1^3 0 1 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1^7 0 1 0 1^5`
- right, step 986,487,677: `1^7 0 1 0 1 0 1 0 1 0 1^5 0 1 0 1^3 0 1 0 1 0 1^5 0 1 0 1^3 0 1 0 1 0 1^5 0 1 0 1 0 1^13 0 1 0 1 0 1 0 1^7 0 1 0 1^3 0 1 0 1^3 0 1 0 1^7 0 1 0 1^7 0 1 0 1 0 1^9 0 1 0 1^7 0 1 0 1^3 0 1 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1^3 0 1 0 1^5 0 1 0 1^5 0 1 0 1^3 0 1 0 1^5 0 1 0 1^5 0 1 0 1^5 0 1 0 1^7 0 1 0 1^5`

## Pages

- [`pages/holdouts/1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC/explainer.html`](../../pages/holdouts/1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC/explainer.html)
- [`pages/holdouts/1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC/proof-status.html`](../../pages/holdouts/1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC/lean/check.sh
```
