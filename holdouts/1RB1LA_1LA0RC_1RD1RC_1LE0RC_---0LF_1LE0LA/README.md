# 1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA

bbchallenge id 78424. The tape is a chain of long solid blocks separated by single 0s, with an alternating tail; the last block is halved over and over, each half moving into the block before it, and the chain is rebuilt when it runs out.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 1LA | 0RC |
| C | 1RD | 1RC |
| D | 1LE | 0RC |
| E | --- | 0LF |
| F | 1LE | 0LA |

## What it does

Stop the run when the head reaches a new cell on the right, in state C (`e = 10`):

    75,796,004  1 e 1^594 e 1^770 e 1^362 e 1^98 e 1^2 e^170 C>0
    75,802,726  1 e 1^594 e 1^771 e 1^413 e 1^49 e 1 e^170 C>0
    75,806,544  1 e 1^594 e 1^772 e 1^441 e 1^25 e^171 C>0
    75,808,532  1 e 1^594 e 1^773 e 1^455 e 1^12 e^171 C>0
    75,918,988  1 e 1^595 e 1^1005 e 1^230 e 1^6 e^171 C>0
    75,949,808  1 e 1^596 e 1^1123 e 1^116 e 1^3 e^171 C>0

Solid blocks separated by single 0s, and an alternating tail `e^k`. The last block is halved again and again (98, 49,
25, 12, 6, 3), its ones going to the block before; when it is used up the tail gains one `10` and the halving moves
one block left. Now and then the chain is regrouped into a few blocks of nearly equal length.

## Halting

E0 halts; E is entered from D0 and F0 (`1LE`). In the first 10^8 steps E was entered 273,805 times, always on a
1 (`c/sstat.c`). A halt needs two adjacent 0s where D or F turns left. Open.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^15 steps (`c/mrun.c`, exact macro simulation). The structure described here is observed, not proved.

## First look

Growth class **power/power** (left: power, exponent 0.286; right: power,
exponent 0.341). After 1,000,000,000 steps: 5,303 cells visited (314 left of the
start, 3,953 right), 4,922 ones.

- left, step 934,066,380: `A>0 1^485 0 1^483 0 1^855 0 1^1598 0 1^991 0 1^8 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1`
- left, step 953,933,758: `A>0 1^1325 0^2 1 0 1^1325 0 1^656 0 1^603 0 1^466 0 1^70 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1`
- right, step 981,589,538: `1 0 1^43 0 1^392 0 1^1663 0 1^1312 0 1^972 0 1^131 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0`
- right, step 997,892,384: `1^2 0 1^1226 0 1^2205 0 1^1023 0 1^79 0 1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `



## Pages

- [`pages/holdouts/1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA/explainer.html`](../../pages/holdouts/1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA/explainer.html)
- [`pages/holdouts/1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA/proof-status.html`](../../pages/holdouts/1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA/proof-status.html)



## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA/lean/check.sh
gcc -O2 -o mrun holdouts/1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA/c/mrun.c && ./mrun 1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA 2 1000000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA/c/sstat.c && ./sstat 1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA 100000000
```

## Later

- Find the exact halving rule (what happens to odd lengths, which block receives the ones) and the regrouping rule.
- From that, a map on the list of block lengths; then whether a block of length 0 can occur (the E0 halt).

## Accelerated run

Trusted computation: `python3 tools/py/bbtools/rleaccel.py 1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA 2 2048000000` runs 2,048,000,000 macro steps from blank tape without a halt, more than 3.02·10^21
machine steps (tape: 88,969,302 cells). The simulator codes the tape in runs, crosses a run in one step and jumps cycles whose
one-cycle rule it has first proved symbolically; it is tested cell for cell against direct runs
(`tools/tests/test_rleaccel.py`).
