# 1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB

bbchallenge id 36498. The tape is a few long solid blocks separated by single 0s; at the left end the first block is cut in the ratio 3 : 1 again and again, and at the right end the blocks are merged back into two.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RC |
| C | --- | 0LD |
| D | 0LE | 0RF |
| E | 1RE | 0RA |
| F | 0LF | 1LB |

## What it does

Stop the run when the head reaches a new cell (`b = 110`):

    86,757,128  1^801 b 1^265 A>0                              (right end)
    86,815,264  E>0^3 1^997 b 0^2 1^67                          (left end)
    87,568,755  E>0^3 1^744 b 0 b 0 1^248 b 1^67
    87,989,880  E>0^3 1^557 b 0^2 1^187 b 0 1^248 b 1^67
    88,227,031  E>0^3 1^414 b 0 b 0 1^138 b 1^187 b 0 1^248 b 1^67
    88,485,699  E>0^3 1^394 b 1^165 b 1^187 b 0 1^248 b 1^67
    88,915,154  1^573 b 1^501 A>0                              (right end)

Solid blocks separated by single 0s. At the left end the first block is cut again and again in the ratio about 3:1
(997 -> 744 + 248, 744 -> 557 + 187, 557 -> 414 + 138); then at the right end the blocks are merged into two and the
next round starts.

## Halting

C0 halts; C is entered from B0 (`1LC`) and B1 (`0RC`). In the first 10^8 steps C was entered 16,645,884 times,
always on a 1 (`c/sstat.c`). Open.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^12 steps (`c/mrun.c`, exact macro simulation). The structure described here is observed, not proved.

## First look

Growth class **power/power** (left: power, exponent 0.336; right: power,
exponent 0.318). After 1,000,000,000 steps: 2,359 cells visited (1,106 left of the
start, 819 right), 2,352 ones.

- left, step 971,008,612: `E>0 0^2 1^2281 0^2 1^2 0^2 1^54`
- left, step 988,766,858: `E>0 0^2 1^1762 0^2 1^585`
- right, step 959,983,502: `1^3 0 1^2326 A>0`
- right, step 982,330,200: `1^9 0 1^2338 A>0`



## Pages

- [`pages/holdouts/1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB/proof-status.html)



## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB/lean/check.sh
gcc -O2 -o mrun holdouts/1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB/c/mrun.c && ./mrun 1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB 12 1000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB/c/sstat.c && ./sstat 1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB 100000000
```

## Later

- Find the exact cutting rule (n -> (3n + c)/4 and its remainders) and the merging rule: a map on block lengths.
- Then whether B can meet the C0 pattern.
