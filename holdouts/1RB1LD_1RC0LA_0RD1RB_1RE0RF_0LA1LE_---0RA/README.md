# 1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA

bbchallenge id 164391. One of the six-state holdouts whose halting from blank tape is open. The tape is a counter written as blocks of ones of lengths 6j+1; its rule is not decoded.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1RC | 0LA |
| C | 0RD | 1RB |
| D | 1RE | 0RF |
| E | 0LA | 1LE |
| F | --- | 0RA |

## What it does

The tape, read left to right, is a block `(100)^n` followed by a list of blocks of ones separated by `00`:

```
(100)^n  1^5 00 (1^7 00)^m1  ...  (1^13 00)^m2  ...  (1^19 00)^m3  ...  (1^25 00)^m4  ...
```

Almost all the blocks have length 6j+1 (7, 13, 19, 25, 31, 37, 43, ...), grouped by length in increasing order;
between two groups, and at the right end, there are a few short blocks (1, 3, 5, 9, 11, ...) where the work is going
on. Examples at the right end of the visited tape (n = the `(100)` count, then the block lengths, `7^54` for 54
blocks of length 7):

```
step   1,153,586   n=76   5 7^54 5 1^2 15 19^11 17 1 5 29 31 13 29 1^2 7 3 1
step   7,772,173   n=75   5 7^123 1 11 13^30 11 1^2 17 19^18 1 11 23 25^6 1 11 29 31^2 35^2 1^2 41^2 1^2 15 5
step  20,110,251   n=140  3 7^220 5 1^2 11 13^26 1 5 17 19^42 7 1 21 25^5 13 29 31^7 35 37 7 1 39 23 7 1 3 1^2 13 1
```

So it behaves like a counter with one digit per block length: the multiplicities of the 7s, 13s, 19s, ... change
from sweep to sweep, a new length appears from time to time (the number of groups grows slowly: lengths up to 31 at
10^6 steps, up to 37 or more at 2·10^7) and the `(100)` block on the left grows and shrinks. The head sweeps the whole tape again and again, each
sweep adding a few cells, so the width grows like the square root of the step count (width about the square root
of the step count, within 3%, from 10^4 to 2.5·10^7 steps). On the way it stops to rewrite the short blocks between
groups. How the multiplicities and the left block change at a group boundary has not been worked out.

The machine halts only in F reading 0, which needs D to read a 1 with a 0 to its right.

## Does it halt?

Unknown. Direct simulation: no halt in 10^11 steps. No rule for the counter is known, so there is no map to iterate
and no heuristic yet. **Open.**

## For later

Stopped at: the shape of the tape (above) only. Next steps:

1. Record, at each sweep, the list (n; lengths of all blocks) and find how one sweep changes it. Since the groups
   are separated by short blocks, a sweep is probably a carry that moves from group to group; look for the rule at
   one group boundary (`1^(6j+1) 00 <short blocks> 00 1^(6j+7)`) with `bbtools.symtm`, using contexts for the rest.
2. With that rule, write the counter map, check it against `tools/c/tmrun.c` runs, and iterate it much further.
3. Then prove its pieces with `bbtools.symtm` and chain them in Lean, as for the three-counter reductions of other
   holdouts in this collection.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the
kernel, in 10,000,000 by `native_decide`. C (`tools/c/tmrun.c`): no halt in 10^11 steps.

## Pages

- [`pages/holdouts/1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA/explainer.html`](../../pages/holdouts/1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA/explainer.html)
- [`pages/holdouts/1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA/proof-status.html`](../../pages/holdouts/1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB1LD_1RC0LA_0RD1RB_1RE0RF_0LA1LE_---0RA 100000000000     # running 100000000000 195666
```
