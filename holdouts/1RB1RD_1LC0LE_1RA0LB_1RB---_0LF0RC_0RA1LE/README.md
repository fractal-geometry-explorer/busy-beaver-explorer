# 1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE

bbchallenge id 105737. Its tape is a chain of long alternating blocks separated by single 1s; blocks are halved, one half merging into the next block, until one block is left, and then it is split again.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0LE |
| C | 1RA | 0LB |
| D | 1RB | --- |
| E | 0LF | 0RC |
| F | 0RA | 1LE |

## What it does

Stop the run when the head reaches a new cell (`a = 10`):

    96,586,116  C>0 a 0 a^610 0^2 1 a^202 1          (left end)
    97,150,995  F>0^2 a^306 0^2 1 a^305 1 a^202 1    (left end)
    97,437,314  1 a^308 1 a^305 1 a^202 1 A>0        (right end)
    97,500,752  1 a^308 1 a^406 0 a^102 1 A>0        (right end)
    97,534,323  C>0 a 0 a^307 0^2 a^509 1            (left end)
    97,681,430  0 a^154 0 a^664 1 A>0                (right end)
    99,010,412  C>0 a^820 1                          (left end)
    99,015,341  C>0 a 0 a^819 0^2 1                  (left end)

A chain of alternating blocks: a block is split in two (610 -> 306 + 305), blocks are halved with the other half merging
into a neighbour (202 -> 102 while 305 -> 406), until one block (820) is left and is split again.

## Halting

D1 halts; D is entered only from A1 (`1RD`), so a halt needs `A>1 1`. In the first 10^8 steps D was entered
106,974 times, always on a 0 (`c/sstat.c`). Open.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^12 steps (`c/mrun.c`, exact macro simulation). The structure described here is observed, not proved.

## First look

Growth class **power/power** (left: power, exponent 0.335; right: power,
exponent 0.335). After 1,000,000,000 steps: 3,565 cells visited (1,269 left of the
start, 1,617 right), 1,782 ones.

- left, step 978,301,074: `C>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- left, step 997,994,516: `C>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 971,233,462: `1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 990,594,758: `1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `



## Pages

- [`pages/holdouts/1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE/explainer.html`](../../pages/holdouts/1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE/proof-status.html)



## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE/lean/check.sh
gcc -O2 -o mrun holdouts/1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE/c/mrun.c && ./mrun 1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE 16 1000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE/c/sstat.c && ./sstat 1RB1RD_1LC0LE_1RA0LB_1RB---_0LF0RC_0RA1LE 100000000
```

## Later

- Find the exact split, halve and merge rules: a map on lists of block lengths.
- Then whether A can meet `A>1 1`.
