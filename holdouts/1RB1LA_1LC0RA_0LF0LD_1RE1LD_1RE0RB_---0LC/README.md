# 1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC

bbchallenge id 40644. The tape is a chain of long solid blocks separated by single 0s; the last block is halved over and over, each half moving into the block before it, and the chain is rebuilt, sometimes as a ladder of doubling lengths.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 1LC | 0RA |
| C | 0LF | 0LD |
| D | 1RE | 1LD |
| E | 1RE | 0RB |
| F | --- | 0LC |

## What it does

Stop the run when the head reaches a new cell on the right, in state B (`e = 10`):

    42,818,030  1^323 e 1^320 e 1^642 e 1^114 e B>0
    43,323,699  1^323 e 1^673 e 1^349 e 1^57 e B>0
    43,327,240  1^323 e 1^673 e 1^381 e 1^28 e B>0
    43,486,171  1^323 e 1^874 e 1^197 e 1^14 e B>0

Solid blocks separated by single 0s. The last block is halved again and again and the blocks before it are
rearranged at the same time; now and then the chain is rebuilt, sometimes as a ladder of nearly doubling lengths
(`1^5 e 1^2 e 1^6 e 1^13 e 1^27 e 1^55 e 1^111 e 1^223 e 1^447 e 1^546 e 1^66 e e A>0` at step 55,813,373).
After 10^9 steps 4,081 of the 4,093 visited cells hold a 1.

## Halting

F0 halts; F is entered only from C0 (`0LF`), so a halt needs two adjacent 0s where C steps left. In the first 10^8
steps F was entered 93,754 times, always on a 1 (`c/sstat.c`). Open.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`. C: no halt in 10^9 steps (`tools/c/triage.c`) and in 10^12 steps (`c/mrun.c`, exact macro simulation). The structure described here is observed, not proved.

## First look

Growth class **power/power** (left: power, exponent 0.285; right: power,
exponent 0.347). After 1,000,000,000 steps: 4,093 cells visited (190 left of the
start, 3,121 right), 4,081 ones.

- left, step 948,184,374: `D>0 1^2793 0^3 1 0^2 1^1191 0^2 1^53 0^2 1`
- left, step 993,047,219: `D>0 1^2636 0^3 1 0^2 1^918 0^2 1^472 0^2 1^53 0^2 1`
- right, step 958,450,821: `1^352 0 1^349 0 1^699 0 1^1398 0 1^1192 0 1^54 0^2 A>0`
- right, step 977,921,177: `1^352 0 1^1839 0 1^1487 0 1^354 0 1^40 0 A>0`



## Pages

- [`pages/holdouts/1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC/explainer.html`](../../pages/holdouts/1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC/explainer.html)
- [`pages/holdouts/1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC/proof-status.html`](../../pages/holdouts/1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC/proof-status.html)



## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC/lean/check.sh
gcc -O2 -o mrun holdouts/1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC/c/mrun.c && ./mrun 1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC 16 1000000000000
gcc -O2 -I tools/c -o sstat holdouts/1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC/c/sstat.c && ./sstat 1RB1LA_1LC0RA_0LF0LD_1RE1LD_1RE0RB_---0LC 100000000
```

## Later

- Find the exact map on the list of block lengths (halving, rearranging, rebuilding).
- Then whether two adjacent 0s can appear where C steps left (the F0 halt).
- Compare with `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA`, which also halves its last block.
