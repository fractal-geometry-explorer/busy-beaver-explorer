# 1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC

bbchallenge id 151599. One of the six-state holdouts whose halting from blank tape is open. (group G07).
Family: **zig-zag block converter feeding a growing irregular region**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1RC | 0LD |
| C | 1LB | --- |
| D | 1RA | 1LD |
| E | 1RA | 0RF |
| F | 1RE | 0LC |

## What it does

The tape has three parts: a fixed left part (a few hundred cells written in the first 10^6 steps, unchanged since),
an **irregular region** that grows to the right, and on the right a **block** of k copies of the 8-cell word
`01011111`, ending in `110`. One round trip of the head:

1. at the right end in state B, the head walks left through the block converting every word, the boundary moving
   about one word per 38 steps (**proved in Lean** for every k: `L (01011111)^(n+3) 1 1 B> 0  ->  L D> (11101000)^(n+3) 1101`
   in 38n+118 steps, `lean/Rules.lean`);
2. at the left end of the block it rewrites the last cells of the irregular region;
3. it walks right converting the block back, and adds a little at the right end.

Measured over the 10,115 visits of the right end in state B in the first 10^9 steps: each round trip changes the
tape by 4 cells, as (block +1 word, region -4 cells), (block -1 word, region +12 cells) or (block unchanged, region +4).
So the block and the region both grow linearly in the number of trips (k = 2,938 and region 17,196 cells at step
9.8·10^8). The rewrite at step 2 usually touches only the last 8-40 cells of the region, but it can reach much deeper:
its depth has a heavy tail (100 cells in about 3% of the trips, 1,000 in 0.3%, the deepest 3,160 cells). The
region behaves like the memory of a counter or a stack machine that the zig-zag drives.

Tape samples (periodic notation, `w^k` is the word w repeated k times; `X>b` is the head in state X on symbol b; a long middle is cut with `...`):

- step 10,000,000: `1^6 01^2 1^6 0 1^3 01^2 1^4 01^4 11010111^3 1 10111110^2 10 1^7 0 1111101011^2 10^2 1^11 01^4 11111101^2 011101^3 1^4 010111^3 111101011111^2 010111^2 1^4 01^2 1111011111^2 1^4 01^2 1^4 0 1^3 01^4 1^4 010111^2 1^6 010111^4 1^8 0 1^5 01^2 110 1^9 0111^2 1^6 0 1^17 01^2 1101^2 0 1^13 010111^2 1^4 01^2 1^6 0 1^9 01^2 1 10^3 1^13 01 ... 01^2 1 10^3 1^5 0 1^3 01^4 1111010111^2 11111101^2 0 1^5 01^2 1^6 0 1^5 01^3 111101^2 011101^2 0 1^7 01^2 111101^2 01^3 1^8 01^2 1 10111110^2 10 1^7 0 1^5 010111^4 110 1^9 0 1^5 0 1^3 01^3 111101^2 011101^2 0 1^7 011111^3 1 10^2 1^9 010111^2 111101^2 1 10111110^2 10 1^3 01^2 1^4 0 F>0 10 1^7 01^3 0^3 1^5 01000111^251 01 0^3 1101`
- step 100,000,000: `1^6 01^2 1^6 0 1^3 01^2 1^4 01^4 11010111^3 1 10111110^2 10 1^7 0 1111101011^2 10^2 1^11 01^4 11111101^2 011101^3 1^4 010111^3 111101011111^2 010111^2 1^4 01^2 1111011111^2 1^4 01^2 1^4 0 1^3 01^4 1^4 010111^2 1^6 010111^4 1^8 0 1^5 01^2 110 1^9 0111^2 1^6 0 1^17 01^2 1101^2 0 1^13 010111^2 1^4 01^2 1^6 0 1^9 01^2 1 10^3 1^13 01 ... 8 010111^2 111101^2 011101^3 1^6 01^2 11011111^2 011111^2 0 11101011^2 101011^4 1^5 010111^2 1^4 01^2 1^4 011101^2 1111111101^2 110 111110101111^2 101110^2 1^3 01^3 1^4 0 1^3 01^3 1^4 0 1^3 01^3 1^4 0 1^3 01^4 1^14 01^4 1^6 0 1^3 01^4 1101^2 1^8 01^6 1^12 01^2 1^6 01^2 1^4 0 11101011^2 11111010^889 1^4 A>1 10^2 0 11010001^35 101`
- step 1,000,000,000: `1^6 01^2 1^6 0 1^3 01^2 1^4 01^4 11010111^3 1 10111110^2 10 1^7 0 1111101011^2 10^2 1^11 01^4 11111101^2 011101^3 1^4 010111^3 111101011111^2 010111^2 1^4 01^2 1111011111^2 1^4 01^2 1^4 0 1^3 01^4 1^4 010111^2 1^6 010111^4 1^8 0 1^5 01^2 110 1^9 0111^2 1^6 0 1^17 01^2 1101^2 0 1^13 010111^2 1^4 01^2 1^6 0 1^9 01^2 1 10^3 1^13 01 ... ^4 01^4 1^8 01^2 1^6 01^2 1^4 0 1^7 01^4 1^10 01^2 1^8 01^4 1^6 011101^4 0 1^7 0 1^3 01^4 1^12 0101111111^2 1^8 01^2 1101^2 0 1^7 0 1^5 01^2 1101^2 0 1^7 011101^4 1 10^2 1^11 0 1^5 01^2 1101^2 01111111^2 0 1^5 0 1^3 01^4 1^10 0 1^5 01^2 1^6 0 1^3 01^2 1^10 01^2 1^10 01^2 1^10 01011111^159 011 B>1 10 1^5 01000111^2805 01 0^3 1101`

## Status

Open.

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`); `sweep_left` (`lean/Rules.lean`).
  **native_decide:** `blank_runs_native` (10^7 steps).
- **Trusted:** no halt in 10^9 steps (`tools/c/triage.c`); the statistics above from `tools/c`-based runs.
- **Open:** the rule of the region rewrite (step 2) and the halting question. The halting transition is C1; C is entered
  only as B0 -> 1RC or F1 -> 0LC, so a halt is B reading 0 before a 1, or F reading 1 after a 1. A closed tape
  language search (`bbtools.ctl`, windows of 4 and 6) leaves such halts possible anywhere.

## Next steps

Find the rewrite of the region as a function of its last few "digits" (the depth statistics suggest a counter or a
stack whose items are short words), prove the rightward sweep with `bbtools.symtm` (it depends on the region's last
cells), and decode the region.

## Pages

- [`pages/holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/explainer.html`](../../pages/holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/explainer.html)
- [`pages/holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/proof-status.html`](../../pages/holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/lean/check.sh
```
