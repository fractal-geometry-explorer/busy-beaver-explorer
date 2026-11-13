# 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF

bbchallenge id 68273. An abacus of a few blocks of 1s: sweeps move units between neighbouring blocks, blocks merge, and a big block is split into about a third and two thirds; the block lengths evolve chaotically.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 0RC | 0RF |
| C | 1LC | 0LA |
| D | 0LE | 1LD |
| E | 1LA | --- |
| F | 0RB | 0LF |

## What it does

The tape is a few blocks of 1s separated by runs of two, three or five 0s. Sweeps move single 0s through the
blocks: `0 C> 1^n -> 1^n 0 C>` in 3n steps (`lean/Rules.lean`, `c_shift`, kernel). Each crossing moves units from
one block to its neighbour. Blocks merge (126, 40 -> 168 at step 150,135), and large blocks are cut in a ratio
close to 1:2 (1041 -> 347, 700 between steps 12,174,442 and 12,902,116). At the times C stands at the right end:

    12,164,477   2 . 13 . 1009      (block lengths; 0^2 between)
    12,902,116   347 . 700
    13,724,275   14 . 345 ___ 693   (0^5)
    14,048,610   14 . 345 . 231 . 464

No rule for the lengths has been found; they look chaotic. The ones grow slowly (6,891 at 3e9 steps).

## Status

Open. Kernel: the halting configurations, no halt in 10^4 steps (10^7 native), the travelling-0 rule. Halting
needs E to read a 1. CTL (K = 2..5) and NGramCPS (widths 2-8, -H, -U) fail.

## For later

A rule on the block lengths is the missing piece. Next steps: list all sweep types (by the separator pattern)
and prove each as a symtm rule in the block lengths; then study the induced map on length vectors (mod 3 looks
relevant). More than a day of work.

## Reproduce

```sh
./tmrun 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF 3000000000 at C R 100000
. /etc/profile.d/lean.sh && holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/explainer.html`](../../pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/explainer.html)
- [`pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/proof-status.html`](../../pages/holdouts/1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF/proof-status.html)
