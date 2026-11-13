# 1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---

bbchallenge id 82729. Most of the tape is one 24-cell word repeated (100100100100100000100000 and its shifts) together with related periodic words; a few defects separate regions of different phase, and the sweeps move them and lengthen the regions.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 1RC | 1RF |
| C | 0RD | 0LB |
| D | 1LD | 0RA |
| E | 0LA | 0LE |
| F | 0RC | --- |

## What it does

Half or more of the tape (48%-63% at the samples, rising) is the 24-cell word `100100100100100000100000` (and its shifts) repeated, e.g. (E at the left end)

    64,104,641   E> 0^6 (100100100100100000100000)^125 001000 001000 (001)^9 (000001)^4 (001)^8 ...
    256,099,511  E> 000 10 11 (001001000001000001001001)^250 001 001 0000 10 11 (001)^6 (000001)^4 ...

Short defects separate regions of different phase. The right sweep crosses whole runs (`lean/Rules.lean`, kernel):
`C> (011)^n -> (110)^n C>`, `C> (011111)^n -> (111110)^n C>`. The leftmost region gains copies of the word
(15, 21, 30, 62, 125, 176 at steps 1e6 ... 1.28e8). The left side grows like sqrt(steps), the right like a smaller
power.

## Status

Open. Kernel: halting configurations, no halt in 10^4 steps (10^7 native), the two crossing rules. Halting needs F
to read a 1 (F is entered from B1). CTL (K = 2..5) and NGramCPS (widths 2-8, -H, -U) fail; a CTL with windows at
least as long as the period (24) and a defect alphabet might work and is the natural next try.

## For later

1. Tokenize the tape by the 24-cell word in its phases and list the defects.
2. Prove the passage of each defect type through a left and a right sweep with symtm.
3. Try CTL / NGramCPS with K >= 24 or a custom automaton built from the word and the defects.

## Reproduce

```sh
./tmrun 1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC--- 400000000 records 10000000 | tail
. /etc/profile.d/lean.sh && holdouts/1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---/lean/check.sh
```

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 24 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..9; n = 10 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: A with 0 under the head, 1 right, 1 two right.

## Pages

- [`pages/holdouts/1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---/explainer.html`](../../pages/holdouts/1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---/explainer.html)
- [`pages/holdouts/1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---/proof-status.html`](../../pages/holdouts/1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---/proof-status.html)
