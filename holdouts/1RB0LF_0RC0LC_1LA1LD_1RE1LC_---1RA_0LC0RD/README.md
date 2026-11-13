# 1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD

bbchallenge id 66058. The tape is the seven-cell word 0101111 repeated, cut into long runs in different phases by short defects; the sweeps carry runs across in one go and slowly move and lengthen them, and the run lengths look irregular.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 0RC | 0LC |
| C | 1LA | 1LD |
| D | 1RE | 1LC |
| E | --- | 1RA |
| F | 0LC | 0RD |

## What it does

The tape is the seven-cell word `0101111` in its phases, long runs separated by short defects. At step 999,903,180:

    (11110)^2 (1011110)^302 1^5 (0101111)^191 (0111101)^1341 (1010111)^1001 10 1^5 (0101111)^731
    (01011)^2 (1101011)^753 11 (01)^4 (1110101)^3767 1^7 (0101111)^1382 01 01 11 0 C>0

B and C cross whole runs (`lean/Rules.lean`, kernel): `1 0 1 1 1 B> (0111110)^n -> 1 0 1 1 1 (1010111)^n B>` and
the same for C on `1111100`. Leftward, a zigzag of D, C, A, E converts a run two copies at a time. The run lengths
look irregular. The right side is the bouncer side (sqrt).

## Status

Open. Kernel: halting configurations, no halt in 10^4 steps (10^7 native), the two crossing rules. Halting needs E
to read a 0. CTL (K = 2..5) and NGramCPS (widths 2-8, -H, -U) fail.

## For later

Tokenize by the period-7 word with a phase per run; list the defects and how each passes a sweep (symtm); then try
a CTL over that alphabet. Same plan as for 1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC--- (period 24). More than a day.

## Reproduce

```sh
./tmrun 1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD 1000000000 records 100000000 | tail -2
. /etc/profile.d/lean.sh && holdouts/1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD/explainer.html`](../../pages/holdouts/1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD/explainer.html)
- [`pages/holdouts/1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD/proof-status.html`](../../pages/holdouts/1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD/proof-status.html)
