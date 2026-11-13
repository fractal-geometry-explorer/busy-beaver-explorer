# 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---

bbchallenge id 71372. A hierarchy of frozen segments (10)^a 11 (01)^b whose sizes grow level by level (43, 403, 893, …); the active end eats the last run of pairs 01 at a steady rate, 400 pairs per sample, and turns it into a growing reservoir of the word 1010101 at the far left.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 1RF |
| C | 1LD | 0LE |
| D | 1RE | 0RA |
| E | 1LC | 0RD |
| F | 0RE | --- |

## What it does

The tape at step 987,150,465 (66,000 cells):

    C> (01)^4 (1010101)^6123 (01)^7 [(10)^11 11 (01)^43] x9 (10)^11 11 (01)^86
       [(10)^83 11 (01)^403] x6 (10)^83 11 (01)^187 (10)^162 11 (01)^893 (10)^565 11 (01)^893
       (10)^565 11 (01)^1162 (10)^6 11 (01)^3523

The middle is frozen: identical at steps 8.39e8, 9.11e8, 9.87e8. Only the reservoir r (5323, 5723, 6123) and the
last run m (4323, 3923, 3523) change, by 400 per sample, and the tape grows 2000 cells to the left (heuristic).
Segment sizes grow by level (43, 403, ~900): nested levels, each presumably built when a drain runs out. The head
crosses runs of pairs in one go (`lean/Rules.lean`, four rules, kernel).

## Status

Open. Kernel: halting configurations, no halt in 10^4 steps (10^7 native), the four crossing rules. Halting needs F
to read a 1. CTL (K = 2..5) and NGramCPS (widths 2-8, -H, -U) fail.

## For later

1. Prove the drain step (400 pairs per sample, or one pair per sweep) as a rule with r and m as variables.
2. Run to the end of the current drain (about 1.5e9 steps more) and record how a new level is made; earlier levels
   can be studied at small sizes (the run passes through them in the first 10^7 steps).
3. If the level-building map is regular, this machine may be provable. Promising.

## Reproduce

```sh
./tmrun 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE--- 1000000000 records 100000000 | awk 'NR%2000==0' | tail -3
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/explainer.html`](../../pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/explainer.html)
- [`pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/proof-status.html`](../../pages/holdouts/1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/proof-status.html)
