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

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---`](../1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---/README.md): rename A→D, B→E, C→B, D→C, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---`](../1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---`](../1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---/README.md): rename A→D, B→E, C→C, D→A, E→B, F→F; it is this table started in state D
- [`1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB`](../1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB/README.md): rename A→B, B→A, C→E, D→F, E→D, F→C and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
