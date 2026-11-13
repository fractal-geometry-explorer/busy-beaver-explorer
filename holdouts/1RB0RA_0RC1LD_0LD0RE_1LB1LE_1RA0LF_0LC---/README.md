# 1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---

bbchallenge id 110703. A list of runs of the four-cell words 0100 and 0111 whose lengths are nearly all 1 mod 3 (near the left) or multiples of 3 (further right), with a periodic stretch (10, 4, 13, 10, 4, 13, …) between; the lengths further out look irregular.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 0RC | 1LD |
| C | 0LD | 0RE |
| D | 1LB | 1LE |
| E | 1RA | 0LF |
| F | 0LC | --- |

## What it does

Read with `a = 0001, b = 1101, c = 0111, d = 0100`, the tape at step 199,354,683 (22,052 cells) is

    D>0 a^11 11 b^16 a  [d^10 c^4 d^13 c^10 d^4 c^13] x 12  d^16 c^7 d^22 c^28 ... c^70 d^149
    c^11 d c d^2 c d^18 c^3 d c^15 d^3 c d^66 c^3 d c^36 d^3 c d^51 c^3 d c^21 ...

Middle run lengths are 1 mod 3; further right they come in groups `c^3 d c^k d^3 c d^m` with k, m multiples of
3 (heuristic). D, C and B cross runs of `0001`, `0010`, `1000` to the left (`lean/Rules.lean`, kernel).

## Status

Open. Kernel: halting configurations, no halt in 10^4 steps (10^7 native), the three crossing rules. Halting needs F
to read a 1. CTL (K = 2..5) and NGramCPS (widths 2-8, -H, -U) fail.

## For later

Check the mod-3 pattern over a long run (all samples), find the sweep rules on run lengths (symtm with lengths
3k + 1), and look for the map they define. Compare with 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF (thirds). More than a day.

## Reproduce

```sh
./tokrun 1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC--- 200000000 a=0001,b=1101,c=0111,d=0100,e=1000 L 100000 | tail -1
. /etc/profile.d/lean.sh && holdouts/1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---/explainer.html`](../../pages/holdouts/1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---/explainer.html)
- [`pages/holdouts/1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---/proof-status.html`](../../pages/holdouts/1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---`](../1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E

<!-- end of related machines -->
