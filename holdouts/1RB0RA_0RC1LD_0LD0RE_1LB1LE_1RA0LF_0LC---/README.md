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

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 256,224,779 | 24,549 | 704 | 876 | 555 | 0.04 |
| right | 257,032,468 | 24,578 | 1,067 | 753 | 790 | 0.04 |
| left | 1,024,451,627 | 46,629 | 1,932 | 2,333 | 588 | 0.02 |
| right | 1,025,987,316 | 46,658 | 2,852 | 1,972 | 837 | 0.02 |
| left | 4,096,203,795 | 91,948 | 4,489 | 5,352 | 564 | 0.01 |
| right | 4,098,133,485 | 91,972 | 6,611 | 4,495 | 837 | 0.01 |
| left | 16,385,027,297 | 183,249 | 9,654 | 11,441 | 588 | 0.01 |
| right | 16,391,067,486 | 183,278 | 14,138 | 9,595 | 837 | 0.01 |

**Proposed family: F06, block-list counters** (a periodic block of long period, a frozen list of growing runs and a list of counters at the right).

With repeats of single words only, the number of pieces is proportional to the tape (21,095 level-1 tokens for 183,249 cells at 1.6·10^10 steps). Most of them are one block of long period: `[(0111)^10 (0100)^4 (0111)^13 (0100)^10 (0111)^4 (0100)^13]^N` with N = 264 at the right-end record at 4.1·10^9 steps and N = 595 at 1.6·10^10 (a period of 216 cells). With such groups counted once, the description is constant: 588, 564 and 588 level-2 tokens at the left-end records at 10^9, 4.1·10^9 and 1.6·10^10 steps, and 837 at each of the three right-end records.

Right of the block the tape is a frozen list of runs of growing lengths (16, 7, 22, 28, 22, 22, 16, 25, … up to 149) and then a list of units `(1110)^a (1000)^3 111 (0100)^b (0111)^3 01 000` with (a, b) = (18, 15), (66, 36), (51, 21), (57, 9), … at the left-end record at 1.6·10^10 steps; the right-end record at 4.1·10^9 steps shows the same units with b one smaller. The table is that of 1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD--- with the states renamed (`related.json`), from another start. The two runs are different and nothing is claimed about one from the other.

A list of units that changes slowly while a periodic block grows behind it is read here as a list of counters: F06. The round rule is not known. Because the description outside the block is constant over a factor of 16 in steps, it is also worth one try of the F01 closure with the 216-cell word as the block.

Next step: The rule of one unit `(a, b)` of the right-hand list, and what turns a unit into a piece of the frozen list.

## Pages

- [`pages/holdouts/1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---/explainer.html`](../../pages/holdouts/1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---/explainer.html)
- [`pages/holdouts/1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---/proof-status.html`](../../pages/holdouts/1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---`](../1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E

<!-- end of related machines -->
