# 1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC

bbchallenge id 149506. One of the six-state holdouts. Analyzed by hand (group G02), partly: shift rules proved, cascade only observed.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LB |
| B | 1LC | 0RE |
| C | 0LE | 0LD |
| D | 0LC | --- |
| E | 1LA | 0RF |
| F | 1RE | 1LC |

## What it does (observed)

With x = `1110`, at step 2,048,043,645 the tape is

    A>0 1 0 x^5326 1 0 11 0 x^579 00 x^3766 1 0 11 0 x^1939 1 0 11 0 x^78 00 x^5 111   (+ ~60 cells right of start)

At each later visit of the left end the segment before the `00` marker loses ~26 words and the one after gains as
many (579 -> 9 and 3766 -> 4336 by step 2,075,216,540); the first segment gains ~3.5. Then the marker restarts
(`x^5405 00 x^5 1 0 11 0 x^4345 ...`) and the marker of the last segment moves by 8 (`x^78 00 x^5` ->
`x^70 00 x^13`). The right side gains one cell per record, records about 1.5 times apart (3.0e8, 4.9e8, 7.6e8,
1.11e9, 1.61e9, 2.41e9).

## Lean

`lean/Rules.lean` (from `py/rules.py`): twelve shift rules over 2- and 4-cell words, found by a symbolic search,
each for every n and every tape around.

## Halting

Only D1 halts. Open. n-gram CPS (widths 3..7) fails; no halt in 10^9 steps (C).

## Notes for later

* Take the visit of the left end as the sample, prove the per-visit rule (b - 26, c + 26, a + 3.5 on average: the
  exact rule depends on parities) with `bbtools.symtm`, then the rule for the marker's rebirth; this gives a
  multi-digit counter whose overflow should decide D1.

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 256,060,160 | 16,252 | 7 | 9 | 16 | 0.48 |
| right | 300,981,518 | 19,408 | 4 | 4 | 8 | 0.58 |
| left | 1,024,035,610 | 31,804 | 11 | 10 | 18 | 0.33 |
| right | 1,112,489,184 | 35,733 | 4 | 5 | 9 | 0.49 |
| left | 4,096,189,910 | 73,208 | 11 | 10 | 18 | 0.65 |
| right | 6,272,872,020 | 95,117 | 9 | 4 | 13 | 0.73 |
| left | 16,384,326,928 | 136,162 | 9 | 11 | 20 | 0.38 |
| right | 18,119,743,260 | 149,702 | 8 | 6 | 14 | 0.68 |

**Proposed family: F01, periodic blocks driven by a bounded engine** (the table of 1RB0LC_0RC0RF… mirrored, from another start: a few long blocks and a short rest).

8 to 20 level-2 tokens at every record from 2.6·10^8 to 1.8·10^10 steps. In the macro simulator (blocks of 4 cells) the tape has 6 to 26 runs at the sampled right-end records up to 1.5·10^19 steps. For example at step 18,119,743,260 the tape is `1 (1000)^5621 101 (0010)^25428 1 (0010)^4347 (0001)^1938 0^6 (1000)^88 100`: four long blocks, one of 88 copies and five short pieces.

The table is that of 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB--- read in a mirror with the states renamed (`related.json`), started in another state. The two runs are different (the block lengths have nothing in common on this screen), so nothing is claimed about one from the other; what carries over is the table, and with it any sweep rule proved for all lengths.

A few periodic blocks trading copies, with a bounded rest: the F01 shape.

Next step: Sample at the right-end records (state F), where the tape has 4 to 6 tokens, and find the map between consecutive ones; then the F01 closure test.

## Pages

- [`pages/holdouts/1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/explainer.html`](../../pages/holdouts/1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/explainer.html)
- [`pages/holdouts/1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/proof-status.html`](../../pages/holdouts/1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LB_1LC0RE_0LE0LD_0LC---_1LA0RF_1RE1LC/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---`](../1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/README.md): rename A→D, B→A, C→B, D→F, E→C, F→E and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
