# 1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD

bbchallenge id 125786. A bouncer whose right part is the word 1101 repeated, one more copy every sweep; it turns around at the left end on a short control word of blocks 110 and 100110 that keeps changing irregularly and grows very slowly; a block of 150 copies of 1101 stays frozen in between.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1RC | 1RF |
| C | 1LD | 0LC |
| D | 1RA | 1LE |
| E | 1RA | 0LC |
| F | --- | 0RD |

## What it does

Three parts (D at the right end):

    95,631,033    [70-cell control word] (1101)^150 (1011)^5 (0111)^1640 0 D>0
    153,514,749   [84-cell control word] (1101)^150 00 (1110)^3 (1101)^2541 11 0 D>0

- Right part: the word `1101` (in its rotations), one more copy per sweep (+300 copies between samples 300 sweeps
  apart). A, F and B cross it whole (`lean/Rules.lean`, kernel): `A> (0111)^n -> (1110)^n A>`,
  `F> (1101)^n -> (1011)^n F>`, `B> (1110)^n -> (1101)^n B>`.
- A frozen block of 150 copies of `1101`, laid down early.
- A control word at the left end, built of `110`, `100110`, `1 00`, `101`. It is rewritten at every turn, wanders
  between 47 and 115 cells in the first 5.5e8 steps, and grows very slowly.

Over the first 2e9 steps the control word takes 19,905 distinct values in 19,908 sweeps, none longer than 111
cells (trusted count).

## Status

Open. Kernel: halting configurations, no halt in 10^4 steps (10^7 native), the three crossing rules. Halting needs F
to read a 0 (F is entered from B1, at the control word). CTL (K = 2..5) and NGramCPS (widths 2-8, -H, -U) fail.

## For later

The control word is the whole question. Next: record its sequence at each turn (it is short, so a dictionary of the
words seen, and their successors, is cheap), look for a counter structure (blocks 110 vs 100110 look like digits),
and try a CTL restricted to the left part with the right part abstracted as `(1101)^*`. Possibly tractable.

## Reproduce

```sh
./tmrun 1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD 600000000 at D R 100000000 | awk 'NR%300==0'
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD/explainer.html`](../../pages/holdouts/1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD/explainer.html)
- [`pages/holdouts/1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD/proof-status.html`](../../pages/holdouts/1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD/proof-status.html)
