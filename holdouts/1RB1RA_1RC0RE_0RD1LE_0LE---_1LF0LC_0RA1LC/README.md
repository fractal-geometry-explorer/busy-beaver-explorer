# 1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC

bbchallenge id 23160. The left side is the six-cell word 010111 repeated, cut into runs whose lengths are almost always 2^k − 1 and that merge in pairs (127 + 1 + 127 = 255), a binary-carry-like structure, swept by a bouncer.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1RC | 0RE |
| C | 0RD | 1LE |
| D | 0LE | --- |
| E | 1LF | 0LC |
| F | 0RA | 1LC |

## What it does

The tape is built from the six-cell word `010111` in its rotations (`p = 010111, q = 101011, r = 110101,
s = 111010`). Moving right, A crosses runs of any length and B crosses `101110` (`lean/Rules.lean`, kernel):
`A> (010111)^n -> (101111)^n A>` and three more rotations, `B> (101110)^n -> (011111)^n B>`.

At the left end the tape is a far-left reservoir `q^n r^m`, then runs `s^n` separated by single 1s and grouped by
`1^3 0`, e.g. (step 37,591,608)

    F>0 q^462 1 0 s^13 1 s^126 1 s^127 1 s^127 1 s^127 1 s^127 1 s^95 1 s^17 1^3 0 s^6 1 s^15 1 s^15 ...

Interior run lengths are 2^k - 1 in 259,121 of 260,035 samples (heuristic). Equal runs merge like binary carries
(127 + 1 + 127 = 255). The left side grows like sqrt(steps), the right side like a smaller power (fitted exponent 0.31).

## Status

Open. Kernel: halting configurations, no halt in 10^4 steps (10^7 native), the five crossing rules. Halting needs D
to read a 1 (D is entered from C0 at a run boundary). CTL (K = 2..5) and NGramCPS (widths 2-8, -H, -U) fail.

## For later

1. Prove the turn-around moves at run boundaries (`1`, `1^3 0`, the reservoir) as symtm rules.
2. Derive the map on run lists per sweep and check it against `tokrun`.
3. Look for an invariant (run lengths 2^k - 1 except near the reservoir) that excludes the halting boundary.
More than a day.

## Reproduce

```sh
./tokrun 1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC 2000000000 p=010111,q=101011,r=110101,s=111010 L 100000 | tail
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC/lean/check.sh
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
| left | 256,008,103 | 20,924 | 19 | 50 | 43 | 0.48 |
| right | 263,749,973 | 21,408 | 9 | 42 | 38 | 0.40 |
| left | 1,024,028,861 | 46,040 | 5 | 185 | 42 | 0.25 |
| right | 1,025,527,289 | 46,077 | 3 | 167 | 32 | 0.25 |
| left | 4,096,021,986 | 88,682 | 11 | 181 | 46 | 0.15 |
| right | 4,098,030,776 | 88,717 | 5 | 164 | 38 | 0.15 |
| left | 16,384,228,978 | 177,835 | 4 | 175 | 48 | 0.14 |
| right | 16,385,178,127 | 177,839 | 6 | 161 | 52 | 0.14 |

**Proposed family: F06, block-list counters** (blocks of 2^k − 1 copies of period-6 words: a binary counter structure).

At the records the tape is blocks of the rotations of one six-cell word (`110101`, `111010`, `010111`, `101011`), and many of the numbers of copies are one less than a power of two (7, 15, 31, 127, 1,023, 2,047), the same count repeated for the rotations of the word. With groups counted once the description is 32 to 52 level-2 tokens at the records from 2.6·10^8 to 1.6·10^10 steps; counted singly the blocks number 161 to 185 from 10^9 steps on, and the macro simulator (blocks of 6 cells) has up to 19,127 runs by 2·10^17 steps.

Blocks with 2^k − 1 copies in a list that grows slowly are the levels of a binary counter: F06.

Next step: The carry rule that merges two blocks of 2^k − 1 into one of 2^(k+1) − 1, as an exact map on the list of block lengths.

## Pages

- [`pages/holdouts/1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC/explainer.html`](../../pages/holdouts/1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC/explainer.html)
- [`pages/holdouts/1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC/proof-status.html`](../../pages/holdouts/1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC/proof-status.html)
