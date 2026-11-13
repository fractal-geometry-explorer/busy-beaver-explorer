# 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF

bbchallenge id 75625. A binary word written in 4-cell letters 1110 and 1111; every leftward sweep replaces it by its running parity (XOR from the right), so the space-time diagram is Pascal's triangle mod 2 (Sierpinski triangles), in epochs that each grow the tape by about 1.75.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 0RC | --- |
| C | 1LD | 1LE |
| D | 1LE | 1LD |
| E | 1RF | 0LC |
| F | 1RA | 1RF |

## What it does

Letters `u = 1110`, `v = 1111`. Between sweeps the tape is a word in `u` and `v` (blocks `1^(4k+3) 0`) plus a short
fixed end on the right. Step 2,003,981:

    u^3 v u v^2 u v u v u^3 v^2 u v u v u v^2 u^2 v^3 u v^2 u v^3 u v u^3 ...   (about 650 letters)

**Leftward sweep = running parity** (proved, `lean/Rules.lean`). The head is in D (even) or C (odd) on the last cell
of a word `111x`:

| state | letter | writes | next |
|---|---|---|---|
| D | u = 1110 | 0101 | C |
| D | v = 1111 | 1111 | D |
| C | u | 1111 | D |
| C | v | 0101 | C |

so behind the head is the running XOR from the right (u = 1), written as 1111 (even) / 0101 (odd). Iterating the
running XOR gives Pascal's triangle mod 2: the Sierpinski triangles of the space-time diagram.

**Epochs** (observed, `c/epochs.c`). The head bounces between the left end and an inner wall that moves left; the
zone between them is rewritten every bounce, the tape right of the wall is frozen; when the zone closes, a full
crossing starts a new epoch.

| step | left end | right end |
|---:|---:|---:|
| 47,799 | 374 | 47 |
| 145,962 | 703 | 58 |
| 487,979 | 1,319 | 69 |
| 1,427,948 | 2,265 | 80 |
| 4,277,179 | 4,020 | 91 |
| 13,419,889 | 7,237 | 98 |
| 40,483,837 | 12,641 | 109 |
| 124,076,294 | 22,085 | 112 |
| 383,276,545 | 38,918 | 115 |
| 1,162,585,978 | 68,091 | 130 |

## Twin

`1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF` has identical configurations at 12 of the 13 epoch starts up to
1.7·10^9 steps (about 1.5 times later); see its folder.

## Halting

Only B1 halts; B is entered only from A0 and A only from F1: halts iff `F> 1 0 1`. F crosses `1111` (proved). Not
decoded: the rightward sweep over `0101` words and the turns at the walls, where the question lies.

- CTL K = 3..6: halts remain. n-gram CPS 3..7: fails. No invariant a·ones + b·pos + W mod 2..12.
- No halt in 3·10^9 steps.

## Notes for later

- Decode the rightward sweep into letter rules (the alignment shifts by one cell; `0101` vs `1010` phase) and the
  two turns; then the whole round is a map on binary words and the wall's motion can be stated.

## Pages

- [`pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/explainer.html`](../../pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/explainer.html)
- [`pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/proof-status.html`](../../pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/lean/check.sh
```
