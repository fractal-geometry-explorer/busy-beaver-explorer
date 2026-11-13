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

## Pages

- [`pages/holdouts/1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC/explainer.html`](../../pages/holdouts/1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC/explainer.html)
- [`pages/holdouts/1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC/proof-status.html`](../../pages/holdouts/1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC/proof-status.html)
