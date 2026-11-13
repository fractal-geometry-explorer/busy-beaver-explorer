# 1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC

bbchallenge id 18046. Domains of the pairs 01 and 10 separated by about a dozen domain walls (00 or 11); sweeps flip the phase of every domain and move the walls, so the domains grow while the number of walls stays near 13; the domain lengths look irregular.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 0RC | 1RE |
| C | 1RD | 1LE |
| D | 0LE | --- |
| E | 1RA | 1LF |
| F | 1RF | 0LC |

## What it does

The tape is `0101...` broken by about a dozen walls (`00` or `11`). Step 83,090,812, F at the left end:

    F>0 11 (01)^2426 (10)^1439 (01)^206 00 (10)^1894 (01)^50 00 (10)^1330 (01)^266 (10)^543 (01)^474 (10)^606 11 (01)^308 000

E and A flip whole domains (`lean/Rules.lean`, kernel): `E> (01)^n -> (10)^n E>`, `A> (10)^n -> (01)^n A>`. The
walls move a little each sweep. Their number stays at 12 to 14 (every 300th sample, steps 2.45e8 to 3e8, 41k to 48k
cells) while the domains grow (heuristic). Domain lengths look irregular.

## Status

Open. Kernel: halting configurations, no halt in 10^4 steps (10^7 native), the two crossing rules. Halting needs D
to read a 1. CTL (K = 2..5) and NGramCPS (widths 2-8, -H, -U) fail.

## For later

Classify the walls (left/right sweep shapes) and their motion per sweep (symtm rules with the domain lengths as
variables); record wall births and annihilations over a long run; then try an abstraction keeping only wall types
and order. More than a day.

## Reproduce

```sh
./tmrun 1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC 300000000 at F L 1000000 | awk 'NR%300==0'
. /etc/profile.d/lean.sh && holdouts/1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC/explainer.html`](../../pages/holdouts/1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC/explainer.html)
- [`pages/holdouts/1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC/proof-status.html`](../../pages/holdouts/1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC/proof-status.html)
