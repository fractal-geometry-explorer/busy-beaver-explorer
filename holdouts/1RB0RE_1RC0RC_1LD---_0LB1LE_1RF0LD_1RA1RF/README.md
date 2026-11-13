# 1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF

bbchallenge id 121862. A slower twin of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF: the same running-parity (Sierpinski) word in 4-cell letters 1110/1111, with the same epochs; at the epoch starts the two machines have identical tapes, head position and state.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1RC | 0RC |
| C | 1LD | --- |
| D | 0LB | 1LE |
| E | 1RF | 0LD |
| F | 1RA | 1RF |

## What it does

The twin of `1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF`: at 12 of the 13 epoch starts up to 1.7·10^9 steps the two
machines have **identical configurations** (tape, head position, state), this one about 1.5 times later
(`c/dump.c`):

| this machine | twin |
|---:|---:|
| 3,350 | 2,284 |
| 8,689 | 5,873 |
| 72,335 | 47,799 |
| 734,951 | 487,979 |
| 6,420,857 | 4,277,179 |
| 60,731,203 | 40,483,837 |
| 1,744,002,084 | 1,162,585,978 |

(all 12 listed in `status.json`; the epoch near 2·10^7 was sampled at different turns). So it computes the same
thing: a word in `u = 1110`, `v = 1111` replaced by its running XOR on each leftward sweep, epochs x1.75.

**Proved** (`lean/Rules.lean`): eleven shift rules over `1111`, `0101`, `1010`.

## Halting

Only C1 halts; C is entered only from B (moving right): halts iff `B> x 1`. CTL K = 3..6: halts remain; n-gram CPS
3..7 fails; no halt in 3·10^9 steps.

## Notes for later

- Prove the agreement with the twin as a simulation (a map from this machine's sweep configurations to the twin's).

## Pages

- [`pages/holdouts/1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/explainer.html`](../../pages/holdouts/1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/explainer.html)
- [`pages/holdouts/1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/proof-status.html`](../../pages/holdouts/1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/lean/check.sh
```
