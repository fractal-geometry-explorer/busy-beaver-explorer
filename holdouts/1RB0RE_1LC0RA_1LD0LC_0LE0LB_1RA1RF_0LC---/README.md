# 1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC---

bbchallenge id 45361. A bouncer over 3-cell words c = 100 and d = 101: the sweeps on the growing left part trade c for d and back, next to a small irregular wall and a frozen tail of 110100 words on the right.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1LC | 0RA |
| C | 1LD | 0LC |
| D | 0LE | 0LB |
| E | 1RA | 1RF |
| F | 0LC | --- |

## What it does

Words `c = 100`, `d = 101`. Step 2·10^9:

    0 c^11883 d [A0] 1 d^5646 00 1 d 00 c^3 1 d 00 c 1 d^2 00 1 d 00 1 d 00 1 d^2 00 c 1 d ... (1 d 00)^n

A left part of `c`- and `d`-runs (grows like sqrt(time)), an irregular wall, and a long tail `(110100)^n` that is
frozen (the slowly growing side). The sweeps move the boundary between the c-run and the d-run:

| step | c | d |
|---:|---:|---:|
| 10^8 | 3,815 | 83 |
| 4·10^8 | 4,022 | 3,805 |
| 10^9 | 3,955 | 8,435 |
| 2·10^9 | 11,883 | 5,646 |

**Proved** (`lean/Rules.lean`): fourteen shift rules; in particular going left C turns `(100)^n` into `(101)^n` and
D leaves it, A and E cross word pairs going right, B crosses the tail word.

## Halting

Only F1 halts; F is entered only from E1 (1RF): halts iff `E> 1 1`. CTL K = 3..6: halts remain; n-gram CPS 3..7
fails; no invariant mod 2..12; no halt in 10^9 steps.

## Notes for later

- Sample at the wall (head entering it from the left) and derive how the wall's words change per sweep; then the
  c/d boundary motion as a function of the wall.

## Pages

- [`pages/holdouts/1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC---/explainer.html`](../../pages/holdouts/1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC---/explainer.html)
- [`pages/holdouts/1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC---/proof-status.html`](../../pages/holdouts/1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1LC0RA_1LD0LC_0LE0LB_1RA1RF_0LC---/lean/check.sh
```
