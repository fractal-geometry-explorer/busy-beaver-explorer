# 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA

bbchallenge id 11019. Open. A **two-block transfer with a tail counter**: two long blocks `(01)^a` and `(10)^b`; at each visit of the
left end a drops by about 1.5 and b grows by about 3.2, paced by a small counter of short blocks at the right end;
when a is used up the right block becomes the new left block, so each round is about 2.2 times longer.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1RC | 0LF |
| C | 1LA | 0LB |
| D | --- | 1RE |
| E | 1LB | 1RA |
| F | 0LC | 0RA |

## The tape as words

At the left end (state A): `0 1 0 (01)^a 0 0 0 0 (10)^b` + tail, the tail being short blocks `(10)^k` separated by
`000`; e.g. step 9,932,715,748:
`0 1 0 (01)^2110 0000 (10)^56419 000 (10)^4 000 (10)^13 000 (10)^16 000 (10)^20 111 0 1`.
The tail changes at every visit and keeps returning to the same patterns, like the low digits of a counter.

## Rounds

Per visit a falls by 1 or 2 and b grows by about 3.2, depending on the tail; over the round from step 2.45e9 to
9.93e9 a went 27,610 -> 2,110 and b 1,942 -> 56,419. When a is used up the right block becomes the new left block (in
state C the tape reads `000 (10)^a 000 (10)^b ...`) and the transfer restarts. New left blocks: 851 (3.2e6),
2,392 (1.9e7), 5,837 (1.0e8), 12,514 (5.0e8), 28,096 (2.3e9); ratio about 2.2.

## Sweeps (Lean, kernel, `lean/Rules.lean`)

| rule | statement | steps |
|---|---|---|
| `f_left` | `L (01)^n F>0 R` -> `L F>0 (01)^n R` | 8n |
| `b_right` | `L 1 B>(101100)^n R` -> `L (010110)^n 1 B> R` | 42n |
| `e_right` | `L E>(101100)^n R` -> `L (100101)^n E> R` | 12n |

## Halting

The only halting transition is D on a 0; D is entered only from A on a 1 (A writes 0, moves right).

## Status

Open. Kernel: halting configurations, 10,000 steps, the three shift rules. Native: 10^7 steps. Trusted: no halt in
10^10 steps (`c/ev.c`). The transfer rates and the tail counter are from simulation only.

## For later

* Find the tail counter's rules (which patterns, in which order) and the exact cells moved per visit; then the
  round map a -> b is a sum over the counter's states.

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.498; right: sqrt,
exponent 0.478). After 1,000,000,000 steps: 38,989 cells visited (7,943 left of the
start, 18,839 right), 19,487 ones.

- left, step 972,062,110: `C>0 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- left, step 987,988,562: `C>0 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 978,051,188: `0 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^`
- right, step 993,829,597: `0 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0^`

## Pages

- [`pages/holdouts/1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA/explainer.html`](../../pages/holdouts/1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA/explainer.html)
- [`pages/holdouts/1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA/proof-status.html`](../../pages/holdouts/1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA/lean/check.sh
gcc -O2 -o ev holdouts/1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA/c/ev.c && ./ev 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA 2000000000 L A 1 100000 12 | awk 'NR%300==0'
```
