# 1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---

bbchallenge id 65944. One of the six-state holdouts. Analyzed by hand (group G02), partly.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LA | 0RD |
| C | 0LB | 1LF |
| D | 1RE | 1LC |
| E | 1LC | 0RB |
| F | 0LA | --- |

## What it does

Sample: B at the left end, `K(pre, N, S) = 0^inf B> 0 0 pre 1^N S 0^inf`, pre in {empty, `10`}, S a short word.
Each round trip turns 4 ones into two words `110` (`B>0 0 a^8705 1^18465` -> `a^8707 1^18461` at 10^9 steps);
when the ones are used up the run of `110` is rebuilt into a block of ones about 3/2 as long. Samples of the run:
N = 175, 263, 395, 584, 923, 1388, 2090, 3140, 4717, 7074, 10624, 15940, 23914, 35873, 53811 (to 1.7·10^9 steps).

Measured map (`py/kmap.py`, N = 20..31), pre empty and S empty:

    N = 4j   -> (empty, 3N/2 + 4, empty)       N = 4j+1 -> (10, (3N+1)/2, 011)
    N = 4j+2 -> (10,    3N/2 + 2, empty)       N = 4j+3 -> (empty, (3N+5)/2, 011)

With pre = `10` the offsets are 3N/2 + 7, 3N/2 + 5, (3N+7)/2, (3N+11)/2. So: a **Collatz-like 3n/2 map** with a
one-bit prefix, and odd N feed a counter-like word S at the right end.

## Lean

`lean/Rules.lean` (from `py/rules.py`): fourteen shift rules over 3-cell words.

## Halting

Only F1 halts. Open; n-gram CPS (widths 3..7) fails; no halt in 10^9 steps (C). `bbtools.cycles` (K = 1..3) makes
little progress within 40 s.

## Notes for later

* Prove the round-trip rule (`1^(N+4)` -> two more `110`) and the rebuild with `bbtools.symtm`, then the map for the
  other S words; work out the S counter and where F1 can fire.
* Compare with the sister machine `1RB1LC_1LA0RD_1LB1LF_1LE1RE_0LA0RB_0LB---` (shared rows A, B, D; a 4n/3 map).

## Pages

- [`pages/holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/explainer.html`](../../pages/holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/explainer.html)
- [`pages/holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/proof-status.html`](../../pages/holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---/lean/check.sh
```
