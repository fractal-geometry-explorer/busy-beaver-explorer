# 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE

bbchallenge id 21883. A BB(6) holdout whose halting from blank tape is open. Family: **doubling bouncer with overflow (parity-protected)**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LF |
| B | 1RC | 1RF |
| C | 0LD | 1RE |
| D | --- | 1LC |
| E | 0RB | 1RE |
| F | 1LA | 0LE |

## What it does

At every right-end visit in state B the tape is

    T = 0^∞ [1^2 0 (10)^c] 1^a 0 (10)^b B>0 0^∞      (the bracket present or not)

* **Doubling**: if a ≥ 2b + 3 the next visit has (a − 2b − 2, 2b + 2) (`py/model.py check`: grid and run).
* **Overflow**: if a < 2b + 3 the pool runs out, the sweep rewrites the tape, and the bracket can appear, grow or
  vanish; not yet written as a formula.
* **Halting**: among these configurations only `0^∞ 1 0 (10)^b B>0` (no bracket, a = 1) halts.

Doubling keeps the parity of a; a halt needs an odd pool. In the first 10^9 steps: 1,453 visits, 48 with a odd, in 7
phases starting at a = 5, 61, 165, 165, 989, 1,853, 189 (steps 28, 10,527, 212,888, 432,061, 43,052,524,
260,493,638, 262,189,033); never a = 1. From (A, 0) doubling gives a = A − (2^(k+2) − 2k − 4) after k steps, so such
a phase halts only for A = 3, 9, 23, 53, 115, 241, 495, 1005, …

## Status

* Trusted: the doubling rule and the halting cases (`py/model.py check`).
* Trusted: the parity statistics above (`c/rec.c`: `gcc -O2 -o rec c/rec.c && ./rec MACHINE 1000000000 R B
  10000000`, each line parsed with `py/model.py`'s pattern).
* Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* Heuristic: odd phases are rare and their targets thin out; a halt is possible but not expected.
* Open: the overflow rule, and so the full macro machine.

## Next steps

Write the overflow as a formula (tabulate `sim` for a < 2b + 3, as for `1RB1RA_0LC0RE`'s odometer, which this
resembles), then the parity of a at the start of each doubling phase becomes a question about that map.

## Pages

- [`pages/holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/explainer.html`](../../pages/holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/explainer.html)
- [`pages/holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/proof-status.html`](../../pages/holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/lean/check.sh
python3 holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/py/model.py check
```
