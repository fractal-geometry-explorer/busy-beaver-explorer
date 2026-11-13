# 1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE

bbchallenge id 89542. A BB(6) holdout whose halting from blank tape is open. Family: **Collatz-like epochs (y ↦ ⌈3y/2⌉ countdown)**. Decision: **open** (heuristically halts with probability 2/5).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 0LC | 0LB |
| C | 1RD | 1LC |
| D | 1RD | 1RA |
| E | 1RF | 0LA |
| F | --- | 1RE |

## What it does

The run returns again and again to

    X(k, m) = 0^∞ A>0 0 (10)^k 1^m 0 0^∞

Between two of them the head makes about k/2 passes; each eats two `10` pairs at the right end of the `(10)^k`
block and pushes a run of 0s at the left out by 6 cells; at the end the 0s are rewritten as the new `(10)^k'` and
one 1 (or two) comes off the `1^m` block. The rules (k ≥ 1):

| case | next |
|---|---|
| m ≥ 4, or m = 3 and k even: k = 2j | X(3j + 3, m − 2) |
| m ≥ 4: k = 2j + 1 | X(3j + 5, m − 3) |
| m = 3, k = 2j + 1 | X(3j + 4, 1) |
| m = 2 | k even: X(2, 3k + 5); k odd: **halt** |
| m = 1 | k odd: X(2, 3k + 3); k even: **D runs right on blank tape forever** |
| m = 0 | k even: X(2, 3k); k odd: **D runs right forever** |

With `y = k + 6` the main rule is `y ↦ ⌈3y/2⌉`, the countdown `m` losing 2 (y even) or 3 (y odd). Every epoch
starts at k = 2, so k always runs through the same sequence 2, 6, 12, 21, 35, 56, 87, …; the epoch's `m` only sets
how long it lasts. The run reaches X(1, 1) after 24 steps; epochs start with m = 6, 41 (step 698), 16,169 (step
78,482,217). The third epoch lasts 6,456 macro steps and ends at m = 2 with k even (1,138 digits): a fourth epoch
starts with m = 3k + 5, a **1,139-digit number**.

## Status

* Trusted (`py/macro.py check`): the rules above against direct simulation for 1 ≤ k < 40, m < 14.
* Trusted (`py/macro.py epochs`): the epochs, exactly.
* Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* Heuristic (`py/macro.py odds`): with fair-coin parities an epoch ends with a new epoch 1/2, a halt 1/5, a run
  away 3/10; the machine halts with probability 2/5 (Racheline's estimate on the bbchallenge wiki).
* Open: the fourth epoch needs ~10^1138 macro steps; its end cannot be computed.

## Next steps

Lean proofs of the macro rules (the pass `B>0 0^z (10)^(j+2) → B>0 0^(z+6) (10)^j` is a symtm rule with z
symbolic; the rest is induction as in Antihydra's `Macro.lean`). That would make "halts iff the epoch game halts"
a kernel theorem; it would not decide the machine.

## Pages

- [`pages/holdouts/1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE/explainer.html`](../../pages/holdouts/1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE/explainer.html)
- [`pages/holdouts/1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE/proof-status.html`](../../pages/holdouts/1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE/lean/check.sh
python3 holdouts/1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE/py/macro.py check
python3 holdouts/1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE/py/macro.py epochs
```
