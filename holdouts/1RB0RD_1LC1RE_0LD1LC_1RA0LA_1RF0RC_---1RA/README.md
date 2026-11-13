# 1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA

bbchallenge id 25604. One of the six-state holdouts whose halting from blank tape is open. Family: **counter of 1^4 blocks (left end)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1LC | 1RE |
| C | 0LD | 1LC |
| D | 1RA | 0LA |
| E | 1RF | 0RC |
| F | --- | 1RA |

## What it does

At every visit of the left end in state C (on a 0, then `1^4`) the tape starts with a row of n blocks `1^4 0`. Along a
stretch n grows by 1 per visit and the gap between visits tends to double (ratios 1.08, 1.15, 1.26, 1.42, ..., 1.96);
now and then n drops by 2–4 while the word of longer blocks behind the row (1^3, 1^7, 1^11, 1^23, ...) is rebuilt.
n = 27 at step 15,886,922,696 (`tools/c/tmrun.c`, `at C L`, 2·10^10 steps).

**Halting.** F on 0 is the only halt; F is entered only from E on 0, E only from B on 1: the machine halts exactly at
`B>1 0 0`. Not seen.

**Open:** the rule by which a visit rewrites the word, and whether `B>1 0 0` can occur.

## Status

Open.

- Lean, kernel (`lean/Sweeps.lean`, written by `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/sweeps.py`): the sweep rules of the self-loops.
- Lean (`lean/Blank.lean`): `step_none_iff`, no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`.
- C: no halt in 2·10^10 steps.

## Next steps

Find the recursion inside one visit (as in `1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA/py/hybrid.py`) and the word rule.

## Pages

- [`pages/holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/explainer.html`](../../pages/holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/explainer.html)
- [`pages/holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/proof-status.html`](../../pages/holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/lean/check.sh
./tmrun 1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA 20000000000 at C L 1500
```
