# 1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---

bbchallenge id 124880. One of the six-state holdouts whose halting from blank tape is open. Family: **word counter on 1100 / 10 (right end)**, with the sibling [`1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---`](../1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---/README.md) (C and D swapped, two transitions differ).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1LC | 1RE |
| C | 1LD | 0LC |
| D | 0LE | 0LC |
| E | 0RA | 0RF |
| F | 1RA | --- |

## What it does

The tape grows mostly to the right, logarithmically: each new cell costs a roughly constant factor more time.

| rightmost cell | first reached at step |
|---|---|
| 50 | 1,791 |
| 100 | 37,189 |
| 150 | 436,687 |
| 200 | 24,850,931 |
| 250 | 1,127,467,227 |
| 300 | 15,161,635,357 |

304 cells after 18,989,462,033 steps (`tools/c/tmrun.c records`). Read in the words `a = 1100`, `b = 10` (`tools/c/tokrun.c`), the
tape is a word over a, b and single 1s (e.g. `a^6 b^14 a 1 b^2 a^3 1 b^4 a^5 b^2 ...`) followed by a regular tail
`(1 b^2)^n`; the front changes at every pass, the tail grows by a unit now and then.

**Halting.** F on 1 is the only halt and F is entered only from E on 1: the machine halts exactly at `E>1 1`. Not seen.

**Open:** everything beyond this first look: the pass rule on the word.

## Status

Open.

- Lean (`lean/Blank.lean`): `step_none_iff`, no halt in 10,000 steps by the kernel, in 10,000,000 by `native_decide`.
- Lean, kernel (`lean/Sweeps.lean`): the sweep rules of the self-loops.
- C: no halt in 2·10^10 steps.

## Next steps

Find the pass rule of the word in the tokens a, b (`tokrun ... a=1100,b=10`), compare with the sibling, then accelerate.

## Pages

- [`pages/holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/explainer.html`](../../pages/holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/explainer.html)
- [`pages/holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/proof-status.html`](../../pages/holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/lean/check.sh
./tmrun 1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA--- 20000000000 records 1500
```
