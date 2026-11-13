# 1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC

bbchallenge id 50923. A BB(6) holdout whose halting from blank tape is open. Family: **three-wheel odometer (doubling counter with carries)**. Decision: **open** (heuristically about 10^-7 chance of halting).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 0LC | 0RE |
| C | 1LF | 1LD |
| D | 1LA | 0LA |
| E | 1LC | 1RB |
| F | --- | 1LC |

## What it does

At every right-end visit in state B the tape is

    S(c, a, b) = 0^∞ (10)^c 1^a 0 (10)^b 1 B>0 0^∞        (a even, a ≥ 2)

and the next one is (`py/model.py`):

    2b < a           -> (c, a − 2b, 2b + 1)                         fast wheel: (10)^b doubles, eating 1s
    2b ≥ a, c ≥ 1    -> rule at (c − 1, 2a + 4, max(b − a/2 − 1, 0))  carry: a 10 of the left block becomes 1s
    2b ≥ a, c = 0    -> halt if b = a/2, else rule at (a, 4, b − a/2 − 1)   reset: the pool becomes the left block

The run reaches S(0, 4, 1) at step 43.

## Status

* Trusted: the rule against direct simulation for c < 6, even 2 ≤ a < 30, b < 34 (2,856 configurations) and on every
  visit in the first 3·10^6 steps (`py/model.py check`).
* Trusted: 10^8 macro steps, 38 resets, no halt; the 38th reset makes a left block of 44,140,926
  (`py/model.py resets 1e8`).
* Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* Heuristic: a reset comes from a doubling step (a′, b′) with 2b′ < a′ ≤ 6b′ + 2, so b′ takes ~a′/3 values and one
  of them halts; summed over future resets the chance is ~10^-7.
* Open: whether a reset ever hits b = a/2.

## Next steps

Lean proofs of the three rules (the doubling sweep, the carry and the reset are symtm shift rules plus induction),
giving "halts iff the odometer halts" as a kernel theorem. A faster odometer simulator (the doubling phase is
O(log a) steps; the carry phase can be jumped arithmetically) would push the reset count far beyond 38.

## Pages

- [`pages/holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/explainer.html`](../../pages/holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/explainer.html)
- [`pages/holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/proof-status.html`](../../pages/holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/lean/check.sh
python3 holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/py/model.py check
python3 holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/py/model.py resets 1e8
```
