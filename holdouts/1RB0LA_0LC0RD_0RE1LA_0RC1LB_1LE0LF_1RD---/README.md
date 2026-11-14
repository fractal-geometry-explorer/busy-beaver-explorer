# 1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---

bbchallenge id 110152. The tape is a list of pairs of (10)-blocks (big, small); between left-end visits every pair moves the same amount from its big block to its small one, so one kind of separator drifts while the other stays, and their collisions reshape the list.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 0LC | 0RD |
| C | 0RE | 1LA |
| D | 0RC | 1LB |
| E | 1LE | 0LF |
| F | 1RD | --- |

## What it does

The left side grows like √t (a bouncer), the right side like t^0.24. Whenever the visited part grows on the left,
the tape is a **list of blocks** `(10)^n` separated by single 0s (read with the word a = `10`):

    step 140,133,553:  A>0 0^3 a^442 0 a^61 0 a^407 0 a^61 0 a^407 0 a^64 0 a^381 0 a^62 0 a^340 0 a^56 …
    step 140,405,051:  A>0 0^3 a^436 0 a^67 0 a^401 0 a^67 0 a^401 0 a^70 0 a^375 0 a^68 0 a^334 0 a^62 …

The blocks come in **pairs** (big x, small y). From one sample to the next, every pair gave the same amount δ = 6
from its big block to its small one: x + y stays (503, 468, 471, 443, …), so the 0 inside each pair moved left by
6 blocks of `10` while the 0s between pairs stayed. Far into the run the pairs are larger (step 2.5·10¹⁰:
1977 199 1923 202 1857 200 …) and the big blocks decrease along the list while the small ones stay near 200.

δ changes from one left visit to the next (2, 4, 6, 12, …); now and then a pair's small or big block runs out,
or a new pair starts at the left end, and the list is rebuilt there. So the machine is a **particle system**: two
kinds of separators in a `(10)` background, one kind drifting and the other fixed, interacting when they meet.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the shift rules by which the sweeps cross the `(10)^n` and `(01)^n` blocks (C rightward, A and C leftward) (`shift_r_C_10`, `shift_l_A_10`, `shift_l_A_01`, `shift_l_C_01`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The drift of the separators is measured; the collisions, which reshape the list, are not
understood. Halting needs F reading 1, entered only from E reading 1 with a 1 to its left (E1 → 0LF).

## For later

More than a day. Next: (1) write the configuration at left extensions as the list (x1, y1, x2, y2, …) plus the
irregular end, and prove the sweep rule that moves every separator by δ (with `symtm.prove` and the shift rules in
`lean/Rules.lean`); (2) find what sets δ (the number of sweeps between two left extensions?); (3) collect the
collisions (a pair whose small block reaches 0) and classify their outcomes.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---/lean/check.sh
python3 holdouts/1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 2.60x10^9 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 4 checkpoints, the last at 1.00x10^9 steps. No trip-level jump was used in this run, only the shift rules over repeated words (exact by induction, but the program is not verified).

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD--- 400
```

## Pages

- [`pages/holdouts/1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---/explainer.html`](../../pages/holdouts/1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---/explainer.html)
- [`pages/holdouts/1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---/proof-status.html`](../../pages/holdouts/1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---/proof-status.html)
