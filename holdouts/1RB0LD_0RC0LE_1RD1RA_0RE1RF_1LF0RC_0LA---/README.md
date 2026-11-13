# 1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---

bbchallenge id 127566. One of the six-state holdouts whose halting from blank tape is open (group G13). Family: **nested counters built from two words, growing left**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | 0LE |
| C | 1RD | 1RA |
| D | 0RE | 1RF |
| E | 1LF | 0RC |
| F | 0LA | --- |

## What it does

Write a for 1 0^2 and c for 1 0 1^2 0. When the head is at the left end in state A, the tape reads, for example at step 513,296,770, A>0 0 1 0 1 0 a^465 1 0 c^86 1 0 1^2 0^2 a^21 1 0 a 1 0 c^8 1 0 1^2 0^2 a^7 1 0 a 1 0 c^63 1 0 1^2 0^2 a 1 0 a 1 0 c^1454 1^2 0 c^3018 1 0 1: runs of a and runs of c, grouped by the marker 1 0 1^2 0^2.

From one such sample to the next shown here (a few samples apart) the first run of a grows by 6 while the first run of c shrinks by 2, and the runs further right change more rarely, like the digits of a counter with several levels. The tape grows only to the left, and slowly (triage exponent 0.19): 27,455 cells at 1.86*109 steps.

### Halting

The machine halts when it reads a 1 in state F (F1 is the halting transition). F is entered from D on a 1 (D1 = 1RF) and from E on a 0 (E0 = 1LF).

## Phase 2 results

`lean/Rules.lean` proves three shift rules for every n: C over `(100)^n` (leaves `(110)^n`), A over `(001)^n`
(leaves `(101)^n`), E over `(11010)^n` (leaves `(01010)^n`). The counter map was not found.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel) and 10^7 (`native_decide`). C: no halt in 10^9 steps. Lean (`lean/Rules.lean`, kernel): the shift rules `shiftC` (C over `(100)^n` leaves `(110)^n`), `shiftA` (A over `(001)^n` leaves `(101)^n`) and `shiftE` (E over `(11010)^n` leaves `(01010)^n`), for every n and any surrounding tapes. The counter map is observed, not proved.

## Later

1. Sample at the A-left events and write the tape as a list of (a-run, c-run) groups; find the rule that moves counts between levels.
2. If it is a counter with fixed digit rules, prove the per-level rules with `bbtools.symtm` and the counter by induction.
3. Work out what happens when a c-run reaches 0 (the moment a level carries).

## Pages

- [`pages/holdouts/1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---/explainer.html`](../../pages/holdouts/1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---/explainer.html)
- [`pages/holdouts/1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---/proof-status.html`](../../pages/holdouts/1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---/lean/check.sh
```
