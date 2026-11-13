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

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| right | 256,071,848 | 18,577 | 12 | 11 | 17 | 0.88 |
| left | 279,146,051 | 19,447 | 15 | 13 | 19 | 0.88 |
| left | 1,035,688,785 | 24,785 | 15 | 15 | 24 | 0.32 |
| right | 1,488,650,106 | 24,829 | 6 | 14 | 20 | 0.32 |
| right | 4,099,398,448 | 49,147 | 7 | 20 | 27 | 0.49 |
| left | 4,175,558,235 | 50,232 | 36 | 23 | 36 | 0.50 |
| left | 16,405,165,975 | 133,330 | 28 | 25 | 35 | 0.81 |
| right | 17,002,373,871 | 133,374 | 7 | 20 | 27 | 0.81 |

**Proposed family: F06, block-list counters** (a slowly growing list of units made of two words).

The description grows slowly: 19, 24, 36 and 35 level-2 tokens at the left-end records at 2.8·10^8, 10^9, 4.2·10^9 and 1.6·10^10 steps. At the last one the tape is a block `(010)^1537`, then a list of blocks of the words `10101` and `100` (3 to 1,184 copies each) closed by markers `1010 (01)^3`, and a last block `(10101)^21602`.

A list of units of the same form whose number grows slowly is a list of counters (F06) and not a bounded description (F01): the token count nearly doubled on the screen.

Next step: The round rule on the list of pairs (a, b), sampled at the left-end records, and the rule that adds a unit.

## Pages

- [`pages/holdouts/1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---/explainer.html`](../../pages/holdouts/1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---/explainer.html)
- [`pages/holdouts/1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---/proof-status.html`](../../pages/holdouts/1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC0LE_1RD1RA_0RE1RF_1LF0RC_0LA---/lean/check.sh
```
