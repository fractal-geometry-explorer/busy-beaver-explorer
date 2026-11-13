# 1RB0RE_1RC0RE_1LD1RB_1LA0LA_1RF0LC_---0RC

bbchallenge id 1125. One of the six-state holdouts whose halting from blank tape is open (group G13). Family: **digit string in two encodings, swept from the left end**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1RC | 0RE |
| C | 1LD | 1RB |
| D | 1LA | 0LA |
| E | 1RF | 0LC |
| F | --- | 0RC |

## What it does

The tape is a string of short blocks of 1s separated by single 0s. When the head is at the left end, the blocks are 1, 1^2, 1^3 (step 93,167,380: A>0 1^2 0 1^2 0 1^2 0 1 0 1 0 1^2 0 &hellip;); when it has reached the right end, the blocks are longer, 1^3, 1^7, 1^10, 1^12, 1^16 (step 25,763,983, from the left: 1^2 0 1^12 0 1^12 0 1 0 1^3 0 1^12 0 1 0 1^7 0 &hellip;). As in the G13 family of 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA, the head seems to carry one list of numbers across the tape, rewriting it between two encodings.

The head returns to the left end in state A often (30,210 times in the first 108 steps) and the tape grows to the left: 3,000 cells at 3.6*106 steps, 30,000 at 9.3*107.

### Halting

The machine halts when it reads a 0 in state F (F0 is the halting transition). F is entered from E on a 0 (E0 = 1RF), so a halt needs E>0 0.

## Phase 2 results

`lean/Rules.lean` proves two shift rules for every n: B over `(01)^n` and C over `(10)^n`, each leaving `(11)^n`.
No exact pass map was found.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel) and 10^7 (`native_decide`). C: no halt in 10^9 steps. Lean (`lean/Rules.lean`, kernel): the shift rules `shiftB` (B over `(01)^n`) and `shiftC` (C over `(10)^n`), each leaving `(11)^n`, for every n and any surrounding tapes. The pass map is observed, not proved.

## Later

1. Find the exact correspondence between the two encodings (which short-digit word each long block becomes).
2. Sample at the A-left events, write the tape as a list of numbers and look for a pass map, as for the 1RB0LA_1RC--- family.
3. Check whether the map is a counter (growth exponent below 1 suggests passes of growing length).

## Pages

- [`pages/holdouts/1RB0RE_1RC0RE_1LD1RB_1LA0LA_1RF0LC_---0RC/explainer.html`](../../pages/holdouts/1RB0RE_1RC0RE_1LD1RB_1LA0LA_1RF0LC_---0RC/explainer.html)
- [`pages/holdouts/1RB0RE_1RC0RE_1LD1RB_1LA0LA_1RF0LC_---0RC/proof-status.html`](../../pages/holdouts/1RB0RE_1RC0RE_1LD1RB_1LA0LA_1RF0LC_---0RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1RC0RE_1LD1RB_1LA0LA_1RF0LC_---0RC/lean/check.sh
```
