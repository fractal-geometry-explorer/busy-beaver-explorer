# 1RB0RD_0LC1LD_1RA1LA_1RE1LB_---0RF_1RA1RF

bbchallenge id 8646. One of the six-state holdouts whose halting from blank tape is open (group G13). Family: **two-ended sweeper over an irregular block word**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 0LC | 1LD |
| C | 1RA | 1LA |
| D | 1RE | 1LB |
| E | --- | 0RF |
| F | 1RA | 1RF |

## What it does

The tape is a word of short blocks of 1s, each followed by a single 0, for example (step 93,864,904, from the left) 1 0 1^7 0 1^3 0 1 0 1 0 1 0 1^3 0 1 0 1^2 0 1 0 1^5 0 &hellip;. Long stretches are 1 0 1 0 &hellip;, the longer blocks have up to about 20 ones.

The head sweeps the whole word: in the first 108 steps it reaches the right end in state F 6,291 times and the left end in state B 3,656 times and in D 3,589 times. Most of the word is unchanged from one sweep to the next; the changes are near the two ends. The visited width roughly doubles each time the step count quadruples (2,000 cells at 1.5*106 steps, 4,000 at 5.9*106, 8,000 at 2.1*107, 16,000 at 8.4*107), so it grows like the square root of the time, as for a bouncer whose sweeps get longer by a constant.

### Halting

The machine halts when it reads a 0 in state E (E0 is the halting transition). E is entered from D on a 0 (D0 = 1RE); so a halt needs D>0 0, the head in D moving right onto two 0s in a row. In ten snapshots of the tape, one every 107 steps up to 108, there are no two adjacent 0s anywhere between the ends, so such a halt would have to happen at an end of the tape.

## Phase 2 results

`lean/Rules.lean` (`py/gen_rules.py`, symtm) proves two shift rules for every n: A over `(1010)^n` leaves `(0101)^n`,
F over `(0101)^n` leaves `(1010)^n`. No exact sweep map was found.

## Status

Open. Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel) and 10^7 (`native_decide`). C: no halt in 10^9 steps. Lean (`lean/Rules.lean`, kernel): the shift rules `shiftA` (A over `(1010)^n` leaves `(0101)^n`) and `shiftF` (F over `(0101)^n` leaves `(1010)^n`), for every n and any surrounding tapes. The sweep map is observed, not proved.

## Later

1. Find the rule by which one sweep changes the two ends (sample at the F-right and D-left events, compare consecutive words).
2. Check whether the inside of the word ever changes; if not, the ends are two separate counters and the machine may reduce to a pair of counters.
3. Try `bbtools.ctl` with a larger window only if the words near the ends turn out to be regular.

## Pages

- [`pages/holdouts/1RB0RD_0LC1LD_1RA1LA_1RE1LB_---0RF_1RA1RF/explainer.html`](../../pages/holdouts/1RB0RD_0LC1LD_1RA1LA_1RE1LB_---0RF_1RA1RF/explainer.html)
- [`pages/holdouts/1RB0RD_0LC1LD_1RA1LA_1RE1LB_---0RF_1RA1RF/proof-status.html`](../../pages/holdouts/1RB0RD_0LC1LD_1RA1LA_1RE1LB_---0RF_1RA1RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_0LC1LD_1RA1LA_1RE1LB_---0RF_1RA1RF/lean/check.sh
```
