# 1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD---

bbchallenge id 52729, group G08 (two-sided square-root growth). Whether it halts from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 0LC | 0RF |
| C | 1LD | 1LC |
| D | 1RA | 0RD |
| E | 0LA | 1LA |
| F | 1RD | --- |

## What it does

A two-sided bouncer over an irregular tape: runs of 1, 2 or 3 ones with gaps of 1 to 8 zeros, short repeats like
`(1101)^k` and `(010)^k`, no word repeating across the tape.

Shift rules (Lean, any n): `1^n C>1 -> C>1 1^n`, `D> 1^n -> 0^n D>`, `(11)^n A>1 -> A>1 (10)^n`,
`(10)^n A>1 -> A>1 (00)^n`, `(11)^n E>1 -> E>1 (01)^n`.

## How it would halt

F1 is the only halting transition. F is entered only from B1, B only from A0 (`enter_F`, `enter_B`): a halt is
exactly `A>0 1 1`. A is entered from D0 (moving right) and from E0 / E1 (moving left, `enter_A`). E is entered only
from A1, which writes 0, and the following B or F reads that 0 (`enter_E`, `via_E0_safe`, `via_E1_safe`). So a halt
needs `D>0 0 1 1` (`halt_D`). In 2*10^9 steps D read 0 about 2.4*10^8 times and never before `0 1 1` (`c/ctx.c`).

## What is established

- **Kernel** (`lean/Halt.lean`): `halt_F`, `halt_B`, `halt_A`, `halt_D`, `enter_F`, `enter_B`, `enter_A`, `enter_E`,
  `via_E0_safe`, `via_E1_safe`.
- **Kernel** (`lean/Rules.lean`): `cleft`, `derase`, `aleft11`, `aleft10`, `eleft`.
- **Kernel / native** (`lean/Blank.lean`): the halting configurations; no halt in 10^4 / 10^7 steps.
- **Trusted** (C): no halt in 10^11 steps (`c/longrun.c`); the contexts of D0 (`c/ctx.c`).
- **Heuristic**: no regular words.
- **Failed**: window CTL (K <= 7), n-gram CPS (`tools/c/ngramcps.c`): plain at widths 4, 6, 8, and with LRU history (`-U`) or fixed history 2 and 4
  (`-H`) at widths 3 to 9, all UNKNOWN or over the configuration limit; also `-U` and `-H 2` at width 10: over the limit of 3*10^7 configurations.

## Open, and next steps

Open. Next: the D0 contexts are very lopsided (`0 1 0` in 79% of cases), which suggests a local invariant around
D's rightward runs; try a CTL whose states remember the last few cells D has erased. Later: the tape itself looks
chaotic.

## Files

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | generated: the machine, its halting configurations, bounded runs from blank tape |
| `lean/Halt.lean` | how a halt comes about: the halting patterns and the ways into the halting state (kernel) |
| `lean/Rules.lean` | shift rules for any count (kernel, written by `tools/py/bbtools/symtm.py`) |
| `c/longrun.c` | the run from blank tape, with the tape's extent at powers of ten |
| `c/runhist.c` | the run lengths of the tape at every moment the head reaches a new cell |
| `c/trfreq.c` | how often each transition is used |
| `c/ctx.c` | counts the tape windows around the head each time a given state reads a given symbol |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD---/lean/check.sh
cd holdouts/1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD---/c
gcc -O2 -o longrun longrun.c && ./longrun 1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD--- 100000000000      # about 20 minutes
gcc -O2 -o runhist runhist.c && ./runhist 1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD--- 10000000000
gcc -O2 -o trfreq trfreq.c && ./trfreq 1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD--- 100000000
gcc -O2 -o ctx ctx.c && ./ctx 1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD--- 2000000000 D 0 3
```
