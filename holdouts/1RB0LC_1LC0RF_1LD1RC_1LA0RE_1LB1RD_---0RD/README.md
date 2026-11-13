# 1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD

bbchallenge id 174142, group G08 (two-sided square-root growth). Whether it halts from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LC | 0RF |
| C | 1LD | 1RC |
| D | 1LA | 0RE |
| E | 1LB | 1RD |
| F | --- | 0RD |

## What it does

A two-sided bouncer. Each time the head reaches a fresh cell at the left end the tape is
`A>0 1 1 0` followed by blocks `1^m 0`; 99.7% of them have m = 4k+3 (in 10^8 steps), k irregular and changing from
sweep to sweep, each k about half as common as k-1. At the right end
the tape shows runs of 1s of length 1 mod 4 and stretches of `(01)^j`.

Shift rules (Lean, any n): `C> 1^n -> 1^n C>`, `1^n C>0 0 -> C>0 0 1^n`, `D> (11)^n -> (01)^n D>`,
`E> (11)^n -> (10)^n E>`.

## How it would halt

F0 is the only halting transition. F is entered only from B1 (`enter_F`). B is entered from A0 and E0
(`enter_B`); E is entered only from D1, after which B reads the 0 D wrote (`enter_E`, `via_E_safe`). So a halt needs
`A>0 1 0` (`halt_A`). `A>0 1 1 0 -> 1 0 A>0 1` in four steps (`achain`), so the halting tapes are exactly
`A>0 1 (10)^n 0` (`halt_chain`, any n). In 2*10^9 steps A reads 0 only in front of `111` or `11011` (`c/evt.c`).

## What is established

- **Kernel** (`lean/Halt.lean`): `halt_F`, `halt_B`, `halt_A`, `enter_F`, `enter_B`, `enter_E`, `enter_A`,
  `via_E_safe`, `achain`, `halt_chain`.
- **Kernel** (`lean/Rules.lean`): `cright`, `cleft`, `dright`, `eright`.
- **Kernel / native** (`lean/Blank.lean`): the halting configurations; no halt in 10^4 / 10^7 steps.
- **Trusted** (C): no halt in 10^11 steps (`c/longrun.c`); what A sees when it reads 0 (`c/evt.c`).
- **Heuristic**: the 4k+3 block form at the left end.
- **Failed**: window CTL (K <= 7), n-gram CPS (`tools/c/ngramcps.c`): plain at widths 4, 6, 8, and with LRU history (`-U`) or fixed history 2 and 4
  (`-H`) at widths 3 to 9, all UNKNOWN or over the configuration limit; also `-U` at widths 10 and 12 and `-H 2` at width 10: UNKNOWN.

## Open, and next steps

Open. Next: find the map that one sweep pair applies to the list of block lengths k (the right-end form suggests
each block is rewritten locally, with a carry), and see whether the walk `A>0 1 (10)^n` can only end in `1 1`.
Later: the block lengths look irregular; if the sweep map is Collatz-like this will stay open.

## Files

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | generated: the machine, its halting configurations, bounded runs from blank tape |
| `lean/Halt.lean` | how a halt comes about: the halting patterns and the ways into the halting state (kernel) |
| `lean/Rules.lean` | shift rules for any count (kernel, written by `tools/py/bbtools/symtm.py`) |
| `c/longrun.c` | the run from blank tape, with the tape's extent at powers of ten |
| `c/runhist.c` | the run lengths of the tape at every moment the head reaches a new cell |
| `c/trfreq.c` | how often each transition is used |
| `c/evt.c` | the tape around the head each time a given state reads a given symbol |

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 24, history 1 up to width 24, history 2 up to width 24, history 3 up to width 24, LRU history up to width 16 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 20, p = 3 up to width 20, p = 4 up to width 20, p = 6 up to width 20.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..10; n = 11 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: A with 0 under the head, 1 right, 0 two right.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD/lean/check.sh
cd holdouts/1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD/c
gcc -O2 -o longrun longrun.c && ./longrun 1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD 100000000000      # about 20 minutes
gcc -O2 -o runhist runhist.c && ./runhist 1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD 10000000000
gcc -O2 -o trfreq trfreq.c && ./trfreq 1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD 100000000
gcc -O2 -o evt evt.c && ./evt 1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD 2000000000 A 0 0 6 | cut -d' ' -f4 | sort | uniq -c
```
