# 1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---

bbchallenge id 11596, group G08 (two-sided square-root growth). Whether it halts from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 0RB |
| C | 0RD | 1LE |
| D | 0LE | 0RA |
| E | 1LC | 1LA |
| F | 0LD | --- |

## What it does

A two-sided bouncer on four-cell words. At the left end the tape reads `C>0 (1000)^k ...` or `E>0 (0001)^k ...`,
then a long list of runs `(0100)^a1 (0111)^b1 (0100)^a2 (0111)^b2 ...` (values like 13, 25, 58, 46, 25, 34), then an
active zone. The sweeps translate the words (`0100 <-> 0001`, `0111 <-> 1101`, ...) but keep the counts, so the list
survives from sweep to sweep and changes only next to the left counter and in the active zone.

Shift rules (Lean, any n): `D> (1000)^n -> (0110)^n D>`, `A> (0001)^n -> (1100)^n A>`, `C> (0100)^n -> (0011)^n C>`,
`B> (0010)^n -> (1001)^n B>`, `B> 1^n -> 0^n B>`, `(0001)^n E>0 -> E>0 (0001)^n`, `(0010)^n D>0 -> D>0 (0010)^n`,
`(01)^n E>0 -> E>0 (11)^n`, `(10)^n C>1 -> C>1 (11)^n`.

## How it would halt

F1 is the only halting transition; F is entered only from A1 (`enter_F`), so a halt is exactly `1 A>1`. A is
entered from D1 and E1 (`enter_A`); after D1, F reads the 0 D wrote (`via_D_safe`). So a halt needs `1 1 E>1`
(`halt_E`), from `1 1 1 C>1` or `1 1 1 D>0`. In 2*10^9 steps E read 1 about 1.7*10^8 times, never with `1 1` on its
left (`c/ctx.c`).

## What is established

- **Kernel** (`lean/Halt.lean`): `halt_F`, `halt_A`, `halt_E`, `halt_C`, `halt_D`, `enter_F`, `enter_A`, `enter_E`,
  `via_D_safe`.
- **Kernel** (`lean/Rules.lean`): `dword`, `aword`, `cword`, `bword`, `berase`, `eshift`, `dshift`, `efill`, `cfill`.
- **Kernel / native** (`lean/Blank.lean`): the halting configurations; no halt in 10^4 / 10^7 steps.
- **Trusted** (C): no halt in 10^11 steps (`c/longrun.c`); E1 never has `1 1` on its left (`c/ctx.c`).
- **Heuristic**: the list of counters.
- **Failed**: window CTL (K <= 7), n-gram CPS (`tools/c/ngramcps.c`): plain at widths 4, 6, 8, and with LRU history (`-U`) or fixed history 2 and 4
  (`-H`) at widths 3 to 9, all UNKNOWN or over the configuration limit.

## Open, and next steps

Open.

Deep dive (asked for a full non-halting proof; not reached). What the sweeps do, as far as I worked it out:

- **Left end.** At successive fresh left cells in state E the tape starts `E>0 (0001)^a X (0111)^b ...`, with X one
  of a few short phase words. Each such visit adds one to a, and every third visit removes one word from the b-run,
  so the run `(0111)^b` is turned into about `3b` words `0001`. When the b-run is used up, the head rewrites the
  whole left counter (`1 (1000)^2 (1110)^(a-1) ...`) and starts on the next pair of the list. The counter sizes at
  these resets (22, 28, 34, 40, ..., 170 in the first 10^8 steps) are irregular.
- **Middle.** The list `(0100)^x (0111)^y ...` is carried unchanged from sweep to sweep (only the code changes:
  `0100 <-> 0001`, `0111 <-> 1101`), so the left end consumes it like a queue.
- **Right end.** New pairs are produced in a zone of about 250 cells whose content changes irregularly from sweep to
  sweep; it holds a second list in another block format (`(0100)^x (0111)^3 01 000 (1110)^y (1000)^3 111`).

A proof along the lines asked would need the exact rule of the right-end zone. That zone looks chaotic, so the
induced queue system has no simple description and I stopped there. Later: if the right-end zone turns out to
cycle or to be a fixed function of a few counters, the left-end and list rules above can be written with symtm.

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
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---/lean/check.sh
cd holdouts/1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---/c
gcc -O2 -o longrun longrun.c && ./longrun 1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD--- 100000000000      # about 20 minutes
gcc -O2 -o runhist runhist.c && ./runhist 1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD--- 10000000000
gcc -O2 -o trfreq trfreq.c && ./trfreq 1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD--- 100000000
gcc -O2 -o ctx ctx.c && ./ctx 1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD--- 2000000000 E 1 2
```
