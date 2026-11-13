# 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC

bbchallenge id 76289, group G08 (two-sided square-root growth). Whether it halts from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 1RC | --- |
| C | 1RD | 1RA |
| D | 0RE | 1LC |
| E | 1LF | 0RF |
| F | 1LD | 0RC |

## What it does

A two-sided bouncer whose head zig-zags across the tape. At the moments the head reaches a new cell on the right, the
tape read in the words `x = 0001`, `y = 0001111`, `z = 0111111` is

    1^3 x^2 z x^N (middle zone) (z x^2 y x)^K A>0

The zone right of the tail repeats exactly every 13 visits to the right end from the 112th on (through 3*10^8
steps, `c/edge.c`, `py/zones.py`); it feeds new periods into the tail, whose left end the middle zone eats into from
time to time. The run `x^N` grows more slowly and from time to time
freezes (at 185 after about 6*10^7 steps; a new run of x then grows to its right). The middle zone, a few dozen words
long, has no visible pattern. At the left end the same tape appears in a shifted code (words `0011`, `0000011`,
`0011111`); every sweep translates the whole tape between the two codes.

Shift rules (Lean, any n): `C> (0011)^n -> (1000)^n C>`, `A> (001)^n -> (111)^n A>`, `1^n A>1 -> A>1 0^n`,
`0 F> 0^n -> 0^n 0 F>`.

## How it would halt

The only halting transition is B1. B is entered only from A0 (`enter_B`), so it halts exactly at `A>0 1`. A is
entered from A1 (moving left; the cell to its right was just erased) and from C1 (moving right) (`enter_A`), so a halt
needs `C>1 0 1` (`halt_C`): C reads a 1 followed by an isolated 0. Isolated 0s are common (one in each z), but in
10^8 steps C has read 8.75 million 1s and always with `0 0` after them.

## What is established

- **Kernel** (`lean/Halt.lean`): `halt_B`, `halt_A`, `halt_C`, `enter_B`, `enter_A`.
- **Kernel** (`lean/Rules.lean`): `cconv`, `afill`, `aerase`, `fzero`.
- **Kernel / native** (`lean/Blank.lean`): the halting configurations; no halt in 10^4 / 10^7 steps.
- **Trusted** (C): no halt in 10^11 steps (`c/longrun.c`); C reads 1s only in front of `0 0` in 10^8 steps
  (`c/trfreq.c`).
- **Trusted** (C + Python): the right end is periodic with period 13 visits (`py/zones.py`).
- **Heuristic**: the tape shape above (`tools/c/tmrun.c` records).
- **Failed**: window CTL (K <= 7), n-gram CPS (`tools/c/ngramcps.c`): plain at widths 4, 6, 8, and with LRU history (`-U`) or fixed history 2 and 4
  (`-H`) at widths 3 to 9, all UNKNOWN or over the configuration limit; also `-U` at width 10 and `-H 2` at width 10: UNKNOWN, `-U` at width 12: over the limit of 3*10^7 configurations.

## Open, and next steps

Open. A separation argument (prove the 13-visit cycle of the right end for all K and show that the halting
pattern can only come from there) does not work: in 10^9 steps every `C>1 0` away from the right edge happened at
the join between the run of x and the irregular middle (44 times, always followed by `0 0`; `c/evt.c`), and at the
right edge the next cell is blank. So the danger is next to the irregular middle. Next: find the macro map of the middle zone (it is fed from both sides; the frozen runs of x suggest a counter
whose digits are runs of x), and look for an invariant on the side of z that C approaches.

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
| `c/edge.c` | the whole tape each time the head reaches a fresh cell on one side |
| `py/zones.py` | cuts those tapes after the periodic tail and finds the period of the rest |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC/lean/check.sh
cd holdouts/1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC/c
gcc -O2 -o longrun longrun.c && ./longrun 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 100000000000      # about 20 minutes
gcc -O2 -o runhist runhist.c && ./runhist 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 10000000000
gcc -O2 -o trfreq trfreq.c && ./trfreq 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 100000000
gcc -O2 -o evt evt.c && ./evt 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 1000000000 C 1 6 3 | grep '\[1\]0'
gcc -O2 -o edge edge.c && ./edge 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC 300000000 R 1 > edgeR.txt && python3 ../py/zones.py edgeR.txt
```
