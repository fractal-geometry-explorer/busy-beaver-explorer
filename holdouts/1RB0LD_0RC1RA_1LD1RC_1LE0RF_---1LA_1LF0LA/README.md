# 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA

bbchallenge id 137602, group G08 (two-sided square-root growth). Whether it halts from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | 1RA |
| C | 1LD | 1RC |
| D | 1LE | 0RF |
| E | --- | 1LA |
| F | 1LF | 0LA |

## What it does

A two-sided bouncer. At the moments the head reaches a fresh cell on the right, the tape is

    (101)^a  (irregular zone, a few dozen cells)  w^K  (irregular zone)  C>0

with `w = 110111011101101101110111101111101111101111111011111` (51 cells). K was 73 / 113 / 151 at widths 4000 / 6000 / 8000, so `w^K` fills most of the tape; a
grows slowly. The right zone repeats exactly every 8 visits to the right end from the 173rd on (checked through
10^8 steps, `c/edge.c`, `py/zones.py`); the left zone (533 different values in 632 visits) does not.

Shift rules (Lean, any n): `(011101111011111011111011111110111111101110111011011)^n D>0 0 0 -> D>0 0 0 (110111011011111111100110111101100111110011110110111)^n` (201 steps a word;
the first word is a rotation of w), `0^n F>0 -> F>0 1^n`, `C> 1^n -> 1^n C>`, `C> (10)^n -> (10)^n C>`,
`A> (01)^n -> (11)^n A>`, `B> (10)^n -> (11)^n B>`.

## How it would halt

E0 is the only halting transition; E is entered only from D0 (`enter_E`), so it halts exactly at `0 D>0`
(`halt_D`). D is entered from A1 and C0, both moving left (`enter_D`): `0 0 A>1`, `0 0 C>0`. In 3*10^9 steps D read
0 about 1.39*10^8 times, always with a 1 on its left (`c/ctx.c`).

## What is established

- **Kernel** (`lean/Halt.lean`): `halt_E`, `halt_D`, `halt_A`, `halt_C`, `enter_E`, `enter_D`.
- **Kernel** (`lean/Rules.lean`): `dword`, `ffill`, `cright`, `cright10`, `afill`, `bfill`.
- **Kernel / native** (`lean/Blank.lean`): the halting configurations; no halt in 10^4 / 10^7 steps.
- **Trusted** (C): no halt in 10^11 steps (`c/longrun.c`); the left neighbour of D0 is always 1 in 3*10^9
  steps (`c/ctx.c`).
- **Trusted** (C + Python): the right zone cycles with period 8; the left zone does not repeat (`py/zones.py`).
- **Heuristic**: the tape shape above.
- **Failed**: window CTL (K <= 7), n-gram CPS (`tools/c/ngramcps.c`): plain at widths 4, 6, 8, and with LRU history (`-U`) or fixed history 2 and 4
  (`-H`) at widths 3 to 9, all UNKNOWN or over the configuration limit; also `-U` at width 10 and `-H 2` at width 10: UNKNOWN, `-U` at width 12: over the limit of 3*10^7 configurations.

## Open, and next steps

Open. The leftward pass over the run is proved (`dword`); the rightward pass is done by C in a zig-zag, 705 steps a
word, and I did not find a form symtm accepts (it looks ahead into the next word). Next: write that rule, then the
8-sweep cycle of the right end (that part is
an exact cycle and can be written as chained rules), which would reduce the question to the left zone. Later: the
left zone, with its run `(101)^a`, looks chaotic.

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
| `c/edge.c` | the whole tape each time the head reaches a fresh cell on one side |
| `py/zones.py` | cuts those tapes at the copies of w and looks for repeats of the zones |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA/lean/check.sh
cd holdouts/1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA/c
gcc -O2 -o longrun longrun.c && ./longrun 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA 100000000000      # about 20 minutes
gcc -O2 -o runhist runhist.c && ./runhist 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA 10000000000
gcc -O2 -o trfreq trfreq.c && ./trfreq 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA 100000000
gcc -O2 -o ctx ctx.c && ./ctx 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA 3000000000 D 0 1
gcc -O2 -o edge edge.c && ./edge 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA 100000000 R 1 > edgeR.txt && ./edge 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA 60000000 L 1 > edgeL.txt
python3 ../py/zones.py edgeR.txt edgeL.txt
```
