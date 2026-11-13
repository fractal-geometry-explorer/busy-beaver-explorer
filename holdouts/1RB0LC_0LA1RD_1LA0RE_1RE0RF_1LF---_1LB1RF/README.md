# 1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF

bbchallenge id 31128, group G08 (two-sided square-root growth). Whether it halts from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 0LA | 1RD |
| C | 1LA | 0RE |
| D | 1RE | 0RF |
| E | 1LF | --- |
| F | 1LB | 1RF |

## What it does

A two-sided bouncer: the head sweeps across the whole tape and adds about a cell at each end per sweep. The tape is
runs of 1s (length 1 to 13) separated by one or two 0s, with no repeating word or counter that I could find.

Shift rules (Lean, any n): `F> 1^n -> 1^n F>`, `F> (10)^n -> (10)^n F>`, `(10)^n A>1 -> A>1 (10)^n`,
`(01)^n C>0 -> C>0 (01)^n`, `(011)^n B>0 -> B>0 (110)^n`.

## How it would halt

E1 is the only halting transition. E is entered from C1 and D0 (`enter_E`). C is entered only from A1 moving left,
which leaves a 0 to C's right, so the C route never halts (`enter_C`, `via_C_safe`). D is entered only from B1
(`enter_D`), so the machine halts exactly at `B>1 0 1` (`halt_B`).

In 10^10 steps, A reads 0 only on a fresh left cell and D reads 0 only two cells later; the three cells right of A
are then always `100` or `011`, never `101` (`c/evt.c`).

## What is established

- **Kernel** (`lean/Halt.lean`): `halt_E`, `halt_D`, `halt_B`, `halt_A`, `enter_E`, `enter_C`, `enter_D`, `via_C_safe`.
- **Kernel** (`lean/Rules.lean`): `fright`, `fright10`, `aleft`, `cleft`, `bleft`.
- **Kernel / native** (`lean/Blank.lean`): the halting configurations; no halt in 10^4 / 10^7 steps.
- **Trusted** (C): no halt in 10^11 steps (`c/longrun.c`); A0 and D0 only at the left end, with the left
  end `100` or `011`, in 10^10 steps (`c/evt.c`).
- **Heuristic**: no regular words in the tape.
- **Failed**: window CTL (K <= 7), n-gram CPS (`tools/c/ngramcps.c`): plain at widths 4, 6, 8, and with LRU history (`-U`) or fixed history 2 and 4
  (`-H`) at widths 3 to 9, all UNKNOWN or over the configuration limit; also `-U` at width 10 and `-H 2` at width 10: UNKNOWN, `-U` at width 12: over the limit of 3*10^7 configurations.

## Open, and next steps

Open. The whole question is about the left end: what the first few cells are each time the head arrives there.
Next: find what the left end depends on (how far into the tape a sweep's changes reach it), and look for an
invariant on that prefix. Later: this looks chaotic, and I did not find a macro structure.

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

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 1 under the head, 0 right, 1 two right.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF/lean/check.sh
cd holdouts/1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF/c
gcc -O2 -o longrun longrun.c && ./longrun 1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF 100000000000      # about 20 minutes
gcc -O2 -o runhist runhist.c && ./runhist 1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF 10000000000
gcc -O2 -o trfreq trfreq.c && ./trfreq 1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF 100000000
gcc -O2 -o evt evt.c && ./evt 1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF 10000000000 D 0 2 2 | cut -d' ' -f2,4 | sort | uniq -c
```
