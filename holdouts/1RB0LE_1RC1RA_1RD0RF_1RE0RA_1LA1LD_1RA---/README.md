# 1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---

bbchallenge id 10690, group G08 (two-sided square-root growth). Whether it halts from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 1RA |
| C | 1RD | 0RF |
| D | 1RE | 0RA |
| E | 1LA | 1LD |
| F | 1RA | --- |

## What it does

A two-sided bouncer that runs a queue of counters. At each fresh left cell the tape is runs of 1s spaced three apart
(words `100` / `001`), the runs separated by `0000`. As numbers: e.g. 48, 17, 53, 7, 47, 15, 37, ... Between
consecutive such moments only the first number changes (down by 2) and the far end of the list is rewritten; when the
first number is used up the next takes over. The list grew past 200 numbers in 5*10^7 steps, with occasional
reorganisations (176 -> 88 numbers at about 2.5*10^7 steps). At the right end the same tape is written in blocks
`110111`, `111101`, `011111` separated by `1^6 0 1^6 0` and similar markers.

Shift rules (Lean, any n): `A> (001001)^n -> (110111)^n A>`, `F> (001001)^n -> (111110)^n F>`,
`C> (100100)^n -> (011111)^n C>`, `B> (100100)^n -> (111011)^n B>`, `A> (01)^n -> (11)^n A>`,
`B> (10)^n -> (11)^n B>`, `(01)^n E>0 -> E>0 (01)^n`, `(10)^n A>1 -> A>1 (10)^n`.

## How it would halt

F1 is the only halting transition. F is entered only from C1, C only from B0, B only from A0, all moving right:
a halt is exactly `A>0 0 1 1` (`halt_A`). In 2*10^9 steps A read 0 about 2.3*10^8 times, never before `0 1 1`
(`c/ctx.c`).

## What is established

- **Kernel** (`lean/Halt.lean`): `halt_F`, `halt_C`, `halt_B`, `halt_A`, `enter_F`, `enter_C`, `enter_B`.
- **Kernel** (`lean/Rules.lean`): `aword`, `fword`, `cword`, `bword`, `afill`, `bfill`, `eleft`, `aleft`.
- **Kernel / native** (`lean/Blank.lean`): the halting configurations; no halt in 10^4 / 10^7 steps.
- **Trusted** (C): no halt in 10^11 steps (`c/longrun.c`); the contexts of A0 (`c/ctx.c`).
- **Heuristic**: the queue of counters (`c/zrec.c`).
- **Failed**: window CTL (K <= 7), n-gram CPS (`tools/c/ngramcps.c`): plain at widths 4, 6, 8, and with LRU history (`-U`) or fixed history 2 and 4
  (`-H`) at widths 3 to 9, all UNKNOWN or over the configuration limit; also `-U` at width 10: over the limit of 3*10^7 configurations.

## Open, and next steps

Open.

Deep dive (asked for a full non-halting proof; not reached). Between consecutive fresh left cells the first number
goes down by 2 and the middle of the list is unchanged, but the last five or so numbers are rewritten every sweep in
no visible pattern (for example `27 16 6 7 8 -> 27 6 36 27 49 -> 27 14 44 19 39 -> 19 18 32 29 27` at about
3*10^6 steps), and from time to time the whole list is reorganised (176 -> 88 numbers). So the producer at the right
end is an irregular zone, the induced queue system has no simple rule I could find, and I stopped there. Later: if
that zone is found to be a function of a few counters, the crossing rules in `lean/Rules.lean` are the pieces a
proof would chain.

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
| `c/zrec.c` | the tape at each fresh left cell (use a word that never matches, e.g. `2`, and print mode 1) |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---/lean/check.sh
cd holdouts/1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---/c
gcc -O2 -o longrun longrun.c && ./longrun 1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA--- 100000000000      # about 20 minutes
gcc -O2 -o runhist runhist.c && ./runhist 1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA--- 10000000000
gcc -O2 -o trfreq trfreq.c && ./trfreq 1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA--- 100000000
gcc -O2 -o ctx ctx.c && ./ctx 1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA--- 2000000000 A 0 3
gcc -O2 -o zrec zrec.c && ./zrec 1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA--- 30000000 A 2 1 | tail -2
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---`](../1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---`](../1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F; it is this table started in state C
- [`1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---`](../1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F; it is this table started in state D

<!-- end of related machines -->
