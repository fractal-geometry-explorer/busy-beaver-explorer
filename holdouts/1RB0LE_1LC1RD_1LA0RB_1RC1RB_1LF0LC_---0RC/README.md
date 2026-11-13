# 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC

bbchallenge id 101395, group G08 (two-sided square-root growth). Whether it halts from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 1RD |
| C | 1LA | 0RB |
| D | 1RC | 1RB |
| E | 1LF | 0LC |
| F | --- | 0RC |

## What it does

A two-sided bouncer. Each time the head reaches a fresh cell at the left end the tape is

    A>0 (1101101101)^K Z

In 3*10^10 steps (77275 samples, `c/zrec.c`) K grew to 11055, almost always by one every 7 samples (11002 of
11056 increases). The first ~50 cells of Z repeat with that period and feed the run; the rest of Z is irregular,
269 to 557 cells long, and never repeated.

Shift rules (Lean, any n): `B> (1101101101)^n -> (1011110110)^n B>` (12 steps a word),
`(0101111011)^n C>0 0 -> C>0 0 (0110110111)^n` (58 steps a word; the two words are rotations of the run's word), `B> (11)^n -> (11)^n B>`,
`D> (10)^n -> (01)^n D>`, `(011)^n C>0 -> C>0 (001)^n`, `(101)^n A>1 -> A>1 (100)^n`.

## How it would halt

F0 is the only halting transition. F is entered only from E0, E only from A1, A only from C0, all moving left
(`enter_F`, `enter_E`, `enter_A`): a halt is exactly `0 E>0` = `0 0 A>1` = `0 0 1 C>0`. In 2*10^9 steps A read 1
about 2.3*10^8 times, never with `0 0` on its left (`c/ctx.c`).

## What is established

- **Kernel** (`lean/Halt.lean`): `halt_F`, `halt_E`, `halt_A`, `halt_C`, `enter_F`, `enter_E`, `enter_A`.
- **Kernel** (`lean/Rules.lean`): `bword`, `cback`, `bright`, `dright`, `cleft`, `aleft`.
- **Kernel / native** (`lean/Blank.lean`): the halting configurations; no halt in 10^4 / 10^7 steps.
- **Trusted** (C): no halt in 10^11 steps (`c/longrun.c`); A1 never has `0 0` on its left in 2*10^9
  steps (`c/ctx.c`).
- **Heuristic**: the shape `A>0 W^K Z` with Z of bounded size (`c/zrec.c`).
- **Failed**: window CTL (K <= 7), n-gram CPS (`tools/c/ngramcps.c`): plain at widths 4, 6, 8, and with LRU history (`-U`) or fixed history 2 and 4
  (`-H`) at widths 3 to 9, all UNKNOWN or over the configuration limit; also `-H 2` at width 10: UNKNOWN, `-U` at widths 10 and 12: over the limit of 3*10^7 configurations.

## Open, and next steps

Open. The run of W is crossed uniformly, so the machine is a bounded zone Z driven by the sweeps. Next: glue `bword`
and `cback` to the ends of the run (the turn at the left end and the entry into Z), check that one sweep pair acts
on Z independently of K, and study Z as a finite system: if Z stays bounded it must eventually repeat, which would
give a non-halting proof. Deep dive (the bounded-zone idea). A reduced simulator that deletes copies of W at the left end (`c/m7z.c`;
it agrees with the full run on all 77275 visits checked) ran 7.7*10^8 visits, about 10^12 steps of the reduced
machine and 1.1*10^8 copies of W, with Brent's cycle check on Z: no repeat (no cycle of period up to 2*10^8
visits starting in the first 5*10^8), and Z stayed under 500 cells at every sample. So a proof that Z eventually
repeats is not available, and the idea is shelved. Later: Z behaves like a chaotic finite-but-large system.

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
| `c/zrec.c` | at each fresh left cell: copies of the word at the left and the size of the rest |
| `c/m7z.c` | the reduced simulation of Z (copies of the word deleted) with Brent's cycle check |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC/lean/check.sh
cd holdouts/1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC/c
gcc -O2 -o longrun longrun.c && ./longrun 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC 100000000000      # about 20 minutes
gcc -O2 -o runhist runhist.c && ./runhist 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC 10000000000
gcc -O2 -o trfreq trfreq.c && ./trfreq 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC 100000000
gcc -O2 -o ctx ctx.c && ./ctx 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC 2000000000 A 1 2
gcc -O2 -o zrec zrec.c && ./zrec 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC 30000000000 A 1101101101 | tail
gcc -O2 -o m7z m7z.c && ./m7z 770000000 6 10000000      # about 2 hours
```
