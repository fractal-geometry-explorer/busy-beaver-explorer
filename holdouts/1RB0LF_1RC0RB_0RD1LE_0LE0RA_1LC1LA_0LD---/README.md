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

## Family screen (F09, 13 November 2026)

The 22 machines of family F09 were screened in one way, to decide which family each belongs to. `holdouts/1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---/screen/screen.py`
runs the machine from blank tape for 2·10^10 steps and, at the first new leftmost and rightmost cell after each
threshold 10^6·4^k, compresses the tape twice: repeats of a word of at most 40 cells (level 1), then repeats of
groups of such tokens (level 2). A bounded description keeps the number of level-2 tokens bounded while the tape
grows. The long runs use the macro simulator `holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c`, sampled at one record per leading digit of the step count.
Everything in this section is observed in one run; none of it is proved.

| record | step | visited cells | cells in no repeat | repeats | level-2 tokens | largest repeat / tape |
|---|---|---|---|---|---|---|
| left | 256,078,994 | 31,354 | 1,146 | 1,293 | 1,033 | 0.02 |
| right | 257,242,630 | 31,402 | 1,802 | 1,109 | 1,487 | 0.02 |
| left | 1,024,512,387 | 66,114 | 2,273 | 2,510 | 2,005 | 0.03 |
| right | 1,025,093,207 | 66,126 | 3,533 | 2,212 | 2,878 | 0.03 |
| right | 4,096,370,281 | 114,470 | 6,324 | 4,222 | 4,033 | 0.02 |
| left | 4,096,738,189 | 114,479 | 4,142 | 4,821 | 2,772 | 0.02 |
| left | 16,385,265,339 | 195,502 | 8,556 | 10,085 | 2,817 | 0.01 |
| right | 16,389,344,111 | 195,526 | 12,747 | 8,616 | 4,135 | 0.01 |

**Proposed family: F06, block-list counters** (a periodic block of long period, a frozen list of growing runs and a list of counters at the right).

With repeats of single words only, the number of pieces is proportional to the tape (18,641 level-1 tokens for 195,502 cells at 1.6·10^10 steps). Most of them are one block of long period: `[(0100)^13 (0111)^10 (0100)^4 (0111)^13 (0100)^10 (0111)^4]^N` with N = 69 at 4.1·10^9 steps and N = 363 at 1.6·10^10 (left-end records; a period of 216 cells). With such groups counted once, the left-end records have 2,772 and 2,817 level-2 tokens at 4.1·10^9 and 1.6·10^10 steps and the right-end records 4,033 and 4,135: the rest of the tape hardly grows over a factor of 4 in steps.

Right of the block the tape is a frozen list of runs of growing lengths (10, 37, 16, 28, 19, 34, … up to 202) and then a list of units `(1110)^a (1000)^3 111 (0100)^b (0111)^3 01 000` with a and b between 3 and 42. The table is that of 1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC--- with the states renamed (`related.json`), from another start; that machine shows the same period-216 word with other counts. The two runs are different and nothing is claimed about one from the other.

A list of units that changes slowly while a periodic block grows behind it is read here as a list of counters: F06. The round rule is not known.

Next step: The rule of one unit `(a, b)` of the right-hand list, and what turns a unit into a piece of the frozen list.

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

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---`](../1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B

<!-- end of related machines -->
