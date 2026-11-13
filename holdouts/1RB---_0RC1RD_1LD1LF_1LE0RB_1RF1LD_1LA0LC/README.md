# 1RB---_0RC1RD_1LD1LF_1LE0RB_1RF1LD_1LA0LC

bbchallenge id 2968, group G08 (two-sided square-root growth). Whether it halts from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 0RC | 1RD |
| C | 1LD | 1LF |
| D | 1LE | 0RB |
| E | 1RF | 1LD |
| F | 1LA | 0LC |

## What it does

A chaotic two-sided bouncer. The head sweeps across the whole tape and back; the tape is blocks of 1s separated by
single 0s, and each sweep re-encodes the blocks it crosses:

- moving right, B and D turn each pair `1 1` into `1 0` (`B> 1 1 1 1` -> `1 0 1 0 B>`), so solid blocks become
  alternating stretches;
- moving left, F and C do the same to solid blocks (`1 1 1 1 F>1` -> `F>1 1 0 1 0`), while D and E fill alternating
  stretches back into solid 1s (`0 1 0 1 D>0` -> `D>0 1 1 1 1`);
- where the two kinds meet the head zig-zags for a few cells, and the block lengths change there.

The block lengths after a sweep are a fixed but complicated function of those before; they look random. At every
sweep end in the run every interior block of 1s is odd and every interior run of 0s has length 1.

## How it would halt

The only halting transition is A1. A is entered only from F0, so the machine halts exactly at `1 F>0` (F reads a 0
with a 1 on its left). F is entered from C1 and E0; the short ways in are `1 B>0 1` (B meets an isolated 0, halt 4
steps later) and `E>0 0` (halt 3 steps later). In the run F reads a 0 millions of times, but always with a 0 to its
left.

## What is established

- **Kernel** (`lean/Halt.lean`): `halt_A`, `halt_F`, `halt_B`, `halt_E` (each pattern halts, for any surrounding tape),
  `enter_A`, `enter_F` (the only ways into A and F).
- **Kernel** (`lean/Rules.lean`): the sweep rules `bsweep`, `fsweep`, `dfill`, `efill` for any n.
- **Kernel / native** (`lean/Blank.lean`): the halting configurations; no halt in 10^4 steps (kernel), 10^7 (native).
- **Trusted** (C): no halt in 10^11 steps (`c/longrun.c`); odd blocks and isolated 0s at every sweep end up to
  10<sup>9</sup> steps (`c/runhist.c`); F reads only paired 0s in 10^8 steps (`c/trfreq.c`).
- **Failed**: window CTL (K <= 7), n-gram CPS (`tools/c/ngramcps.c`): plain at widths 4, 6, 8, and with LRU history (`-U`) or fixed history 2 and 4
  (`-H`) at widths 3 to 9, all UNKNOWN or over the configuration limit; also `-U` at widths 10 and 12 and `-H 2` at width 10: UNKNOWN.

## Open, and next steps

The question is open. The natural route is a closed tape language built on the odd-block shape; it must also describe
the stretch between the pair of 0s that the leftward fill drags along and the head. Next: learn the language from the
run (the sides of the tape at every step, as a DFA by state merging) and check it with `TM/CTL.lean`; or find the
exact map on block lengths per sweep and look for a counter in it.

## Files

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | generated: the machine, bounded runs |
| `lean/Halt.lean` | how a halt comes about (kernel) |
| `lean/Rules.lean` | the sweep rules (kernel, written by `bbtools.symtm.prove`) |
| `c/longrun.c`, `c/runhist.c`, `c/trfreq.c` | long run, run-length histogram at sweep ends, transition counts |

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: C with 1 two left, 0 left, 1 under the head; E with 0 under the head, 0 right.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_0RC1RD_1LD1LF_1LE0RB_1RF1LD_1LA0LC/lean/check.sh
cd holdouts/1RB---_0RC1RD_1LD1LF_1LE0RB_1RF1LD_1LA0LC/c
gcc -O2 -o longrun longrun.c && ./longrun 1RB---_0RC1RD_1LD1LF_1LE0RB_1RF1LD_1LA0LC 100000000000
gcc -O2 -o runhist runhist.c && ./runhist 1RB---_0RC1RD_1LD1LF_1LE0RB_1RF1LD_1LA0LC 10000000000
```
