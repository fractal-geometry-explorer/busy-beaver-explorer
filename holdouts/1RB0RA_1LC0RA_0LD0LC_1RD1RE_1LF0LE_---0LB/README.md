# 1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB

bbchallenge id 29825. A six-state holdout of group G05 (growth class fixed/sqrt). **Open.** It is
[1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF](../1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF/README.md) (bbchallenge
id 147837) in a mirror, started one step later, and its run is that machine's run with one extra 1 at the far wall;
the analysis is in that machine's folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1LC | 0RA |
| C | 0LD | 0LC |
| D | 1RD | 1RE |
| E | 1LF | 0LE |
| F | --- | 0LB |

## The same table as 1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF

Swap left and right and rename the states (this machine's A, B, C, D, E, F are the other machine's F, A, B, C, D, E):
the tables become identical. Only the start state differs: this machine starts in the other's state F. Its first
step (`A0 -> 1RB`, the other's `F0 -> 1LA` in the mirror) writes a 1 and enters the other's state A, so from step 1
on it runs the other machine from a tape holding one extra 1 next to the head.

That 1 rides along: `c/twin.c` runs the other machine from blank tape and from the tape with the extra 1, side by
side. At each of the 32,539 left-end records of the first 10^9 steps (the other machine's growing side is the left)
the two tapes agree except for one extra 1 at the end of the wall at the far end, and the step counts differ by 56
(constant since step 4,194,242, the last time the head reached the wall); with this machine's first step, 57. The
generated first look below agrees: its records come 57 steps after the other machine's, with one more 1 and one
more cell.

So everything said there holds here in the mirror: a sea of `1010` with a dozen particles pushed by a 2-bit gadget
like a counter with carries; a halt needs an **E-run** (E erasing 1s leftwards; Lean, kernel,
`halt_needs_erun` in `lean/Halt.lean`, the mirror of the other's `halt_needs_drun`), and E-runs have only happened
when a rare trip reached the wall. The two machines can only behave differently on such a trip, where this
machine's last wall block is one 1 longer.

## Status

Open. Lean: `halt_needs_erun` (kernel, `lean/Halt.lean`); the halting configurations (`step_none_iff`), no halt in
10,000 steps by the kernel, in 10,000,000 by `native_decide` (`lean/Blank.lean`). C: no halt in 10^9 steps
(`tools/c/triage.c`); the comparison with the other machine over 10^9 steps (`c/twin.c`, trusted). The cycle rules
and the long runs are in the other machine's folder.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/lean/check.sh
gcc -O2 -o twin holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/c/twin.c && ./twin 1000000000
```

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.0; right: sqrt,
exponent 0.516). After 1,000,000,000 steps: 65,135 cells visited (56 left of the
start, 49,806 right), 34,221 ones.

- right, step 973,442,783: `1^7 0 1^2 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 989,347,259: `1^7 0 1^2 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 14, history 1 up to width 13, history 2 up to width 9, history 3 up to width 10, LRU history up to width 2 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 12, p = 3 up to width 12, p = 4 up to width 12, p = 6 up to width 12.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: E with 0 two left, 0 left, 1 under the head.

## Pages

- [`pages/holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/explainer.html`](../../pages/holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/explainer.html)
- [`pages/holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/proof-status.html`](../../pages/holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF`](../1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF/README.md): rename A→F, B→A, C→B, D→C, E→D, F→E and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
