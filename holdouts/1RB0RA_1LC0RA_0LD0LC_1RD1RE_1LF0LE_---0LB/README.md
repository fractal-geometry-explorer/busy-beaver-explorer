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

## The same machine as 1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF

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

## Pages

- [`pages/holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/explainer.html`](../../pages/holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/explainer.html)
- [`pages/holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/proof-status.html`](../../pages/holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB/lean/check.sh
```
