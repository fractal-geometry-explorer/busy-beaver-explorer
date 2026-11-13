# 1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC

bbchallenge id 5380. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **bouncer with a multi-digit counter of 10 blocks (chaotic)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1LC | --- |
| C | 1RE | 0LD |
| D | 1LC | 1LD |
| E | 1RF | 0RE |
| F | 1RA | 0RC |

## What it does

Read from the left end, the tape is blocks of `a = 10` separated by separators such as `b = 110`, `0`, `1 1 b`. The separators near the left end change at each sweep and carry rightward like counter digits; the first block grows by about one `a` per sweep. The left end grows by 2 cells per sweep; the right end moved out 579 times in 10^9 steps.

```
the tape at the left end every 6·10^7 steps (a = 10, b = 110):
step 660,503,926  C b^2 a^4 0 a^6668 0 a^4 0 a^2 0 a^1681 b a^5 b a^12 b a^9 b a^3161 ...
step 720,557,246  C b^2 a^3 b a^6964 1^2 b a^2 1^2 b a 0 a^1755 b a^5 b a^12 b a^10 0 a^3197 ...
step 780,753,976  C b^2 a^3 b a^7249 b a^3 b^2 a^1828 0 a^4 0 a^14 0 a^9 b a^3233 ...
```

## Halting

The only halting transition is B1. `bbtools.ctl` finds closed tape languages (windows of 2 to 6 cells) that cover the run but still allow halts, with only a local constraint near the head: at K = 6 the cells left of the head read (outward) `111000`, `111001`, `111010` or `111101`.

## Status

**Open.** Lean: only the generated `lean/Blank.lean` (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by `native_decide`).
Deciders tried without success: `bbtools.ctl` with windows K = 2..6 (no closed language without halts), `ngramcps`
with widths 2..6, plain and with `-H 2`, `-H 3`, `-U`.

## For later

- As for 1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA: write the separator cycle and carries as a counter and check it.

## Pages

- [`pages/holdouts/1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC/explainer.html`](../../pages/holdouts/1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC/explainer.html)
- [`pages/holdouts/1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC/proof-status.html`](../../pages/holdouts/1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF`](../1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF/README.md): rename A→B, B→C, C→D, D→E, E→F, F→A; it is this table started in state F

<!-- end of related machines -->
