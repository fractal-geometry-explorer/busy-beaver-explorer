# 1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---

bbchallenge id 10642. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0LE |
| C | 1LD | 0LB |
| D | 0RB | 0RA |
| E | 1RD | 1LF |
| F | 0LC | --- |

## What it does

At each visit of the left end in state B the tape reads `0 (01)^a [junk] W^b [right part]` with `W` a 4-cell word
(`1100`, `1001` or `0011` according to the phase type). Within a phase a grows and b shrinks (about 10 cells of pairs
per 3 words); when b runs out the pairs are converted into the next block of about a/2 words and a restarts near 0.

Pair block at the end of each phase (direct run, to 3e8 steps): 90, 209, 207, 357, 385, 491, 819, 1389, 1457, 2464,
4140, 6945, 6971, 9749. Long phases multiply by about 1.4-1.7; short ones (209 -> 207, 6945 -> 6971) are a second phase
type. The right part of the tape (a run of 0s that grew from 46 to 687 cells, then words `(100)^3 (0110)^2 01`) is
read at each conversion and decides the type: a Collatz-like system not yet written exactly.

**The phase cycle, exactly.** Inside a phase the left end repeats with period 8 visits. For example (state B at the
left end; the right part `10010011000 (1001)^3 ...` unchanged):

    step 2,591,480   B> 0 (01)^694 10100 (1100)^206
    step 2,596,393   B> 0 (01)^697 100101 (1100)^205
    step 2,601,290   B> 0 (01)^700 101 (1100)^205
    step 2,606,257   B> 0 (01)^701 001001100101 (1100)^203
    ...              (four more visits, junk 00100110010010001, 001000110010010001, 1010100100010010100,
                      10010100)
    step 2,632,206   B> 0 (01)^724 10100 (1100)^197

so every 8 visits `(01)^a 10100 (1100)^(b+9) -> (01)^(a+30) 10100 (1100)^b` (checked over five consecutive periods,
a = 694 ... 844). Each visit the head carries a bubble of 1s through the pairs (`D0 -> 0RB`, `B1 -> 0LE`: it does not
cross a pair in one state, so `bbtools.symtm` finds no shift rule for it; a proof needs a macro step of 4 cells).

The halting transition is F1, reached only as B1 -> 0LE, E1 -> 1LF: B must meet `1 1 1` read leftwards; the phase type
`1^3 (0011)^b` contains such a run.

## Status

Open. Lean: `lean/Blank.lean`. C: no halt in 1e9 steps. The phase description is heuristic.

## Next steps

Prove the 8-visit cycle (blocks of 4 cells, or a hand-written symbolic rule for the bubble), pin down the two
phase types and the right part as a few counters, prove the within-phase cycle with
`bbtools.symtm.prove`, and derive the phase map (as was done for 1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---).

## Pages

- [`pages/holdouts/1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---/explainer.html`](../../pages/holdouts/1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---`](../1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---`](../1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---/README.md): rename A→E, B→C, C→A, D→B, E→D, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
