# 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF

bbchallenge id 99431. Both sides grow by sweeps; the tape is an irregular list with one long periodic block inside it (the word 1^7 00 1 00 repeated, 3,766 times at 8.8·10^8 steps) that grows steadily.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0RD |
| C | 1LD | 1LB |
| D | 1LE | 0LF |
| E | 0RA | --- |
| F | 0LB | 1LF |

## What it does

Both sides grow (left like t^0.66, right like √t). At the left end the tape is a list of runs of 1s of length
3a + 1 separated by `00`, with one long **periodic block** in it:

    step 882,788,555:  E>0 1^17 0010 1^3 0 (01)^3 1^4 00 1^5 (001)^4 1^8 (001)^3 1^6 00 1^11 …
                       … (001111111001)^3766 00 (10011)^3 1^3 (001111100111)^5 00 …

(7,550 of the 7,582 runs of 1s have length 3a + 1; 7,574 of the 7,581 runs of 0s have length 2.) The block
`(001111111001)^3766` is the pair of runs 1^7, 1^1 repeated. At the right end (step 999,852,606) the same block is
written `(011011101011)^2687 … (01)^1608`. Outside the block the list is irregular.

In plain words: a sweeping machine that rewrites a list of numbers each time, in which one long regular stretch
keeps growing while the rest churns.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the shift rules of the leftward sweep in B across `(01)^n` and `(011)^n` (`shift_l_B_01`, `shift_l_B_011`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The periodic block and the codes are measured; the irregular part is not understood.
Halting needs D reading 0 with a 1 to its left.

## For later

More than a day. Next: (1) follow the periodic block over time (how many copies per left visit) and prove the
sweep across it with `symtm.prove`; (2) look at the irregular part as a list of numbers (runs 1^(3a+1)) and test
whether the sweep acts on it as a finite transducer.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/lean/check.sh
python3 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Pages

- [`pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/explainer.html`](../../pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF`](../1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F and exchange left and right; it is this table started in state C, in a mirror
- [`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF`](../1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF`](../1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
