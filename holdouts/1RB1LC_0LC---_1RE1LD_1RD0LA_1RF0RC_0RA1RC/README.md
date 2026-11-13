# 1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC

bbchallenge id 103901. A bouncer on the left feeds a list of counters (01)^n separated by 1 1 1: at each new cell on the right, the j-th counter from the right loses exactly 2^j, up to a point where the list is rebuilt; when the whole list pays, a new counter is born and the wall is 2^(k+3) - 3.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 0LC | --- |
| C | 1RE | 1LD |
| D | 1RD | 0LA |
| E | 1RF | 0RC |
| F | 0RA | 1RC |

## What it does

The left part `(10)^x` is a bouncer's wall that grows by one cell per sweep (the left side grows like √t). The rest
of the tape is a **list of counters**. Each time the visited part grows on the right (rarely: the right side grows
like t^0.15) the tape reads

    step 233,350,399:  (10)^2461 1^4 (01)^2693 1^3 (01)^3139 1^3 (01)^1283 1^3 (01)^339 1^3 (01)^5487
                       1^3 (01)^1363 1^3 (01)^2621 1^3 (01)^313 1^3 (01)^2778 1^3 (01)^377 101 B>0
    step 378,591,341:  (10)^8189 1^4 (01)^413 1^3 (01)^1669 1^3 (01)^2627 1^3 (01)^1027 1^3 (01)^211 1^3
                       (01)^5423 1^3 (01)^1331 1^3 (01)^2605 1^3 (01)^305 1^3 (01)^2774 1^3 (01)^375 101 B>0

From the right: 377 → 375 (−2), 2778 → 2774 (−4), 313 → 305 (−8), 2621 → 2605 (−16), 1363 → 1331 (−32),
5487 → 5423 (−64), 339 → 211 (−128), 1283 → 1027 (−256), 3139 → 2627 (−512), 2693 → 1669 (−1024), and a new
counter 413 is put at the front, while x became 8189 = 2¹³ − 3.

**The rate law** (measured on the 74 transitions between right extensions from step 8,225 to 2.5·10⁹): counter j
from the right loses exactly 2^j between two right extensions, for every j up to some point; beyond it the
counters are rebuilt (into a different number of counters). In 21 transitions every counter pays, and then always
a new counter appears in front and the wall `x` is 2^(k+3) − 3 (61, 125, 253, 509, 1021, 2045, 4093, 8189, 16381).
Where a rebuild starts is not yet understood: in 28 of the 53 rebuilds it is at the first counter (from the right)
smaller than its rate, or at its right neighbour. A guess, not checked: between left
visits the defects (the `1^3` separators and the phase changes of `(01)`/`(10)`) travel through the background at
speeds that halve from one counter to the next, which would be where the powers of two come from.

In plain words: a binary counter laid out in space, whose j-th digit is a block that drains at rate 2^j, refilled
from the left by a bouncer.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the shift rules of the sweeps across the `(10)^n` / `(01)^n` blocks in states C, A and E (`shift_l_C_10`, `shift_r_C_01`, `shift_l_A_01`, `shift_r_E_10`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The rate law (counter j loses 2^j per right extension) and the rebuilding of the counters
that cannot pay are measured, not proved. Halting needs A reading 0 with a 1 to its right (A0 → 1RB, then B1
halts).

## For later

More than a day. Next: (1) prove the one-sweep rules between two left visits with `symtm.prove` (the shift
rules are in `lean/Rules.lean`), so the rate law becomes a theorem for the counters that can pay; (2) collect
the rebuild events (the list printed by the right-extension samples) and fit the map on the leftmost counters;
(3) look at the counters in binary: the law says the list is a counter whose digits have weights 2^j, so the
rebuild should be a carry.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC/lean/check.sh
python3 holdouts/1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Deep exact run

No halt in the first 5.93x10^18 steps: the macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with blocks of 6 cells ran
from blank tape to step 5,931,313,351,842,280,547. It is exact, and at this block size it agrees with the
direct simulator after 2,000,038,489 steps (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/deep.py run 240`, then `verify`).

## Pages

- [`pages/holdouts/1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC/explainer.html`](../../pages/holdouts/1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC/explainer.html)
- [`pages/holdouts/1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC/proof-status.html`](../../pages/holdouts/1RB1LC_0LC---_1RE1LD_1RD0LA_1RF0RC_0RA1RC/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC`](../1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC/README.md): rename A→C, B→D, C→E, D→F, E→A, F→B; it is this table started in state E
- [`1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD`](../1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD/README.md): rename A→D, B→E, C→A, D→F, E→B, F→C; it is this table started in state C

<!-- end of related machines -->
