# 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---

bbchallenge id 127983. One of the six-state holdouts whose halting from blank tape is open. **It runs a layered
counter: a growing prefix `(110)^k` is turned, at each reset, into a sorted list of groups of sizes 4, 7, 10, 13, …
with large multiplicities, which the following sweeps use up one group at a time.** The rule of a round is not
found; this folder records the structure seen so far.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0RE |
| C | 1LD | 1LC |
| D | 1RA | 0LB |
| E | 0RD | 0RF |
| F | 0LC | --- |

## What it does (observed)

The tape grows to the left (like the square root of the step count); its right end hardly moves. At each visit of
the left end in state B the tape reads

    B> 00 (110)^k  (10)^a₁ 1 (10)^a₂ 1 (10)^a₃ 1 …

so it is a prefix of `k` words `110`, then a list of group sizes `a₁ a₂ …`. Between resets the prefix grows by 2 at
each visit, and the sweeps use up the list from the left: a group followed by two groups of size 1 is merged into a
larger one, so the list turns into runs of equal sizes on the grid 4, 7, 10, 13, 16, 19, … (at step 2.8·10⁸,
written run-length coded: `2 4^140 3 1 7^514 10^28 13^105 16^3 15 1 4 19^21 18 22 25^3 23 1^2 29 1^2 33 2 1^2 4`).
When the prefix is no longer needed it is turned into groups, about `k/2` groups of size 4, and a new round starts
(`c/resets.py` prints these resets). Large and small resets alternate:

    step          k      list after the reset (run-length coded, start)
    36,031,105    909    1 4^454 3 1 7^7 10^89 12 13^3 16^17 18 1 22^2 …
    36,550,531    37     2 3 4^18 6 7^17 5 1 5 1^2 5 1^2 …
    136,979,965   1670   2 3 4^835 7^38 6 1 10^170 9 13^5 16^35 15 1 20 …
    143,004,220   220    2 3 4^110 7^108 5 1 5 1^2 5 1^2 …
    336,918,693   2591   1 1 4^1295 3 1 7^70 6 10^257 13^14 16^53 19 18 5 …
    354,166,720   397    1 1 4^198 3 1 7^197 5 1 5 1^2 …
    528,837,280   3185   2 3 4^1592 6 7^98 6 1 4 10^323 9 7 13^16 12 1 4 16^60 14 …

The large values of `k` grow by a factor of about 1.2 per large reset, and the steps between them by about 1.5. So
the machine is a counter with several levels, the multiplicities of 4, 7, 10, 13, 16 being its digits; how they carry
is not worked out.

## Does it halt?

Open. Proved (Lean): only the generated facts in `lean/Blank.lean` (the halting configurations; no halt in 10⁷
steps). Computed: no halt in 10⁹ steps (`tools/c/triage.c`), and the resets above (`c/sim.c`, to 6·10⁸ steps). The
machine halts only if state F reads a 1; without the round rule, where that could happen is not known and no
heuristic is given.

## For later

More than a day of work remains. (1) Prove the sweep that merges a group with two groups of size 1 (`a 1 1 → a+…`)
and the growth of the prefix with `symtm`, for all sizes. (2) Write the reset as a map on the multiplicity vector
of the sizes 4, 7, 10, … and check it against `c/resets.py`. (3) Then decide whether that map can reach the
configuration where F reads a 1.

## Files

- `c/sim.c`: plain simulation from blank tape, printing the edge events.
- `c/resets.py`: reads `sim … 1` and prints the resets of the prefix with the list after them.

## Status

Open. The claims with what each rests on are in `status.json` and the proof-status page.

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 1.48x10^14 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.00x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 12,476 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC--- 400
```

## Pages

- [`pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---/explainer.html`](../../pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---/lean/check.sh
gcc -O2 -o sim holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---/c/sim.c && ./sim 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC--- 600000000 1 | python3 holdouts/1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---/c/resets.py   # about 8 min
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---`](../1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---`](../1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---/README.md): rename A→B, B→C, C→D, D→A, E→E, F→F; it is this table started in state D

<!-- end of related machines -->
