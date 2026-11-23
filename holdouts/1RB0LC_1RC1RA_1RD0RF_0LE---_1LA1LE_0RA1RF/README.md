# 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF

Group G08 (two-sided square-root growth). Whether it halts from blank tape is **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 1RA |
| C | 1RD | 0RF |
| D | 0LE | --- |
| E | 1LA | 1LE |
| F | 0RA | 1RF |

## What it does

Full sweeps over a row of periodic regions. With `c = 110`, `q = 010110101101010110101101` (24 cells) and
`s = 101010110110110` (15 cells), at the left-end turn of step 7,087,597 the tape is (`X = 10`)

    B> c^2 0 c^2 X c X c 1 q^40 0 X c X c X^2 c X^3 c^2 X c X s^36 X c^6 X s c X^5 s c X^16 s c X^38 c X c X^78
       c^2 0 c^2 X^157 1 c^3 ... (1 0 1 c^3)^many ... irregular right end

The runs of `10` roughly double in length (5, 16, 38, 78, 157). Counting copies at the left-end turns: the q-run
grows from 3 (step 561,704) to 111 (step 4,263,440) while the s-run shrinks from 50 to 7; by 4.7·10⁶ both are gone
and q starts again; from 5.9·10⁶ to 1.2·10⁷ an s-run of 35–36 copies sits still while q grows to 109 and the region
of `101110110110` further right shrinks. It looks like a counter whose digits are whole regions.

Passes (proved for any n): A moving right rewrites q (rotation `011010110101011010110101`) as
`100111001111100111001111`, 32 steps a copy (`pass_right_q`); C moving left restores it, 68 steps a copy
(`pass_left_q`); A turns each `011` into `100` (`pass_right_c`). These need `set_option maxRecDepth`.

The only halt is D reading a 1, and D is entered only from C reading a 0: `C> 0 1` halts (`halt_C`).

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10⁴ steps (kernel) and 10⁷ (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): `pass_right_q`, `pass_left_q`, `pass_right_c`; `halt_C`.
- `lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, every configuration two steps before a
  halt is `B> 0 0 1`.
- `lean/RSimBound.lean`, `lean/RSimLong.lean` (`native_decide`, the checked accelerated simulator
  `tools/lean/TM/RSim.lean`): no halt in 10^8 steps (`rsim_1e8`, part of `check.sh`, 45 s) and in 2·10^14 steps
  (`rsim_long`; `check_big.sh`, about 2 minutes). The simulator is rsim (`c/rsim_fast.cpp` of the T3 sibling) with
  every move proved: learned crossing rules are checked by a run of the machine before use, and each sample-level jump
  is checked by one symbolic period with the counts as linear forms. `RSimRun.lean` holds the run as a definition so
  that `check_big.sh` compiles it with the machine.
- `py/turns.py` (heuristic): the tape as words at the end turns.

## What is open, next steps

The round-trip rule on the row of regions (which region feeds which, and the rebuild when one runs out), then an
invariant from it that keeps D off a 1. The doubling runs of `10` suggest the digits of a binary-like counter.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/lean/check.sh
holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/lean/check_big.sh   # 2·10^14 steps, checked simulator, about 2 minutes
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/py/route.py        # rewrites lean/Route.lean
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/py/rules.py        # rewrites lean/Rules.lean
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF/py/turns.py 1.2e7 L  # the tape at the left-end turns
```

## Start B of a PR 93 neighbour table (22 November 2026)

This machine is the table of 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF started in state B, mirrored (see Related machines). With E and F of that machine
exchanged and its halting detour replaced by one step, the table is `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LE`, which is DeepMind's busycoq PR 93 table T3
with one transition (E1) changed. Of PR 93's 18 basic macro rules, 14 still hold; the four that pass through E1 change:
this table writes the digit D k followed by a stray 10 where T3 writes D (k+1), and a call that meets 10 10 runs on to the right end instead of returning. So PR 93's engine does not carry over to this table, from any start. Details, and Lean proofs of
the changed rules, are in [1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF](../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/README.md#pr-93s-engine-on-this-table-22-november-2026).

Run for a halt from this start: the accelerated simulator `rsim.py`, validated against direct simulation at 6 points up to 10^10 steps,
went 225,538,757,990,671 steps from blank tape in 20 minutes without a halt (82 jumps).
Its faster C++ port [`c/rsim_fast.cpp`](../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/c/rsim_fast.cpp) (same trajectory as
`rsim.py`; tape equal to direct simulation at 4 points up to 10^10) went **122,501,965,489,001,108,659 steps (1.2·10^20)**
in 3 hours without a halt (136 jumps, 1.8·10^10 rules; 22 November 2026). It reached 1.2·10^20 after 11 minutes; after
that no jump applied and the rest of the run crossed sweeps rule by rule. The jumps are validated, not proved.
The Lean rebuild of rsim (`lean/RSimLong.lean`) follows the same trajectory with the same jumps and proves the first
2·10^14 steps. From 2.25·10^14 to about 10^15 no long jump applies (a binary-counter-like row of `(01)^k` blocks whose
separators change on every sweep), and rsim crosses that stretch sweep by sweep in about 10 minutes before its jumps
cascade to 10^20; the Lean simulator is about 25 times slower there.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF 1200
g++ -O2 -std=c++17 -o rsim_fast holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/c/rsim_fast.cpp
DECADES=1 ./rsim_fast 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF run 10500 out.json
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF`](../1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B
- [`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF`](../1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF/README.md): rename A→D, B→E, C→A, D→B, E→C, F→F; it is this table started in state C
- [`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF`](../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror

<!-- end of related machines -->
