# 1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---

bbchallenge id 58362. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0LE |
| C | 1RA | 0LB |
| D | 1RA | 1RF |
| E | 0RA | 0RC |
| F | 1RE | --- |

## What it does

At each visit of the right end in state D the tape is `Q 0 1^x (01)^y 1 D>0`: a short prefix `Q`, a block of `x`
ones and `y` pairs `01`. One **cycle** (head to the block and back) eats three ones and writes four pairs:

    1^(x+3) (01)^y 1 D>0  ->  1^x (01)^(y+4) 1 D>0        in 6y + 39 steps        (lean/Cycle.lean, all x, y)

A **phase** starts at `Q 0 1^m (01)^5 1 D>0` and runs `k = m div 3` cycles. Then the `r = m mod 3` leftover ones, the
prefix and the long run of pairs are rebuilt into the next phase start `Q' 0 1^m' (01)^5 1 D>0` with

    m' = 8k + c(Q, r),    Q' = Q'(Q, r),    steps = 12k^2 + B(Q, r) k + C(Q, r).

For the empty prefix: r = 0 -> (empty, 8k+12), r = 1 -> (empty, 8k+14), r = 2 -> (`1^6`, 8k+8). The prefix has the
shape `1^a (01)^b` of the main tape and behaves like a smaller copy of it (r = 2 turns three of its ones into two
pairs, r = 0 removes a pair, r = 1 usually runs its own phase and empties it); some cases nest a third level
(`1^6 0 1^4`, ...). So the machine is a **Collatz-like map with growth 8/3 and a nested prefix counter**.

Phases from blank tape (`py/phasemap.py`; the start steps of phases 1-9 are identical to a direct C run):

| phase | start step | Q | m | m mod 3 |
|---|---|---|---|---|
| 0 | 576 | empty | 38 | 2 |
| 1 | 3,291 | `1^6` | 104 | 2 |
| 2 | 19,764 | `1^3 (01)^2` | 284 | 2 |
| 3 | 132,789 | `1 (01)^3` | 764 | 2 |
| 4 | 925,650 | `1^14` | 2,040 | 0 |
| 5 | 6,524,191 | empty | 5,466 | 0 |
| 6 | 46,493,506 | empty | 14,588 | 2 |
| 7 | 330,517,071 | `1^6` | 38,904 | 0 |
| 8 | 2,349,492,124 | empty | 103,762 | 1 |
| 9 | 16,707,143,908 | empty | 276,710 | 2 |

## Status

Open.

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`); `cycle` (`lean/Cycle.lean`). **native_decide:**
  `blank_runs_native` (10^7 steps).
- **Computed (trusted):** the phase map. `py/phasemap.py` runs the machine from a phase start for four block sizes
  per (Q, r) case and fits m' and the step count (exact on all four); the fitted map reproduces the direct C run
  (`tools/c/tmrun.c`) through phase 9, step 16,707,143,908.
- **Heuristic:** iterated 3,000 phases (about 10^2557 steps) the map meets 68 cases and none halts; the 120 prefixes
  nearest the empty one (breadth first) have no halting case. The halting transition is F1, reached only as `D>1 1`.
- **Open:** the cases are fitted, not proved, and there are infinitely many (the prefix can grow).

## Next steps

Prove the phase-end rules in Lean with `bbtools.symtm.prove` for a parametric prefix `1^a (01)^b` (they are linear in
k), which would make the map exact; then look for an invariant of the prefix that rules out the halting pattern
`D>1 1`, or a halting case deep in the prefix tree.

## Pages

- [`pages/holdouts/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---/explainer.html`](../../pages/holdouts/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`](../1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA/README.md): rename A→C, B→D, C→E, D→F, E→B, F→A; it is this table started in state F
- [`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`](../1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---`](../1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---/README.md): rename A→B, B→C, C→A, D→E, E→D, F→F; it is this table started in state C

<!-- end of related machines -->
