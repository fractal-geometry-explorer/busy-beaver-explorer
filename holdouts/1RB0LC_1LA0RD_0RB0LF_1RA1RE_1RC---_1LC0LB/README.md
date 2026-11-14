# 1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB

bbchallenge id 102105. Halting from blank tape is open. The tape is a staircase of runs of `001` separated by `0001`, rewritten by whole-tape sweeps.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1LA | 0RD |
| C | 0RB | 0LF |
| D | 1RA | 1RE |
| E | 1RC | --- |
| F | 1LC | 0LB |

## What it does

With `a = 0001` and `b = 001`, at left extensions the tape is `C> b a^m b^x1 a b^x2 a ... a b^xk`. Run lengths at
step 5,543,681,176 (`.` marks an `a^2`):

    4 2 2 . 2 4 2 4 2 16 6 6 6 6 6 6 6 6 6 6 6 4 10 10 10 10 10 8 10 12 12 12 12 10 12 10 28 16 16 16 16 16 20 18 ...

rising across the tape in plateaus up to above 120, each plateau usually ending with an outlier. The sweeps
complement the words they cross (`001` <-> `110` and others; these are the Lean rules). The width grows like
1.16·sqrt(t) (31,604 at step 7.39·10^8, 86,428 at 5.54·10^9).

## What is proved

- Lean, kernel (`lean/Rules.lean`, from `py/rules.py`): the sweep rules

    L D> (001)^n R -> L (110)^n D> R
    L A> (010)^n R -> L (101)^n A> R
    L B> (100)^n R -> L (011)^n B> R
    L 0 D> (1011011)^n R -> L (1011011)^n 0 D> R
    L B> (1101101)^n R -> L (1011011)^n B> R
    L C> (0010)^n R -> L (1011)^n C> R
    L 0 B> (0100)^n R -> L (1011)^n 0 B> R
    L (1011)^n A> 1 R -> L A> 1 (1000)^n R

- Lean (`lean/Blank.lean`, generated): the halting configurations, no halt in 10^4 / 10^7 steps.

Everything under "What it does" is observation from simulation, not proof.

## Open

Halting. The rule by which a sweep changes the run lengths is not known.

## For later

- Follow one full sweep at the level of the run lengths and write the update as a map on the list.

## Reproduce

```sh
tools/c/tokrun 1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB 6000000000 a=0001,b=001 L 100000
python3 holdouts/1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB/py/rules.py > holdouts/1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB/lean/Rules.lean
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB/lean/check.sh
```

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 1.43x10^9 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 4 checkpoints, the last at 10^9 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 58 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB 400
```

## Pages

- [`pages/holdouts/1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB/explainer.html`](../../pages/holdouts/1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB/explainer.html)
- [`pages/holdouts/1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB/proof-status.html`](../../pages/holdouts/1RB0LC_1LA0RD_0RB0LF_1RA1RE_1RC---_1LC0LB/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC`](../1RB---_0RC0LF_1LD0RE_1RC0LB_1RD1RA_1LB0LC/README.md): rename A→D, B→C, C→B, D→E, E→A, F→F; it is this table started in state E
- [`1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---`](../1RB0LC_1LA0RD_1LB1LF_0LA0RE_1RD0RA_1LD---/README.md): rename A→B, B→A, C→D, D→C, E→F, F→E and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
