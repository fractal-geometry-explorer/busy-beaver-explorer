# 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA

bbchallenge id 9123. A BB(6) holdout whose halting from blank tape is open (group G07).
Family: **nested base-4 counter on pairs (a recursion on words)**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LF |
| B | 1LC | 1RB |
| C | 1LF | 1LD |
| D | 1LE | 0RD |
| E | 1LB | --- |
| F | 1LA | 0LA |

## What it does

**Pairs.** Cut the tape into pairs of cells and write `X = 10`, `Y = 11`, `O = 00`. A *wall visit* is the head in F
on a 0 with nothing but 0s to its left. At a wall visit the tape to the right of the head is a word S over X and Y
(`0^inf F> 0 S 0^inf`; in 3·10^6 steps, 1,39x of the wall visits are of this kind and follow the rule below, the others are the
visits around the right-end events). The wall is the growing end: it moves **one pair to the left at every
visit**; the right end of the tape stands still between right-end events.

**The rule.** The next wall visit shows V(S) = G(S), one pair longer, where

    G(Y^a X X U)     = X^a Y Y Y U                      the head turns back at the first double X
    G(Y^a X Y^k X U) = X^a Y G^k(Y Y U)     (k >= 1)    a "digit" k passes k visits on to the rest
    G(Y^a)           = X^a Y Y                          the head reaches the blank right end in B

In the machine: B runs right over Y's; at `Y B> X X` it turns (`<F Y Y Y`); at `Y B> X Y^k X` state D erases the
k Y's, the pair before them becomes blank too, and B and F fill two of the k + 1 blank pairs: `X O^(k-1) Y Y Y B>`.
F, coming back, swaps X and Y in every pair it crosses, and on a blank pair it turns round again (`O -> Y`, B to
the right). So each of the k - 1 blank pairs left behind is a wall for the rest of the tape: the rest gets k
visits before F goes home. `py/gmodel.py` checks the recursion against the machine (20,000 random words; every
covered wall visit of the run from blank tape).

**The counter.** Read S as digits (the lengths of the runs of Y between X's). Then `1 0` is the six-cell word
`111010`, and after the first few hundred steps the tape is

    wall | 3 or 000 | (1 0)^N1 | w1 ... (1 0)^N2 w2 ... (1 0)^N3 w3 ...

with digit words w that cycle through four phases, `0000000 -> 3 00000 -> 0000 3 -> 3 00 3 -> 0000000`. Two wall
visits make one phase (a *bounce* `000 -> 3`, 16 steps, then a crossing of the first block), the block gains one
`1 0` in the second and in the fourth phase, and the fourth phase sends the head on into the rest of the tape (the
carry). All of it is **proved in Lean** for every block length n and every tape R to the right
(`lean/Rules.lean`: `bounce`, `phase1`, `phase2`, `phase4_in`, `phase4_out`): one cycle of 8 wall visits takes

    000 (1 0)^n 0000000 R    to    000 (1 0)^(n+2) 0000000 R'

in 104 n + 407 steps plus the time the head spends in R, and R' is what one visit makes of R (in the recursion:
R' = G(X R)). So the rest of the tape lives the same life eight times slower, whatever the block length is: that
is why the block lengths fall by about 4 from level to level (after 10^9 steps: 5998, 1492, 372, 88, 21) and why
level k moves once every 4^(k-1) phases. Between two levels there may be a frozen stretch of other digits
(for example `4 1 0 0 1 0 0 0 0 0 1 0 1 0 4 3 1 0 4 0 3 0 0 0` between the first and second block); they pass the
visits on unchanged.

**Right-end events.** The recursion stops when the head reaches the blank right end in D (S ends in `X` or
`X Y^k`): this happens when the last level overflows, at steps 1,937; 57,942; 61,755; 63,313; 83,647; 125,133; 48,737,226 in the first 2·10^10
steps (`rightvis`-style count: the head back at the right end after more than 1,000 steps away). What happens
then is not regular: the head comes back in A or D, pairs change parity (`01` pairs appear), blank stretches are
left inside the tape.
The event at step 48,737,226 is a **reset**: 29,000 steps later (step 48,766,065) the head, coming back across
the first block (1,308 copies), has turned it into a single run `1^7855`, and a new counter grows from there (the
earlier pass followed it to 4.5·10^9 steps; pieces of the long run of 1s are still being worn down at 2·10^9).

**Where it can halt.** Only E reading 1. In the pair picture that needs a blank pair with `11` or `01` to its left
at the moment the head backs onto it from a blank cell, which the counter never produces; a right-end event can.
There are words of X and Y on which the wall visit halts: the shortest is `X Y^7 X X` (253 steps; Lean:
`pure_tape_halts`), and 8 (this machine) or 18 (the twin) of the 16,383 words of at most 13 pairs do. None of
them is a tape of the run from blank. So the pair structure alone cannot prove that the machine runs forever: the
answer depends on which words the right-end events leave behind, and those look irregular.

Near-twin: [`1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA`](../1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA/README.md): the same table with C, D, E wired differently. The recursion G, the four
phases and their step counts are the same for both; the right-end events differ.

## Status

* **Lean (kernel)**, `lean/Rules.lean` (written by `py/rules.py`), for every count and every surrounding tape:
  the pair moves `reflect`, `flipX0/1`, `flipY0/1`, `turn0/1`, `digit1`, `digit`; the wall moves `bounce`,
  `cross`; the counter phases `phase1`, `phase2`, `phase4_in`, `phase4_out`; and `pure_tape_halts`.
* **Lean**: `lean/Blank.lean`: the halting configurations; no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* **Trusted**: `py/gmodel.py`: V = G on random words and on the run from blank tape; `py/blocksim.py` /
  `py/bscheck.py` (the earlier exact simulator on runs of `111010`). Direct simulation (`tools/c/tmrun.c`): no halt
  in 2·10^10 steps.
* **Trusted**: a closed tape language from windows of 6 cells confines the halt to a head with only 0s on its left
  (`python3 -m bbtools.ctl 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA 6`).
* **Open**: what the right-end events do in general, and so whether a halting word ever appears.

## Next steps

* The carry is a visit of the rest (`R' = G(X R)`), so the whole run is the iteration of one map on words, and the
  levels only set the clock. An accelerator that strips the regular levels (each proved rule of the form
  "p visits turn P(n) T into P(n + c) T' with T' a visit of T") would reach the right-end events directly,
  exponentially faster than any step-by-step run; the frozen stretches between levels need the same kind of rule.
* Extend the recursion to the three ways a visit of the rest can come back (F, the regular one; A; D) and to tapes
  with `01` and blank pairs: that is the full macro machine, and the place to look for an invariant or for a halt.
* A mirrored CTL certificate (left and right swapped) would make the confinement a Lean theorem.

## Pages

- [`pages/holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/explainer.html`](../../pages/holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/explainer.html)
- [`pages/holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/proof-status.html`](../../pages/holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/lean/check.sh
cd holdouts/1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA/py && python3 rules.py > ../lean/Rules.lean   # regenerate the Lean rules
python3 gmodel.py 3000000                                      # the recursion against the machine
gcc -O2 -o tmrun ../../../tools/c/tmrun.c && TMRUN=./tmrun python3 bscheck.py 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA 111010 F L 2000000
cd ../../../tools/py && python3 -m bbtools.ctl 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA 6
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LA_1RC1RE_1RD0RD_1LA1RC_1RF0LE_1RA---`](../1RB1LA_1RC1RE_1RD0RD_1LA1RC_1RF0LE_1RA---/README.md): rename A→D, B→A, C→B, D→E, E→F, F→C and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
