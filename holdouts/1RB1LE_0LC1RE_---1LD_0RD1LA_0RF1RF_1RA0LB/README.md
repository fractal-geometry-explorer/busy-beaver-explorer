# 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB

bbchallenge id 23376. A BB(6) holdout whose halting from blank tape is open (group G07).
Family: **geometric block ladder with resets (a recursion on pair words)**. Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 0LC | 1RE |
| C | --- | 1LD |
| D | 0RD | 1LA |
| E | 0RF | 1RF |
| F | 1RA | 0LB |

## What it does

**Pairs, read from the growing end.** A *visit* is the head in A on the blank cell right of the tape. Read the tape
from the head leftwards in pairs of cells and write X for the pair `0 1`, Y for `1 1` (the word `Y Y X` is the
tape `... 0 1 1 1 1 1 A>`). At a visit the tape is such a word, down to a short irregular stretch at the left end.
The right end is the growing end: **one pair per visit**. The next visit shows V(S):

    V(X U)          = Y Y U                bounce (8 steps)
    V(Y X U)        = X X Y U
    V(Y Y X X U)    = X Y^4 U
    V(Y Y Y S)      = X X Y V(S)           three Y's pass the visit on
    V(Y Y X Y Y S)  = X Y^4 V(S)           so does Y Y X Y Y

These five rules cover 724 of the first 1,012 visits (3·10^6 steps) and agree with the machine on all of them and
on 19,312 random words (`py/vmodel.py`). The words that start `Y Y X Y X` follow a second family of rules that is
not written down yet (`V(Y Y X Y X T) = X Y^3 X H(T)`, with for example `H(X X X U) = Y^4 U`, `H(Y^3 X U) = Y^5 U`,
`H(X Y X U) = X Y^3 U`). Whole visits are **proved in Lean** for three families, for every j and every tape to
the left (`lean/Rules.lean`): `V(Y^(3j+1) X U) = X X (Y X X)^j Y U`, `V(Y^(3j+3) X U) = X X (Y X X)^j Y^3 U`,
`V(Y^(3j+2) X X U) = ... X Y^4 U`, in 28 j + const steps.

**The ladder.** In cells, `Y^4 X` (read leftwards) is the block `1^9 0`, and most of the tape is this block,
repeated in *rungs* separated by short digit words. In run lengths (all 0s single, `9*k` = k runs of 9):

    11201 visits, step 232,867,207:
    1^10 0 1 0 1^3 0 1 0 ... (1^7 0 1 0)^n  15 9 3 1 13 1 9*2 21 9*6 21 9*19 3 1 11 9*53 3 1 3 1 9*144 3 15 9*384 3 7 1 9*1024 7 1  A>

Rung lengths grow by a factor of about 8/3 from left to right (2, 6, 19, 53, 144, 384, 1024); the last rung gains
one block every 8 visits. The digit words between rungs change like the digits of a counter: the rules above are
its carries (a visit is passed on to the left through `Y Y Y` and `Y Y X Y Y`, and stops at the first of the three
turning words).

**Left-end events and the reset.** A visit that is passed on all the way reaches the left end of the tape. In the
first 3·10^9 steps the head came to the left end at steps 1,781 and 27,158,888 (after the first 2,000 steps: once). The second
time is the **reset** found by the earlier pass: at step 27,167,335 one sweep rewrites the left part block for block
(each `1^9 0` becomes `1^7 0 1 0`, the digit words become `1^3 0 1 0`, `1^11 0 1 0`, ...); that part then stays
frozen, and a new ladder builds up to its right (7 rungs at 2.4·10^8 steps).

**Where it can halt.** Only C reading 0, and C comes from B reading 0 and stepping left: the machine halts exactly
when **B reads a 0 that has a 0 on its left**. Inside the tape all 0s are single, so this means B arriving at the
blank left edge. Closed tape languages (windows 4, 6, 8) confirm it: the halt is only allowed at the left end,
blank to the left. A visit that runs into the left edge can halt: on the tape `0^inf 0 1 1 1 1 1 A>` (the word
`Y Y X`) it does, after 17 steps (Lean: `edge_halts`); at the two left-end events of the run the head arrived in E
and in D, not in B. So the question is in which state the rare visits that cross the whole tape arrive.

## Status

* **Lean (kernel)**, `lean/Rules.lean` (written by `py/rules.py`): `bounce`, `fam1_0`, `fam1`, `fam0_0`, `fam0`,
  `fam2_0`, `fam2` (whole visits, every j, every tape to the left), and `edge_halts`.
* **Lean**: `lean/Blank.lean`: the halting configurations; no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* **Trusted**: `py/vmodel.py`: the five rules against the machine. `py/blocksim.py` / `py/bscheck.py`: an exact
  simulator on repeats of `1111111010`, equal to the C simulator at every visit up to 3·10^7 steps; `py/runs.py`
  prints the ladder.
* **Trusted**: no halt in 3·10^9 steps (direct C simulation); the CTL confinement to the left end.
* **Open**: the second family of rules (`Y Y X Y X ...`), what a visit does at the left end, and whether B ever
  arrives there.

## Next steps

* Complete the recursion: derive H (the words `Y Y X Y X T`) from the machine, as was done for V; then the ladder
  and its 8/3 ratio should follow as for the base-4 twins (`1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA`).
* List the ways a visit can arrive at the left end (state and the pairs next to the edge), and which of them the
  reset leaves possible for the next arrival: a halt needs B on the edge.
* A mirrored CTL certificate would make the left-end confinement a Lean theorem.

## Deep exact run

No halt in the first 6.00x10^19 steps: the macro simulator `holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c` with blocks of 10 cells ran
from blank tape to step 60,000,783,412,981,265,560. It is exact, and at this block size it agrees with the
direct simulator after 2,000,002,519 steps (`python3 holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/deep.py run 240`, then `verify`).

## Pages

- [`pages/holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/explainer.html`](../../pages/holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/explainer.html)
- [`pages/holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/proof-status.html`](../../pages/holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/lean/check.sh
cd holdouts/1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB/py
python3 rules.py > ../lean/Rules.lean                          # regenerate the Lean rules
python3 vmodel.py 3000000                                      # the recursion against the machine
gcc -O2 -o tmrun ../../../tools/c/tmrun.c && TMRUN=./tmrun python3 bscheck.py 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB 1111111010 A R 30000000
python3 runs.py 600 400 300                                    # the ladder at every 400th visit
cd ../../../tools/py && python3 -m bbtools.ctl 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB 8
```
