# 1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---

bbchallenge id 116343. One of the six-state holdouts whose halting from blank tape is open. Group G07
(fixed/sqrt growth), family **nested run counter, x10/3 per epoch**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 0LE |
| C | 1RD | 0LB |
| D | 0RA | 1RC |
| E | 0RC | 0RF |
| F | 1RA | --- |

## Status

Open; conjectured not to halt. Every rule found below continues without halting, and an accelerated simulation
built on them runs 8,000 epochs (about 10^8021 steps) from blank tape without a halt. What is missing for a proof
is a complete, closed set of rules: one recursive case (an active run of 2 directly after a run of 2) is not
written out in general.

## What it does

Read the tape, at the moments the head is in state A just right of the last written cell, as a list of **runs of
1s separated by single 0s** (two adjacent 0s are an *empty run*, of length 0). A run of length 1 is a *unit*;
`u^k` is k units in a row. The tape is then always

    ... runs ...  [a]  u^B   A>

with one long *active* run `a` followed by B units. Everything happens at the right end:

* **cycle** (`cycle` in `lean/Rules.lean`, 6B+39 steps): the head walks left over the units to the active run,
  takes 3 cells from it and comes back writing 5 more units: `[a+3] u^B  ->  [a] u^(B+5)`.
* The cycles repeat until the active run has 0, 1 or 2 cells left: an *epoch* ends, and what happens next depends
  on `a mod 3`, and on the run to the left of the active one:
  * **a = 1**: the active run is now a unit itself; the active run becomes the next run to the left (the units
    merge). Its own cycles start.
  * **a = 0** (two adjacent 0s): the run on the left gives up one cell (`q0_unit`: a unit disappears; `q0_long`:
    a long run shrinks by 1 and merges with the new run), and the B units are filled into one new run of 2B+11.
  * **a = 2** after a long run `x+3` (`q2_long`): that run loses 3, 7 units join the units before the 2, and the B
    units become a new run of 2B-1. After an empty run or blank tape (`q2_zero`, `q2_blank`): the m units before
    the 2 become a run of 2m+4 (2m+6 after an empty run), then 6 units, then a new run of 2B-5.
  * only units, blank on the left (`units_blank`): they become one run of 2B+11.

Since B grows by 5 for every 3 cells taken from the active run, the new run is about 2·(5/3)·a = **(10/3)·a**: each
epoch multiplies the tape by about 10/3 and the step count by about (10/3)^2, which is why the tape grows like
the square root of the step count. Which branch is taken is decided by `a mod 3`, a residue of a number that is
roughly multiplied by 10/3 every epoch, so the branches come in a pseudo-random order (in 8,000 epochs: 2,634
times 0, 2,629 times 1, 2,737 times 2). The runs left of the active one form a short second-level counter that the
branches decrement, refill and occasionally merge away; in 8,000 epochs it never held more than one long run and
one block of units, and its long run never exceeded 32.

The first epochs (`python3 py/epochs.py 16`):

    epoch     3  step          21645  runs: 4 u^6 [338] u^3      (active run mod 3 = 2)
    epoch     4  step         216882  runs: u^14 [1122] u^3      (active run mod 3 = 0)
    epoch     5  step        2338267  runs: u^13 [3753] u^3      (active run mod 3 = 0)
    epoch     6  step       25890901  runs: u^12 [12523] u^3     (active run mod 3 = 1)
    epoch     7  step      287483938  runs:  [41778] u^3         (active run mod 3 = 0)
    ...
    epoch    14  step       [~10^15]  runs: 32 u^4 [191048923] u^3   (active run mod 3 = 1)
    epoch    15  step       [~10^16]  runs:  [32] u^318414878        (the run 32 becomes active)

## Where it could halt

The only halting transition is F reading 1. F is entered only from E reading 1 (`0RF`), and E from A reading 1
(`1RE`) or B reading 1 (`0LE`, moving left: then F reads the 0 that B just wrote). So a halt needs A moving right
onto `1 1 1`: A entering a run of three or more 1s from the left. In the rules above A moving right meets only
units and, in the a = 2 rules, the run of 2 itself (`A> 1 1 0`: E reads 1, F reads 0); the three near misses of the
first 10^9 steps (steps 97, 21,273 and 215,726) are of that kind. Each rule is a theorem that the stated number of
steps runs without a halt, so none of them halts. Window-based closed tape languages (`bbtools.ctl`, K up to 6; K = 8 does not
close) cannot rule this out: the invariant needs counting.

## Evidence and proofs

* `lean/Rules.lean` (kernel): the cycle rule and the epoch-end rules listed above, each for all values of its
  parameters, generated from symbolic traces by `py/rules.py` (shift rules `cross_l`/`cross_r`, `rfl`, `omega`).
* `py/epochs.py` (trusted): an exact accelerated simulator, `py/fastsim.py` (run-length tape, shift rules of
  `bbtools.symtm`, words re-cut when a shift rule needs a multiple) with the proved cycle rule applied k times at
  once (`k(6B+39) + 15k(k-1)` steps). `python3 py/epochs.py 12 check` compares the whole tape at the start of each of
  the first 8 epochs (up to step 3,197,349,547) with the C simulator: identical. 8,000 epochs take 18 s and reach
  about 10^8021 steps without a halt.

## What is open, and next steps

The rules above cover every epoch end that has occurred, but not every one the rewriting can produce: an active
run of 2 whose left neighbour is a run of 2 (`2 u^p 2`) recurses further left, its result depends on p (for p >= 3
roughly `y u^s 2 u^p 2 u^B -> (y-3) u^(s+7) (2p-6) u^6 (2B-8)`), and an empty run next to an empty run was not
seen. With adversarial residues the second-level counter can grow without bound (a breadth-first closure of the
prefixes with all three residues allowed does not terminate), so a proof cannot just enumerate prefixes; it needs
either the general recursive rule for any run list, or an argument that the residues needed to grow the prefix
never occur. A complete rule set for arbitrary run lists, proved symbolically, would give a non-halting proof
(no rule halts). Heuristically the machine never halts: no epoch end of any kind that was tried (including 400 random
run lists tried as epoch ends) halts.

## Pages

- [`pages/holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/explainer.html`](../../pages/holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/explainer.html)
- [`pages/holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/proof-status.html`](../../pages/holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/lean/check.sh
python3 holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/py/epochs.py 12 check   # accelerated run vs C
python3 holdouts/1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---/py/rules.py > /tmp/Rules.lean   # regenerate the rules
```
