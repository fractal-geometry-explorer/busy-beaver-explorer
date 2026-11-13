# 1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---

bbchallenge id 26463. Group G01. **Quadrupling counter with nested lists** (one rule known): B> 000 (100)^a (010)^(b+2a+1) 01 → B> 000 (100)^(4a) (010)^b 01. Open. **Same table as 1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA--- with the states renamed** (another start state); the quadrupling round is now exact.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1LC | 0RD |
| C | 1LA | 0LC |
| D | 1RE | 0LB |
| E | 1RB | 1RF |
| F | 0LD | --- |

## What it does

At the moments when the head is in state B at the left end, the tape starts `B> 000 (100)^a (010)^b 01 …`
or `B> 000 (100)^a 1 (100)^c 1 …`. While b is large:

    B> 000 (100)^a (010)^(b+2a+1) 01  →  B> 000 (100)^(4a) (010)^b 01        (a = 5: 1,604 steps)

In the run: (100)^10 (010)^250 → (100)^40 (010)^229 → (100)^160 (010)^148 → (100)^171 1 (100)^298 1 → … →
(100)^5647 (010)^2686 01 (step 255,057,568). When b < 2a + 1 the outcome depends on b and on the blocks to the
right, and gives shapes like `(100)^x 1^2 (001)^y`, `(1001)^2 (001)^y`, `(100)^10 (0100100)^2 (100)^y`.

## Same table as 1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---

Renaming the states (A→E, B→C, C→D, D→A, E→B, F→F) turns this transition table into the one of `1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---`; only the start state differs.
So both holdouts are runs of one table from two different starts (two separate halting questions) and every rule below holds for both (tape words are unchanged; this
machine's state B is the other's C).

## The quadrupling round (exact)

With the head at the left end in state B reading `000`:

    B> 000 (100)^c (010)^(b+2c+1) X   →   B> 000 (100)^(4c) (010)^b X       in 60c² + 13c + 39 steps   (c ≥ 3)

for any tape X to the right (the round never reaches X). Checked by direct simulation for c = 3..39, b = 0..7 and
four tails X, 1,184 cases with their step counts (`../1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---/py/quadround.py`). In the run the counter
goes 10, 40, 160, 640, … until the block of `010`s cannot pay; the ending depends on the remainder and on the list
to the right and is not yet mapped.

## Third pass: the list form (see the twin)

This machine and 1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA--- are one transition table with two start states, and from blank tape
they reach the same list of runs: sampled at the left end reading `000` (here in state B), both runs give the same
events with the same step counts. Everything in `../1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---/README.md` therefore holds here: the
list rules (quad, flips, carries, restarts; 60,000 cases checked), the 46 events from blank tape to step 1.95·10¹¹,
all predicted by the rules, and the one known way to halt, [c 0, 2c+1 1, d …] → [4c 01, d …] → halt, an exact hit of
the second run (chance about (log b)/b per phase; probably non-halting, nothing proved).

The macro simulator (`python3 ../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/py/check_msim.py run 1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD--- 1e18`) runs 10¹⁸ steps from blank tape without a
halt. No pushdown certificate with a DFA of at most 6 states exists (checked for the twin; same table).

## What is proved

| level | result | where |
|---|---|---|
| kernel | halting configurations; no halt in 10⁴ steps (10⁷ by native_decide) | `lean/Blank.lean` |
| trusted | no halt in 10⁹ steps | `holdouts/triage.json` |
| trusted | the quadrupling round | `py/explore.py 5 30`, `py/explore.py 10 250` |
| trusted | the quadrupling round, exact, c ≥ 3 (1,184 cases) | `../1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---/py/quadround.py` (with `1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD--- B`) |
| trusted | the list rules and the halting rule (60,000 cases); the 46 events from blank tape | `../1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---/py/listmap.py check`, `blank` |
| trusted | no halt in 10¹⁸ steps | `../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/py/check_msim.py run` |
| open | the rules for odd runs below the front; halting | |

## Further work

See the twin: the general flip for every parity pattern, the halting chance made precise, and the quadrupling
round in Lean.

## Pages

- [`pages/holdouts/1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---/explainer.html`](../../pages/holdouts/1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---/explainer.html)
- [`pages/holdouts/1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---/proof-status.html`](../../pages/holdouts/1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---`](../1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---/README.md): rename A→E, B→C, C→D, D→A, E→B, F→F; it is this table started in state D

<!-- end of related machines -->
