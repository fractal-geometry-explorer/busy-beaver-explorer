# 1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---

bbchallenge id 141950, a six-state holdout of group G05 (growth class fixed/sqrt). **Open**, and reduced in Lean
(kernel) to a Collatz-like orbit: the machine never halts unless the orbit of (0, 0) under
`(3k, y) -> (4k+1, y+4)`, `(3k+1, y) -> (4k+5, y+6)`, `(3k+2, y) -> (4k+8, y-1)` ever reaches y = 0 with z not
a multiple of 3.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1RC | 1RF |
| C | 1LA | 0RA |
| D | 0LA | 0LE |
| E | 1LD | 1LA |
| F | 0RB | --- |

## What it does

**The tape.** The right end of the tape is fixed; everything happens at the left end. Whenever the head, in state A,
is on the leftmost visited cell with nothing grown yet, the tape is a *wall*

    C z y  =  A>0 0 10 0^z (10)^y 0 1        (blank tape on both sides)

(z = 0, y = 0 at step 7; then (1, 4), (5, 10), (12, 9), (17, 13), (28, 12), ... at steps 44, 202, 257, 490, 733, ...).

**A sweep** (`sweep`, 4x + 11 steps): `A>0 (10)^x 0 10 0^(z+3)` becomes `A>0 (10)^(x+2) 0 10 0^z`: the head runs
right over the grown 10s (B), writes into the wall and comes back (D); the wall loses three 0s and the left block
gains two 10s. The sweep never looks at the right part. A wall z = 3k + r takes k sweeps, 4k² + 7k steps
(`sweeps`), and leaves x = 2k and r = 0, 1, 2 zeros.

**The end of a wall** (`end0`, `end1`, `end2`): the grown 10s are erased back to 0s, the head walks to the right end
and back, and a new wall starts:

| left over | new z | new y | steps |
|---|---|---|---|
| r = 0 | 2x + 1 = 4k + 1 | y + 4 | 8k + 8y + 37 |
| r = 1 (y ≥ 1) | 2x + 5 = 4k + 5 | y + 6 | 16k + 16y + 94 |
| r = 2 (y ≥ 1) | 2x + 8 = 4k + 8 | y − 1 | 16k + 28 |

**The emergent behaviour: a Collatz-like map with a drifting counter.** From wall to wall, z is multiplied by about
4/3 and the counter y moves by +4, +6 or −1 according to z mod 3 (the last base-3 digit of z). This is the shape of
bbchallenge's Antihydra (n -> floor(3n/2), counter +2 / −1), with 4/3 in place of 3/2 and a drift of +3 per step
instead of +1/2.

**Where it can halt.** F reads a 1 (the only halting transition) never happens inside the rules above. The map
breaks down only at a wall with y = 0 and z not a multiple of 3 (`orb_exit`): then there is no 10 left on the right
for `end1`/`end2`, the head uses up the final `0 1` and the tape takes another shape. Since y goes down only by
one at a time, an exit comes from (3k+2, 1) -> (4k+8, 0) with k not ≡ 1 mod 3. From such configurations the machine
sometimes halts (from `C 92 0` after 54,805 steps; computed) and sometimes not (`C z 0` for z = 4k + 8 ≤ 164, k not
≡ 1 mod 3, other than 92: no halt in 10^6 steps).

## Status and evidence

**Lean, kernel only** (`lean/Rules.lean`, written by `py/gen_rules.py` with `bbtools.symtm.prove`): the cell rules
`sweep_cells`, `end0s`, `end1s`, `end2s` (x ≥ 1) and `end0z`, `end1z`, `end2z` (x = 0), for all x, y.

**Lean, kernel only** (`lean/Macro.lean`): `sweep`, `sweeps` (with `scost_eq`: `scost x k + 4k = k(4x+11) + 4k²`),
`end0`, `end1`, `end2` on the encoding `S x z R`, `C z y`.

**Lean, kernel only** (`lean/Reduce.lean`): the map `next` and its cost `mcost`; `next_sound` (the machine goes
from `C z y` to the next wall in exactly `mcost z y` steps); `init_wall` (blank tape reaches `C 0 0` in 7 steps);
the orbit `orb`; **`not_halts_of_orbit`: `(∀ n, orb n ≠ none) → ¬ HaltsFromBlank`**; `orb_exit` (the orbit leaves
the rules only at y = 0, z % 3 ≠ 0).

**Lean, `native_decide`** (`lean/OrbitRun.lean`): `orbit_runs`: 10,000 macro steps with step counts (`orbT`, proved
a run of the machine by `orbT_sound`, kernel) stay inside the rules and take more than 10^2400 steps; hence
`orb_some_10000` and `blank_runs_orbit` (no halt in the first 10^2400 steps). `lean/Axioms.lean` prints the axioms.

**Computed (trusted)**: `py/check.py 1e9` runs the machine 10^9 steps and finds every wall exactly at the step and
with the whole tape the map predicts, and no other wall. `py/orbit.py 1e6`: 10^6 macro steps, no exit; at the end
y = 2,999,377 and z has 124,940 decimal digits; after the first step y never fell below 4; the residues of z mod 3
came 332,673 / 333,716 / 333,611 times; y − 3n stayed within a few thousand of 0 (−623 at the end).

**Heuristic**: if z mod 3 behaves like a fair die, y is a random walk with steps +4, +6, −1; the chance of ever
reaching 0 from height y is about ρ^y with ρ = 0.3349 the root of (ρ⁴ + ρ⁶ + 1/ρ)/3 = 1. With y ≈ 3n that is
astronomically small after the first few steps (and y was never below 4). So the machine almost certainly never
halts, but a proof needs control of the base-3 digits of an orbit multiplied by 4/3, a Collatz-type problem.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---/lean/check.sh
python3 holdouts/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---/py/gen_rules.py     # rewrites lean/Rules.lean
python3 holdouts/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---/py/check.py 1e9     # about 7 minutes
python3 holdouts/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---/py/orbit.py 1e6     # about 45 seconds
```

## Pages

- [`pages/holdouts/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---/explainer.html`](../../pages/holdouts/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---/explainer.html)
- [`pages/holdouts/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---/proof-status.html`](../../pages/holdouts/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---/proof-status.html)

## For later

The structure is closed and the reduction is proved; what is left is the orbit itself. Possible next steps: run the
orbit further with a base-3 representation (each step is a multiplication by 4/3 with a small carry, so z mod 3^j for
the next j steps depends only on the last j digits); and analyse what the exit configurations `C z 0` (z = 4k + 8)
do, to turn `not_halts_of_orbit` into an exact "halts iff" statement.
