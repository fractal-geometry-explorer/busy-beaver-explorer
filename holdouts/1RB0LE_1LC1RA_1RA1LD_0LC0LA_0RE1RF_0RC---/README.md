# 1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---

bbchallenge id 9516. One of the six-state holdouts whose halting from blank tape is open. Family: **solid block and alternating stretch, erratic sizes**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1LC | 1RA |
| C | 1RA | 1LD |
| D | 0LC | 0LA |
| E | 0RE | 1RF |
| F | 0RC | --- |

## Status

Open, and now exactly a question about one orbit of a map on three numbers.

- **Lean (kernel, core Lean): halts iff DeepMind's map stops.** `deepmind_halts_iff` (`lean/DMMap.lean`) proves on this
  repository's semantics what google-deepmind/cryptids proves with Mathlib: the machine halts from blank tape iff the
  orbit of their map `DM.next` on C(m, k, b) = `0^inf 1^m (10)^k C> 1^b 0^inf` from C(0, 0, 2) stops. It used to be a
  cited axiom. The 12 clauses are 18 symbolic rules in `lean/DMRules.lean`, written by `tools/deepmind/dmproof.py`.
- **Lean (kernel): halts iff the orbit visits m = 3b + 1.** `halts_iff_visits` (`lean/Criterion.lean`): the map stops
  only at C(2, 0, b ≥ 2), only C(1, k, 0) goes there, and C(m + 3, k, b + 1) always sweeps to C(m, k + 2, b). So the
  machine halts iff the orbit visits some C(3B + 1, k, B).
- **Lean (kernel): the shortcuts of the fast iterator.** `left_step` and `wall_step` (`lean/Batch.lean`): q + 1 map
  steps take C(3q + r, k, q + 2 + c) to C(4q + 2k + 2 + 2[r = 1], 1, c) (q ≥ 1, r < 3), and b + 1 map steps take
  C(3b + d, k, b) to C(d + 1, 0, 2(k + 2b) + 2).
- **Iterated (trusted):** `c/fast.c` runs the map with both shortcuts (left steps L ≤ 9 at a time from tables indexed
  by m mod 3^L), each used only with a margin of 101 so every sweep start with |m − 3b − 1| ≤ 100 is still examined.
  It agrees exactly with `c/far.c` to 3·10^8 walls and is 1.9 times as fast. Three two-hour legs from checkpoints:
  **1.81e24 map steps, 9.16e36 machine steps**, 9.50e11 walls, 3.80e12 sweep starts, m + b up to 7.6e12, no halt.
  Earlier: `c/far.c`, 3.26e21 map steps (7.03e32 machine steps) in 56 minutes; `tools/collatz/c/dm9516.c`, 10^12
  accelerated steps.
- **Near misses (heuristic):** m − 3b came within 2 of 1 at 16 sweep starts (values −1, 0, 2, 3), at sizes up
  to about 1.3e11, and at none in the 1.8 further decades of the fast run (about 2 expected). Sweep starts with
  |m − 3b − 1| ≤ 100: 669 in all, 38 to 71 per decade of b, flat in d (about 3 per value of d; d = 1 is one of many
  values with none). If m − 3b behaved like a random number of the size of b, about 3.3 hits of d = 1 were expected
  by now and none came (chance about 4%); residues of d at walls mod 2, 3, 4, 5, 8, 9, 16, 27 are uniform, so there is
  no sign of an invariant. The model gives about 0.28 expected hits per decade of b: probability 1 eventually, very late.
- Older checks: no halt in 10^7 steps by `native_decide` and 10^9 by C; Quick_Sim 7.07·10^14 steps.

## What it does

Two parts: at left-end switches `0 0 (10)^r 1^m` (or `0 1 1 (10)^r 1^m`), at right-end switches `0 1^m (10)^r 0`;
the parts swap sides each trip, with erratic sizes (e.g. right m = 2733, 3627, 238 after left m = 9, 1564).

Halting: F on a 1, entered only from E on a 1 moving right: a halt is exactly `E>1 1`.

Growth: 666 side switches in 10^9 steps; after 5·10^8 they are ≈ 0.291·w² steps apart and add ≈ 6 cells each, so
width ~ t^(1/3) (fitted 0.344; 3,679 cells). `py/shape.py` and `py/switches.py` print all of this from a `tmrun ... records` log.

## The map

With C(m, k, b) = `0^inf 1^m (10)^k C> 1^b 0^inf` (left block, stretch, right block):

| clause | to | steps |
|---|---|---|
| C(m + 3, k, b + 1) (sweep) | C(m, k + 2, b) | 6k + 9 |
| C(m, k, 0) (wall) | C(m + 1, 0, 2k + 2) | 4k + 3 |
| C(0, k, 1) | C(2k + 3, 0, 2) | 4k + 7 |
| C(0, k, b + 2) | C(2k + 2, 1, b) | 4k + 8 |
| C(1, 0, b + 1) | C(0, 0, b + 3) | 4 |
| C(1, k + 1, 1) | C(2k + 7, 0, 2) | 4k + 37 |
| C(1, k + 1, b + 2) | C(2k + 6, 1, b) | 4k + 38 |
| C(2, 0, 1) | C(0, 1, 0) | 8 |
| C(2, 0, b + 2) | halt | 7 |
| C(2, 1, b + 1) | C(0, 1, b + 1) | 10 |
| C(2, k + 2, 1) | C(2k + 7, 0, 2) | 4k + 25 |
| C(2, k + 2, b + 2) | C(2k + 6, 1, b) | 4k + 26 |

The sweep trades three 1s on the left and one on the right for two `10` pairs. When the right block runs out, the wall
turns the stretch into a new right block; when the left block runs down below 3 first, the stretch becomes a new left
block about twice as long. A halt needs a run of sweeps that empties both blocks at once, leaving one 1: m = 3b + 1.

## Later

1. Find a reason why the orbit avoids m = 3b + 1 at sweep starts. The work is now about one map step per unit of
   size (≈ 0.12 walls per unit of m + b), so going much further needs an idea that skips walls, not a faster loop:
   between walls the left steps form a 4/3 map m → 4⌊m/3⌋ + c on the fraction x = m/(m + b), and the wall is
   x → 4x − 3, an expanding map with no visible structure.

## First look

Growth class **power/power** (left: power, exponent 0.341; right: power,
exponent 0.345). After 1,000,000,000 steps: 3,680 cells visited (1,766 left of the
start, 1,213 right), 3,050 ones.

- left, step 980,492,457: `E>0 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- left, step 996,727,782: `C>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 972,250,598: `0 1^1438 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1`
- right, step 996,613,780: `0 1^239 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/explainer.html`](../../pages/holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/explainer.html)
- [`pages/holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/proof-status.html`](../../pages/holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/lean/check.sh
gcc -O2 -march=native -o /tmp/fast holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/c/fast.c -lm && /tmp/fast 7000 /tmp/ck.bin  # repeat to resume
gcc -O2 -o /tmp/far holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/c/far.c && /tmp/far 3600
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC--- 1000000000 records 100000 > /tmp/rec.txt
python3 holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/py/shape.py /tmp/rec.txt a=10
python3 holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/py/switches.py /tmp/rec.txt a=10
```
