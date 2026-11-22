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
- **Iterated (trusted):** `c/far.c` ran the map with the sweep jumped for 56 minutes: 3.26e21 map steps,
  7.03e32 machine steps, sizes up to about 2.6e11, no halt. Earlier: `tools/collatz/c/dm9516.c`,
  10^12 accelerated steps.
- **Near misses (heuristic):** m − 3b came within 2 of 1 at 16 sweep starts (values −1, 0, 2, 3), at sizes up
  to about 1.3e11, about once per decade of steps. If m − 3b behaved like a random number of the size of
  b, a halt would have a chance of about 0.1 per decade of steps (about 20 sweep starts per decade have |m − 3b − 1| ≤ 100):
  probability 1 eventually, but very late. About 3 hits were expected in this run and none came (chance about 5%).
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

1. Find a reason why the orbit avoids m = 3b + 1 at sweep starts, or a faster accelerator (whole rounds between walls)
   to push the hunt beyond sizes 10^12.

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
gcc -O2 -o /tmp/far holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/c/far.c && /tmp/far 3600
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC--- 1000000000 records 100000 > /tmp/rec.txt
python3 holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/py/shape.py /tmp/rec.txt a=10
python3 holdouts/1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---/py/switches.py /tmp/rec.txt a=10
```
