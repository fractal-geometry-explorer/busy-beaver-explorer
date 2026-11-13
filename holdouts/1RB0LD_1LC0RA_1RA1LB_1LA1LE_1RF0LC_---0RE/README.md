# 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE

bbchallenge id 50372. Group G01. **Collatz-like with a doubling counter**: the run is the orbit of a map
n → 3n − 10·2^k + 3k + 14 (k ≈ log₂ n the level), and the machine halts exactly when n lands on
h_k = 5·2^k − k − 6. Listed by bbchallenge as "potential Cryptid, chaotic". Open; probviously non-halting.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1LC | 0RA |
| C | 1RA | 1LB |
| D | 1LA | 1LE |
| E | 1RF | 0LC |
| F | --- | 0RE |

## What it does

Sample the run when the tape is

    P(n)  =  0^inf (10)^n A> 0^inf

From blank tape (which is P(0)) the machine reaches P(4) at step 31, then P(9), P(24), P(52), P(99), P(163), …
One round from P(n):

1. **Sweep** (`r_sweep`, `r_start`): the head runs left and turns the tape into `F> 1^(2n+2)`, a counter
   `T(c, m) = 0^inf 1 F> (10)^c 1^m` with c = 1 and m = 2n+2 ones.
2. **Doubling rounds** (`t_round`): while m ≥ 2c+6, T(c, m) → T(2c+4, m − 2c − 6), through a zigzag
   `S(a, b, m) = 0^inf (10)^a 11 A> (01)^b 1^m`, S(a+1, b+1, m+2) → S(a, b+3, m) (`zig_iter`, by induction).
   c runs 1, 6, 16, 36, 76, … = 5·2^j − 4; the number k of complete rounds is the level.
3. **End** (`tend`): with m < 2c+6 ones left, m = 0 or 1 halts (`T0_halts`, `T1_halts`); otherwise the
   remainder picks one of a few short endings and a final sweep `X(c, m) = 0^inf 1 (01)^c B> 1^m`,
   X(c, m+2) → X(c+2, m) (`x_iter`), writes P(n′).

Closed form: with h_k = 5·2^k − k − 6 (3, 12, 31, 70, 149, 308, 627, 1266, …), for h_k < n < h_{k+1} and
r = n − h_k − 1:

    n′ = 5·2^k − 1 + 3r = 3n − 10·2^k + 3k + 14
    steps = 12r² + (40·2^k + 6)r + (100·4^k + 23)/3 − 10·2^k

and P(h_k) halts. n′ ≈ 1.58·n on average, so the level grows by about 0.66 per round.

**Halting condition.** The machine halts if and only if the orbit of 4 reaches some h_k.

**Heuristic.** From level k, n′ takes about 5·2^k values (step 3), and the targets h_j in reach occur with
period 6 in k (4 targets per 6 levels); treating r as random, the chance of a hit is about 2^−k per round. Since
k grows linearly, the sum converges: the chance of a halt after the 10⁵ rounds followed in Python (k ≈ 66,605)
is about 10^−20,000. Halting is a question of the same kind as the Collatz problem (does a 3x+c / 2^k orbit avoid
a sparse set?), hence "Cryptid".

## What is proved

| level | result | where |
|---|---|---|
| kernel | halting configurations; no halt in 10⁴ steps (10⁷ by native_decide) | `lean/Blank.lean` |
| kernel | 21 symbolic rules (generated) | `lean/Rules.lean` from `py/rules.py` |
| kernel | the macro step: `pstep n` returns P(n′) with exact steps or a halt, sound for **every** n | `pstep_sound`, `lean/Macro.lean` |
| kernel | blank → P(4) in 31 steps; any value of `orbit k 4` is a true run | `init_P4`, `orbit_sound`, `lean/Orbit.lean` |
| kernel | 200 rounds without a halt, > 10⁸⁶ steps | `orbit_200`, `orbitT_200_big` |
| native | 2,000 rounds without a halt, > 10⁷⁹⁸ steps | `orbit_2000`, `orbitT_2000_big` |
| trusted | closed form = `pstep` for 1 ≤ n ≤ 200,000 (Python transcription of the Lean function) | `py/macro.py check 200000` |
| trusted | all 16 P-events up to 10¹⁰ steps match direct simulation (last: P(70411) at step 9,108,900,940) | `py/macro.py orbit 1e10`, `c/pevents.c` |
| trusted | 10⁵ rounds without a halt: n has 66,605 bits, ≈ 10^40,100 steps | `py/macro.py far 1e5` |
| heuristic | chance of a later halt ≈ 10^−20,000 | above |
| open | does the orbit of 4 ever hit an h_k? | |

The closed form itself is not proved in Lean: Lean evaluates `pstep` (closed polynomial step counts, fuel-bounded
round recursion) directly, so the orbit theorems do not depend on it.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/lean/check.sh     # ~2 min
python3 holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/py/rules.py > holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/lean/Rules.lean   # regenerate the rules
python3 holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/py/macro.py check 200000
python3 holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/py/macro.py orbit 1e10
gcc -O2 -o pevents holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/c/pevents.c && ./pevents 10000000000   # ~3 min
python3 holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/py/macro.py far 1e5                               # ~10 min
```

## Further work

Prove the closed form in Lean (an induction over the doubling rounds with c = 5·2^j − 4), which would turn
`pstep` into an explicit map and the halting question into a pure number-theory statement.

## Pages

- [`pages/holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/explainer.html`](../../pages/holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/explainer.html)
- [`pages/holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/proof-status.html`](../../pages/holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/proof-status.html)
