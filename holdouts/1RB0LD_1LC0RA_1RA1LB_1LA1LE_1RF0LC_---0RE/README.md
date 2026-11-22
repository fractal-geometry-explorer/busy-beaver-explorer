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
| kernel | **`halts_iff`: the machine halts from blank tape if and only if `orbit k 4 = none` for some k** (the fuel in `pstep` never runs out, and a macro step takes at least 8 steps) | `halts_iff`, `pstep_never_unknown`, `lean/Iff.lean` |
| kernel | 200 rounds without a halt, > 10⁸⁶ steps | `orbit_200`, `orbitT_200_big` |
| native | 2,000 rounds without a halt, > 10⁷⁹⁸ steps | `orbit_2000`, `orbitT_2000_big` |
| kernel | closed form of the position: `pstep n` goes to P(3n + 3k + 14 − 10·2^k) for h_k < n < h_{k+1}, halts at n = h_k | `pstep_closed`, `pstep_halt`, `lean/Closed.lean` |
| trusted | closed form of the step count = `pstep` for 1 ≤ n ≤ 200,000 (Python transcription of the Lean function) | `py/macro.py check 200000` |
| trusted | all 16 P-events up to 10¹⁰ steps match direct simulation (last: P(70411) at step 9,108,900,940) | `py/macro.py orbit 1e10`, `c/pevents.c` |
| trusted | 10⁵ rounds without a halt: n has 66,605 bits, ≈ 10^40,100 steps | `py/macro.py far 1e5` |
| kernel | **no congruence invariant**: no set of residue classes mod any divisor of 2^16·3^9 holds the run, is kept by the map and misses every h_k (same for the starts n = 10 and n = 1 of the two sibling machines) | `no_cong_4`, `no_cong_10`, `no_cong_1`, `no_inv`, `lean/Congruence.lean` |
| trusted | the same for every modulus M ≤ 20,000 and every 2^j·3^i ≤ 2^12·3^7 (breadth-first search) | `py/congruence.py all 20000`, `grid 12 7` |
| heuristic | chance of a later halt ≈ 10^−20,000 | above |
| open | does the orbit of 4 ever hit an h_k? | |

The closed form of the position is now proved in Lean for every n (`pstep_closed`: for h_k < n < h_{k+1},
`pstep n = .go (3n + 3k + 14 − 10·2^k) t` for some t; `pstep_halt`: `pstep (h k)` halts for k ≥ 1; both in
`lean/Closed.lean`, kernel only); the step-count formula is still only checked in Python, and the orbit theorems
evaluate `pstep` directly. The three holdouts 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE, 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE and 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE iterate the same function f(n) = 3n − 10·2^k + 3k + 14 (h_k < n < h_{k+1}, halt at n = h_k), the second in the coordinate N = 2n + 2, from different starts (n = 4, 10, 1); the three orbits share no value in their first 20,000 steps (checked in Python).

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/lean/check.sh     # ~2 min
python3 holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/py/rules.py > holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/lean/Rules.lean   # regenerate the rules
python3 holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/py/macro.py check 200000
python3 holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/py/macro.py orbit 1e10
gcc -O2 -o pevents holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/c/pevents.c && ./pevents 10000000000   # ~3 min
python3 holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/py/macro.py far 1e5                               # ~10 min
python3 holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/py/congruence.py all 20000   # ~8 min; `lean 16 9 17 17` ~1 min
```

## Congruences cannot settle it

A non-halting proof of the usual Collatz kind would be a set of residue classes (of n mod 2^j·3^i, say) that holds
the run, is kept by the map and misses every h_k. There is none. With v = n + k + 6 − 5·2^k (v = 0 exactly at
n = h_k) the step is, exactly,

    v′ = 3v + 2 + 5·2^k + k′ − 5·2^k′,   k′ = k + d,  d ∈ {0, 1} (d = 2 only in the top ~k/3 values of a level).

A congruence mod M sees only (v, k, 2^k) mod M, and whether d is 0 or 1 depends on the size of n inside its level,
not on its residues: for 2^k ≥ 3M + k + 10 every residue of v occurs with both (`realize`). So an invariant has to
survive both choices, and one sequence of choices from the residues of the run to v ≡ 0 rules it out (`no_inv`).
`py/congruence.py lean 16 9 17 17` finds such sequences (34 choices, meet in the middle) for M = 2^16·3^9 from the
three starts, and `lean/Congruence.lean` checks them in the kernel; an invariant mod a divisor of M would be one
mod M (`no_inv_dvd`), so this covers every 2^j·3^i with j ≤ 16, i ≤ 9. A breadth-first search finds such paths
for every modulus M ≤ 20,000, primes other than 2 and 3 included (at most 24 choices). Mod 3^i the step forgets v
after i steps (it is multiplied by 3), and mod 2^j the multiplication by 3 is a permutation while k drifts freely,
so the residues mix completely. A proof that the orbit avoids the h_k has to use the size of n within its level.

## Further work

The closed form of the position is proved (`lean/Closed.lean`); the step-count formula could be added the same way.

## Pages

- [`pages/holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/explainer.html`](../../pages/holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/explainer.html)
- [`pages/holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/proof-status.html`](../../pages/holdouts/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE`](../1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE/README.md): rename A→B, B→C, C→D, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE`](../1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F; it is this table started in state C

<!-- end of related machines -->
