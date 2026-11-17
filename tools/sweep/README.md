# Sweep of the Lean-proved finite-variable maps

36 open BB(6) holdouts have a Lean theorem `halts_iff`: the machine halts from blank tape if and only if the orbit of
an explicit map on a fixed tuple of naturals (sometimes with a finite tag) reaches a halting case. This folder runs
all 36 maps on one engine, far past their earlier bounds, and compares them with each other and with known problems.

## Files

| file | what it is |
|---|---|
| `engine.py` | the engine: loads `maps/<slug>.py`, iterates exactly (gmpy2 big integers), records branch counts and the closest approach to the halting case, checkpoints to JSON and resumes. `python3 engine.py list`, `run SLUG --seconds S --ckpt DIR`, `orbit SLUG N` |
| `maps/m_<machine>.py` | one module per machine (`---` written `ZZZ`): `MACHINE`, `LEAN` (file and theorem names), `VARS`, `START`, `HALT`, `KIND`, `BOUND` (the best run before this sweep), `step` (the Lean map, case for case), optional `margin` and `accel` (exact batching) |
| `maps/_cycle.py` | exact batching of translation cycles for the frame maps given as data (keeps Lean's first-match order) |
| `residue.py` | divide and conquer runner for "affine residue walks" (one big number x ↦ (A·x + B[x mod D]) / D and a small counter): K steps at once from x mod D^K in O(M(K) log K), special steps done by the module's own `step` |
| `report_A.md` … `report_D.md` | transcription reports: the map, the Lean theorem, what each module was checked against |
| `report_F08.md` | the four F08 zone-orbit machines (run by their own engine, recorded here for the table) |

Every module was checked against the machine's own orbit script for at least 10,000 states and against a direct
simulation from blank tape (map states found in order in the real run). `residue.py check` compares its blocks
with plain steps; a 245,760-step run of each of its three maps ends in the same state as plain stepping.

## Families found

**Doucette family (5 machines).** Each is a sequence D → D + α·a + v + γ, where D = b^v·(b·a + ρ) with ρ ≠ 0 (v
counts the factors b), and the machine halts iff some D is a pure power of b (in base 3, with one more condition).
All five are proved in Lean, for every value, from each machine's proved map (`halts_iff_pow2` in Space Needle's
`lean/Collatz.lean`, `halts_iff_doucette` in the others' `lean/Doucette.lean`):

| machine | base b | rule (r = 1) | exception | halts iff | D |
|---|---|---|---|---|---|
| 1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD (Space Needle) | 2 | D + 3a + v | none | power of 2 | b + 3 at c = 1 visits |
| 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE | 2 | D + a + v | D = 3·2^v: D + v + 3 | power of 2 | p + 3 at q = 1 visits |
| 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC | 2 | D + a + v + 1 | D = 3·2^v: ends at p = 3 | power of 2 | p + 3 at r = 1 visits |
| 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB | 2 | D + a + v + 2 | D = 3·2^v, v even > 0: (3D + 3v + 10)/2 | power of 2 | n + 2 (every pass) |
| 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB | 3 | D + a + v + 2 + ρ | D = 3^v: ends at p = 2 | 3^v with v + r ≡ 1 (mod 3) | p + 1 at r = 1 visits |

The Space Needle rule is Doucette's sequence; the others are its ×3/2 relatives (the community calls three of them
"Space Needle-like"), and the last is the base-3 version. The fitted rules (first 1,500 to 20,000 terms) missed the
exceptions because the orbits never take those values (none in the first 20,000 terms); the Lean statements include
them, so the equivalences need no assumption. Correction to the fit: in base 3 a power of 3 halts only when
v + r ≡ 1 (mod 3) (for r = 1, when 3 | v), and otherwise the sequence goes on.

**Same map, different start.** 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE is the map of
1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE under N = 2n + 2 (checked for every n < 200,000), started at n = 10
instead of n = 1. The two orbits share no value in their first 5,000 steps, so this is one question about one map
from two starting points, not a halt-together pair.

**Conjugate up to a thin set.** The phase maps of 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE and
1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE agree under r(x,y) ↦ a(x,y−1), q(m,k,t) ↦ q(m,k/2,t) on 6161 of 6280
grid points. Their orbits run in sync for long stretches (89,633 shared states in the first 10^6 phases) and fall
out of sync at all-ones moments; a halt inside a synced stretch is a halt of both.

**Same branches, different boundary.** 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE and
1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD have the same main branches (compare two numbers, subtract, multiply
the smaller by 3, same constants and halting set) but differ on the rows next to the diagonal; their orbits share
nothing.

**Antihydra-type walks.** Antihydra (1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA: x ↦ ⌊3x/2⌋, counter +2/−1 by
parity), 1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA (y even ↦ 3y/2 with +2, y odd ↦ (3y+3)/2 with −1) and
1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC (×4/3 by residue mod 3, counter −1/+1/+1) are all one big number and a
drifting counter; `residue.py` runs them.

**Doubling inside a budget.** The four e/q phase machines, 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD,
1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE, 1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD and the doubling-mod pair
1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC / 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE: a number doubles while a
budget pays for it, and a halt needs the budget to be used up exactly.

## Results

See `RESULTS.md` (written as the runs finish).
