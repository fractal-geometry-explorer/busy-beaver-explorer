# The Doucette family: what can be said about the sequences

Five holdouts halt exactly when a Doucette-type sequence reaches a power of the base (proved in Lean, each in its own
folder; see [`tools/sweep/README.md`](../sweep/README.md)):

| machine | base | next D (D = b^v (b a + ρ)) | start |
|---|---|---|---|
| 1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD (Space Needle) | 2 | D + 3a + v | 6 |
| 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE | 2 | D + a + v | 5 |
| 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC | 2 | D + a + v + r | (5, r = 2) |
| 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB | 2 | D + a + v + 2 | 6 |
| 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB | 3 | D + a + v + r + ρ + 1 | (4, r = 1) |

This folder is about the sequences themselves. The page is
[`pages/holdouts/doucette-family.html`](../../pages/holdouts/doucette-family.html) (built by `build_page.py`).

## Proved in Lean

**The last step before a halt** (`holdouts/<machine>/lean/Preimage.lean`, with the shared arithmetic in
`PowMod.lean`; kernel only, no `native_decide`). Which values step onto a power? For the four maps with α = 1 the
equation `D' = b^n` reads `(b a + ρ)(b^(v+1) + 1) + w = b^(n+1) + c` with `w` a small linear expression in `v` (and
`r`, `ρ`), and since `b^(v+1) ≡ −1` the powers of `b` modulo `q = b^(v+1) + 1` are only `±b^i`, `i ≤ v`
(`PowMod.pow_mod`). So `w` must be one of a few numbers, which pins `v` and puts `n` in one class:

| machine | a value steps onto b^n only if | never reached | Lean |
|---|---|---|---|
| 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE | v = 0, n even; or v = 1, n ≡ 3 (mod 4) | n ≡ 1 (mod 4) | `last_step`, `no_pow2_one_mod_four` |
| 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC | r = 1: v = 0, n odd; v = 1, n ≡ 2 (4); v = 2, n ≡ 4 (6). r = 2: v = 2, n ≡ 3 (6); v = 3, n ≡ 6 (8). Exception: only (12, 1) → 16 | n ≡ 0, 8 (mod 12), n > 4 | `last_step`, `no_pow2_mod_twelve` |
| 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB | v = 2, n ≡ 3 (mod 6); or v = 3, n ≡ 6 (mod 8) | 17 of every 24 exponents | `last_step`, `halting_exponent` |
| 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB | r = 1: v = 1, n ≡ 3 (4) if ρ = 1, n ≡ 0 (4) if ρ = 2. r = 2: v = 0, or v = 2, ρ = 2, n ≡ 4 (6) | a halt from r = 1 has n ≡ 0, 3 (mod 12) | `last_step`, `halt_from_r1` |

For Space Needle (α = 3) the modulus is `2^(v+1) + 3` and has no such symmetry: `last_step_congr` gives
`2^(n+1) ≡ 2v − 3 (mod 2^(v+1) + 3)`, and `last_step_small` works it out for v ≤ 8 (v = 1, 4, 7 impossible; v = 0, 2,
3, 5, 6, 8 each one class of n, modulo 4, 10, 18, 66, 130, 204). Computed further (sympy, not in Lean): v = 9, 10,
12, 13, 18, 19, 21–26, 28, 31–33, 35, 36, 39, 40 are impossible; about 60% of exponents below 400 have no
predecessor at all.

These are the wiki's "dangerous families" (Aristotle's lemmas for 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE), made
exact for all five machines.

**The shift identity** (`lean/Shift.lean`, standalone, `lean/check.sh`): for the generic step
`D + α·(part D / b) + β(val D, part D mod b)`, if `D = b^m X + L`, `X ≥ 1`, `L ≠ 0`, `val L + 2 ≤ m`, then `D` has the
valuation and last part-digit of `L`, its part is at least `b^2` (so `D` is never exceptional), and
`step D = b^(m−v−1)(b^(v+1) + α) X + step L` (`shift`); iterated, `jump`. This is what `djump.py` uses.

## Computed

`djump.py MACHINE STEPS` (Python with gmpy2/GMP; `pip install gmpy2`). It advances the low digits alone by the shift
identity, recursively, and folds the high part back in by one multiplication: N terms in roughly the time of a few
multiplications of the last term. Top-level steps (where the identity gives no certain step) use the exact Lean map
`G`, exceptions included, so every possible halt is checked exactly. `--check N` compares it with the plain map at
50 points up to N (done to 200,000 for Space Needle and 20,000 for all five). For Space Needle it reproduces the
community's 10^8-term run (94,125,050 bits at term 10^8, first v = 25 at term 23,145,881).

| machine | terms | last term | largest v (first at term) | time |
|---|---|---|---|---|
| 1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD (Space Needle) | 10,000,000,000 | 9,411,461,282 bits | 32 (1,567,575,299) | 3.3 h |
| 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE | 1,000,000,000 | 401,523,017 bits | 31 (821,959,313) | 12 min |
| 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC | 1,000,000,000 | 401,522,426 bits | 29 (312,120,542) | 12 min |
| 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB | 1,000,000,000 | 401,524,403 bits | 32 (161,127,945) | 12 min |
| 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB | 1,000,000,000 | 198,650,412 base-3 digits | 18 (680,991,685) | 25 min |

Results and SHA-256 checkpoints (every 10^8 terms; every 10^9 for the Space Needle run, which was done in three
segments with `--save-dir`/`--resume` and `--maxm 400000000` to stay under about 5.5 GB) are in `results/run_*.json`.
The valuation counts match the geometric law (`build_page.py` prints χ²; Space Needle: 20.1 on 26 degrees of
freedom at 10^9 terms), the growth matches the prediction to five digits (0.94116 bits per term against 0.94115),
and consecutive valuations look independent (`results/pairs_*.json`).

`tree.py MACHINE N` computes, for every n ≤ N, the whole backward tree of `b^n` (every value whose orbit reaches it).
Depth at most 9 (Space Needle) and 33 (the others) for n ≤ 400 (`results/tree_*.json`), against hundreds of terms
needed just to grow to that size.

## What does not work, and why

- Residues: every finite run of valuations is exactly one residue class modulo `b^Σ(v_i+1)` (the multiplier
  `b^(v+1) + α` is prime to b), so no congruence on D is invariant along orbits in general, and the conditions above
  leave infinitely many exponents open.
- Backward trees are finite for each n, but bounding their depth for all n is the original problem.
- Baker-type bounds (as for 1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---) need a closed form of the orbit; these orbits
  have none.
