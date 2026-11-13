# 1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD

bbchallenge id 70770. Group G01. **Two-level Collatz**: a number n is multiplied by 3/2 or 9/8 per pass, and a
small counter k in the tail word moves by −2…+1 or is multiplied by 3/2. The map covers every configuration except
Z_k with n < 12k + 12, the only place a halt can come from. **The map is proved in Lean's kernel** for every tail
and n outside that region, and the orbit from blank tape is checked in Lean for 10⁵ passes (no halt in 10¹⁶⁰⁰⁰
steps). Open; probviously non-halting, because k would have to catch up with n.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1LC | 0LD |
| C | 0RF | 0LD |
| D | 0LE | 0RA |
| E | 0LC | 1RA |
| F | 1RC | 1RD |

## What it does

Sample the run at an **E-event**: the head, in state E, at the left end of the tape on the first of six 0s,

    E> 0^6 (10)^n T            (blank beyond T; n maximal)

From blank tape the first is (T, n) = (`1`, 0) at step 18. The tail T is always one of

    1,    X_k = 000 (10)^k 1,    Y_k = 11 (01)^k,    Z_k = 000 (10)^k 0001

and the next E-event is:

| tail | rule |
|---|---|
| `1` | n even → (`1`, (3n+6)/2); n odd → (X_0, (3n+1)/2) |
| Z_k | n even → (`1`, (3n−d)/2); n odd → (X_0, (3n−d−5)/2), d = 6⌊(3k−2)/2⌋; **valid for n ≥ 12k+12** |
| X_k | n' = (9n+c)/8, by n mod 8 = 0…7: Y_{k−1}, Y_k, X_{k+1}, X_k, X_{k+1}, Y_{k−2}, Y_{k−1}, M(k); c = 24, 15, −2, 13, 4, 27, 18, 1 |
| Y_k | n' = (9n+c)/8, by n mod 8 = 0…7: Y_{k−2}, Y_{k−1}, M(k), Y_{k−1}, Y_k, X_{k+1}, X_k, X_{k+1}; c = 24, 15, −2, 21, 12, −5, 10, 1 |

Here M(k) = X_{3k/2+3} for even k and Z_{(3k+1)/2} for odd k. An index below 0 gives the tail `1`, except that X_0
at n ≡ 5 gives X_0 (c = 19) and Y_0 at n ≡ 0 gives X_0 (c = 16). So the run alternates between phases of 3/2 passes
(tail `1`) and phases of 9/8 passes (X/Y tails), in which the small counter k wanders by −2…+1 and grows by half at
1 pass in 8. A phase ends when k runs out, or at a Z_k, which subtracts about 4.5k in a 3/2 pass.

From blank tape: n = 0, 3, 5, 8, 12, 21, 32, 39, …, (`1`, 48351) at step 2.1·10¹⁰.

**Halting condition.** The X and Y rules hold for every n ≥ 0, and the Z rule for n ≥ 12k + 12. Below that bound
the tail becomes a longer word, and the machine can halt (for example from Z_15 with n = 189). So a halt needs a
Z-event with k ≳ n/12.

**Heuristic.** k is reset at every phase and grows by half only at 1 pass in 8 (and only when it is even), while n
grows at every pass. Along the orbit the fraction of Z-events with k ≥ K falls like K^−1.1 to K^−1.7 (0.6% for
K = 100, 0.04% for K = 1000). The chance of some phase reaching k ≈ n/12 is therefore about (n/12)^−1.2 per phase,
about 10⁻⁵ at the end of direct simulation and negligible after that. The tightest Z-event of the orbit is at pass 28
(n = 3989, k = 5), with n/(12k+12) = 55; after pass 70 the ratio is above 10⁶.

## What is proved

| level | result | where |
|---|---|---|
| kernel | the halting configurations; no halt in 10⁴ steps | `lean/Blank.lean` (generated) |
| native | no halt in 10⁷ steps | `lean/Blank.lean` |
| kernel | **the map**: for every tail T and every n, except Z_k with k = 0 or n < 12k + 12, the machine goes from `Ev n T` to the E-event `next T n` gives, in exactly the number of steps it gives (`next_sound`; axioms propext, Quot.sound) | `lean/Map.lean`, `lean/Cases.lean` |
| kernel | blank tape reaches `Ev 0 .one` in 18 steps (`init_E`); the first 3,000 passes stay in the proved region, so no halt in the first 10⁴⁵⁰ steps (`orbit_3k`, `no_halt_3k`); pass 37 is at step 20,999,239,576, as direct simulation finds (`orbitT_37`) | `lean/Orbit.lean` |
| native | the first 10⁵ passes stay in the proved region: no halt in the first 10¹⁶⁰⁰⁰ steps (`orbit_100k`, `no_halt_100k`) | `lean/Orbit.lean` |
| trusted | the map against direct simulation: a grid of every tail with k < 25 at 120 values of n each (Z_k from n = 12k+12): 9120 starts, no mismatch; 200 rules measured independently by direct simulation agree | `py/emap.py grid 25 120`, `py/emap.py rule`, `py/rules.json` |
| trusted | the 38 E-events of the blank run up to 2.1·10¹⁰ steps follow the map | `py/emap.py blank 2.2e10` |
| trusted | 10⁵ passes from (`1`, 0): n then has 8063 digits, k never above 1046, tightest margin n/(12k+12) = 55 | `py/emap.py far 100000` |
| heuristic | a halt needs k ≈ n/12; chance about (n/12)^−1.2 per phase | above |

### How the map is proved

`py/gen_map.py` writes `lean/Cases.lean`: 83 case theorems, one per family of E-events (tail `1` by n mod 2; X_k
and Y_k by n mod 8 with n = 8m+8+r or n = r, and k generic from some K on plus the k < K left over, or by parity of
k where the next tail is M(k); Z_k by the parities of k and n, with n = 24j + 2z + c). Each theorem is a chain of
segments proved by the symbolic simulator (`py/symtm2.py`, a copy of `tools/py/bbtools/symtm.py` that also crosses a
repeat with literal cells between it and the head, and splits long literal runs into segments of 40 steps) and of
loops: `srX`, `srY`, `srY0` (three rounds of the 9/8 phase, `(10)^(9i+3) E> (10)^(8x+8+r) T`), `one_even`,
`one_odd` (a round of the 3/2 phase, also used on the tail) and `srZ1`, `srZ2` (nine rounds with a Z tail), each
proved for one round and iterated by induction (`TM.iter` in `lean/Chain.lean`, with the step count in closed form
by `iterT_lin`). Between pieces the tapes are matched by normalizing both sides (`tape_eq` in `py/chain.py`). The
expected next event is read off `py/emap.py` at sample points and fitted linearly; Lean checks it. `py/gen_mapdef.py`
then writes `lean/Map.lean`, the map `next` as a Lean function and `next_sound` from the cases. The framework
(`py/chain.py`, `py/symtm2.py`, `lean/Chain.lean`) is shared with `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` and
`1RB0LE_1RC0LB_1RD0RC_1LA1RC_---1LF_1LB1LD`, which use it by path.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/lean/check.sh   # about 3 min
cd holdouts/1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/py
python3 gen_map.py && python3 gen_mapdef.py   # regenerate lean/Cases.lean, cases.json, Map.lean (a few min)
python3 emap.py rule 000101010101     # measured rules of a tail, compared with the map
python3 emap.py grid 25 120           # the map against direct simulation
python3 emap.py blank 2.2e10          # the blank run's E-events against the map
python3 emap.py far 100000            # 10^5 passes
```

`py/emap.py` uses `../1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---/py/g01tools.py` and its C simulator `c/from.c`.

## Further work

- Non-halting. The map is proved, so what is left is a statement about one orbit of an explicit map: k never
  catches up with n at a Z-event. No simple invariant k ≤ f(n) is in sight. Within a 9/8 phase the residues n mod 8
  that move k are themselves an orbit of n → (9n+c)/8, and that map is a bijection on residues mod 8^j, so every
  finite sequence of residues, including ones that pump k by 3/2 several times in a row, occurs for some n. A bound
  on k would therefore be a Collatz-type statement about this orbit. Empirically only n = 8, 11, 13, 15 among the
  3·10⁵ starts (`1`, n) with n < 3·10⁵ reach the uncovered region within 200 passes.
- The region n < 12k + 12 of Z_k has not been analysed beyond a few samples; the map leaves it undefined.
- This machine and `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---` are both a Collatz map driven by a tail or context
  word, but the words behave differently: here they form one counter, there they form a ternary-like counter.

## Pages

- [`pages/holdouts/1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/explainer.html`](../../pages/holdouts/1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/explainer.html)
- [`pages/holdouts/1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/proof-status.html`](../../pages/holdouts/1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/proof-status.html)
