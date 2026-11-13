# 1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA

bbchallenge id 13743. Group G01. **A 3/2-Collatz map on a mixed with Euclid-like steps on a second number b**: the
machine halts exactly at b = 1 with a ≡ 0 (mod 4), which takes a near-coincidence of size about 1/a. **The map is
proved in Lean's kernel for every even a** (the run from blank tape only meets even a), non-halting is reduced in
Lean to the orbit of the map, and that orbit is checked in Lean for 10⁵ passes (no halt in 10¹⁰⁰⁰⁰ steps). Open;
probviously non-halting.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 0LC | 1RF |
| C | 1LE | 1RD |
| D | 0RC | 1RC |
| E | 0LA | 1LA |
| F | --- | 1RA |

## What it does

Sample the run when the head is in state A at the left end of the tape. From step 118 on, the tape is then

    U(a, b)  =  A> 011011 1^a 0 1^b        or        V(a, b)  =  A> 1110 1^a 0 1^b

or the configuration 3 steps after a V-event, which is skipped. Write s for the letter of the start and o for the
other one. The next U/V-event is:

| case | from U | from V |
|---|---|---|
| a ≡ 0 (4), b odd ≥ 7 | s((3a+16)/2, b−5) | s((3a+20)/2, b−5) |
| a ≡ 0 (4), b = 1 | **HALT** | **HALT** |
| a ≡ 0 (4), b = 3 | V(4, (3a+16)/2) | V(2, (3a+22)/2) |
| a ≡ 0 (4), b = 5 | V(4, (3a+14)/2) | U(4, (3a+18)/2) |
| a ≡ 2 (4), b odd | o((3a+10)/2, b) | o((3a+10)/2, b) |
| a ≡ 1 (4), b odd | o((3a−3)/2, b+8) | o((3a−7)/2, b+8) |
| a ≡ 3 (4), b odd | s((3a+3)/2, b+3) | s((3a+3)/2, b+3) |
| a, b even, b ≥ a+4 | s(3a+6, b−a−3) | s(3a+8, b−a−3) |
| a, b even, b ≤ a−2 | o(3b+4, a−b−1) | o(3b+4, a−b−1) |
| a, b even, b = a | V(4, 3a+6) | V(2, 3a+9) |
| a, b even, b = a+2 | V(2, 3a+11) | V(4, 3a+10) |
| a odd, b even, b ≥ a−7 | s(3a−5, b−a+8) | s(3a−5, b−a+8) |
| a odd, b even, b ≤ a−13 | o(3b+26, a−b−12) | o(3b+24, a−b−12) |
| a odd, b = 0 | o(6, a−3) | o(6, a−3) |
| a odd, b = a−11 | V(4, 3a−5) | V(2, 3a−4) |
| a odd, b = a−9 | V(2, 3a) | V(4, 3a−3) |

These rules hold for a ≥ 15. For odd a < 15 they need b ≥ 30, and then the a ≡ 1 cases change (a = 1, and
s((3a−7)/2, b+7) for 5 ≤ a ≤ 13; see `step` in `py/emap.py`). When both a < 15 is odd and b < 30, the next event is
found by direct simulation.

So when b is odd, a is multiplied by 3/2 and b moves by −5, 0, +8 or +3. When both are even, the smaller number is
subtracted from the larger and a is tripled, and the two swap when b was the smaller. It is a Collatz step mixed with
a step of Euclid's algorithm.

From blank tape: U(4, 3) at step 118, V(4, 14), V(20, 7), V(40, 2), U(10, 37), …, U(100, 7), U(158, 2),
V(10, 155), …, U(74180, 24362) at step 8,744,109,161.

**Halting condition.** The machine halts exactly at U(a, 1) or V(a, 1) with a ≡ 0 (mod 4); the head then reads a 0
in state F. The −5 rule makes b even, so b = 1 can only come out of a subtraction leaving exactly 1, which needs
b ∈ {a−2, a+4, a−7, a−13} (or b = 1 already, carried by an a ≡ 2 step).

**Heuristic.** A halt therefore needs a coincidence of size about 1/a. Iterating the map from 20,000 random starts
at each scale S (a ∈ [S, 2S), b ∈ [0, 2S)) gives halting frequencies 2.0·10⁻², 2.5·10⁻³ and 2.1·10⁻⁴ for
S = 10², 10³ and 10⁴: about 2/S. Along the run a grows exponentially (about 0.1 decimal digits per pass), so the
total chance is dominated by its first terms. It is about 3·10⁻⁵ from the last simulated event and about 10⁻⁹⁶⁶⁰⁰
after the 10⁶ passes iterated. Probviously non-halting.

## What is proved

| level | result | where |
|---|---|---|
| kernel | the halting configurations; no halt in 10⁴ steps | `lean/Blank.lean` (generated) |
| native | no halt in 10⁷ steps | `lean/Blank.lean` |
| kernel | **the map for every even a**: from `Ev F a b` (a even) the machine reaches the event `next F a b` gives, in exactly the steps it gives (`next_sound`); `next` is defined at every event with a even, a ≥ 2, b ≥ 1 except the halting events a ≡ 0 (4), b = 1 (`next_isSome`); every pass takes at least one step (`next_pos`). Axioms propext, Quot.sound | `lean/Map.lean`, `lean/Cases.lean` |
| kernel | blank tape reaches U(4, 3) in 118 steps (`init_U`); **if the orbit of `next` from U(4, 3) never gets stuck, the machine never halts** (`not_halts_of_orbit`); the first 3,000 passes are not stuck: no halt in the first 10⁵⁰⁰ steps (`orbit_3k`, `no_halt_3k`); pass 34 is U(35354, 10986) at step 1,916,511,832, as direct simulation finds (`orbit_34`) | `lean/Orbit.lean` |
| native | the first 10⁵ passes are not stuck: no halt in the first 10¹⁰⁰⁰⁰ steps (`orbit_100k`, `no_halt_100k`) | `lean/Orbit.lean` |
| trusted | the whole map, odd a included: all 7,980 covered starts with a < 60, b < 70 and 300 random starts with 15 ≤ a < 2000 agree with direct simulation, as do 84 starts with odd a < 15 and 30 ≤ b < 3000; the halting events do halt (same grid) | `py/emap.py grid 60 70`, `py/emap.py random 300 1` |
| trusted | the 38 U/V-events of the blank run up to 8.7·10⁹ steps follow the map | `py/emap.py blank 1.2e10` |
| trusted | 10⁶ passes from U(4, 3) without a halt (both numbers then have about 96,600 digits) | `py/emap.py far 1000000` |
| heuristic | P(halt) ≈ 2/a; about 10⁻⁹⁶⁶⁰⁰ after the iterated passes | above |

The map sends even a to even a (every rule's new a is even when a is), so the odd-a rules of the table are never
used from blank tape; they are kept above as checked by simulation only.

### How the map is proved

`py/gen_map.py` writes `lean/Cases.lean`: 32 case theorems, 16 for U and 16 for V. They are a ≡ 2 (4) with b odd;
a ≡ 0 (4) with b odd ≥ 7, b = 3 and b = 5; and a, b even with b ≥ a+4, b ≤ a−2, b = a and b = a+2. Each family has
a generic part (e.g. U(4x+8, 2y+7)) and the few small values of a (or b) below it. A case is a chain: the a block
regrouped into the repeats a loop needs, a segment proved by the symbolic simulator, one loop and the rest of the
way. The loops are `la`, `lb` (a round of the b-odd phase, for a ≡ 2 and a ≡ 0 mod 4: `L (111111)^i 111111 0 C> 111
(1111)^(x+1) 11 0 (11)^y 1` and the like) and `e1`, `e2` (a round of the Euclid phase, a block or b block the
shorter: `L (111111)^i 111111 0 C> (11)^(x+1) 1 0 (11)^(x+y) 11`). Each is proved for one round and iterated by
induction. The loop instance is found by unifying the loop template with the configurations of a symbolic run.
When the run needs `(w)^n w = w (w)^n` to go on, the tape is re-bracketed automatically. The expected next event
comes from `py/emap.py`, fitted linearly at sample points, and Lean checks it. `py/gen_mapdef.py` writes
`lean/Map.lean`: `next` tries the cases in order, recovering x, y from a, b by division, and `next_sound`,
`next_isSome` and `next_pos` follow branch by branch. The chaining framework is
`../1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD/py/chain.py` (with `symtm2.py` there); `lean/Chain.lean` is a copy of
that folder's.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA/lean/check.sh   # about 1 min
cd holdouts/1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA/py
python3 gen_map.py && python3 gen_mapdef.py   # regenerate lean/Cases.lean, cases.json, Map.lean (a few min)
python3 emap.py grid 60 70        # the map against direct simulation (1.5 min)
python3 emap.py random 300 1      # random large starts (2 min)
python3 emap.py blank 1.2e10      # the blank run's events against the map (2.5 min)
python3 emap.py far 1000000       # 10^6 passes (4 min)
python3 emap.py mc 1000 20000     # halting frequency from random starts of size 1000
```

`py/emap.py` uses `../1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---/py/g01tools.py` and its C simulator `c/from.c`.

## Further work

- Non-halting is now the arithmetic statement that the orbit of `next` from U(4, 3) never reaches b = 1 with
  a ≡ 0 (mod 4) (`not_halts_of_orbit`). Nothing short of a Collatz-type argument is in sight.
- A Lean proof that the halting events do halt (a symbolic run from U/V(4x+4, 1) to the F0 transition) would make the
  halting condition an equivalence in Lean.
- The odd-a rules (never used from blank tape) could be proved the same way, with more families.
- A sharper heuristic: the 2/S law could be derived from the exact offsets that produce b = 1.

## Pages

- [`pages/holdouts/1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA/explainer.html`](../../pages/holdouts/1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA/explainer.html)
- [`pages/holdouts/1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA/proof-status.html`](../../pages/holdouts/1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA/proof-status.html)
