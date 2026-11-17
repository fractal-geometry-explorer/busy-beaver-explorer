# 1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC

bbchallenge id 50923. A BB(6) holdout whose halting from blank tape is open. Family: **three-wheel odometer = doubling map with a growing modulus**. Decision: **open** (proved in Lean: it halts iff the doubling map below halts; no halt in 10^11 operations of that map, 54 resets; heuristically a later halt has probability about 10^-10).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 0LC | 0RE |
| C | 1LF | 1LD |
| D | 1LA | 0LA |
| E | 1LC | 1RB |
| F | --- | 1LC |

## What it does

At every right-end visit in state B the tape is

    S(c, a, b) = 0^∞ (10)^c 1^a 0 (10)^b 1 B>0 0^∞        (a even, a ≥ 2)

and the next one is (`py/model.py`, `step`):

    2b < a           -> (c, a − 2b, 2b + 1)                         fast wheel: (10)^b doubles, eating 1s
    2b ≥ a, c ≥ 1    -> rule at (c − 1, 2a + 4, max(b − a/2 − 1, 0))  carry: a 10 of the left block becomes 1s
    2b ≥ a, c = 0    -> halt if b = a/2, else rule at (a, 4, b − a/2 − 1)   reset: the pool becomes the left block

The run reaches S(0, 4, 1) at step 43.

## The same thing as a doubling map

Put u = b + 1 and v = a/2 + b + 2. Then one operation (a doubling step or a carry) is (`py/model.py`, `op`):

    2u < v           u ← 2u,      v ← v + 1                        a visit
    2u > v, c ≥ 1    u ← 2u − v,  v ← v + 1,  c ← c − 1            carry
    2u = v, c ≥ 1    u ← 1,       v ← v + 2,  c ← c − 1            carry that empties the fast wheel
    2u > v, c = 0    c ← 2(v − u − 1),  u ← 2u − v,  v ← u + 3     reset
    2u = v, c = 0    halt

So the machine doubles u modulo v, the modulus grows by one at every operation, and the left block c only counts the
wrap-arounds: c of them are allowed, and the next one is a reset. **It halts iff a reset happens with 2u = v
exactly.** One conserved quantity: v + c = 5 + visits + resets + emptying carries, so v at a reset is the number of
visits so far plus a small number (90 at reset 51).

A reset finds 2u − v anywhere between 0 and v; the new left block is c = v − (2u − v) − 2, the new modulus 2u − v + 3,
and the next reset comes about 2c operations later, at a modulus near v(3 − 2x), x = u/v ∈ [1/2, 1). The moduli at
resets therefore grow by a factor between 1 and 2 (on average e^0.386 ≈ 1.47): reset k needs about 1.47^k
operations, and this is why the reset count grows only logarithmically with the work (54 resets in 10^11 operations;
thousands of resets are out of reach of any step-by-step method, and the doubling map with a moving modulus has no
known shortcut).

## The recursion in rule form

Exact tapes, then rules with exact step counts, as the bbchallenge wiki writes Antihydra's. The Lean proof works on
the sweep of `lean/Map.lean`, one level below the doubling map, so the table does too (Lean: `S c p b` with
a = 2p + 2, and `Rc c p k z`):

    S(c, a, b)    := 0^∞ (10)^c 1^a 0 (10)^b 1 B> 0^∞                    (a visit; a even, a ≥ 2)
    R(c, p, k, z) := 0^∞ (10)^c 1^(2p) A> 1 0 1^(4k+1) 0 (10)^z 1111 0^∞   (inside a sweep)

    0^∞ A> 0^∞              --43-->        S(0, 4, 1)                 blank_to_S
    S(c, a, 0)              --24-->        S(c, a, 1)                 start0
    S(c, a, n + 1)          --4n + 22-->   R(c, a/2 − 1, 0, n)        start_g
    R(c, p + 1, k, z + 1)   --8k + 8-->    R(c, p, k + 1, z)          round
    R(c, p + 1, k, 0)       --12k + 18-->  S(c, 2p + 2, 2k + 3)       final_g
    R(c + 1, 0, k, z + 3)   --12k + 22-->  R(c, 2k + 2, 1, z)         carry
    R(c + 1, 0, k, 2)       --12k + 32-->  S(c, 4k + 6, 3)            carry_z2
    R(c + 1, 0, k, 1)       --12k + 20-->  S(c, 4k + 8, 1)            carry_z1
    R(c + 1, 0, k, 0)       --12k + 36-->  S(c, 4k + 8, 1)            carry_z0 (the emptying carry)
    R(0, 0, k, z + 2)       --12k + 20-->  R(2k + 2, 1, 0, z)         reset
    R(0, 0, k, 1)           --12k + 26-->  S(2k + 2, 4, 1)            reset_z1
    R(0, 0, k, 0)           --16k + 31-->  HALT                       halt_run (16k + 30), then F reads 0

Every step count is a Lean theorem for all values of its counts (`blank_to_S` in `lean/Map.lean`, the rest in
`lean/Rules.lean`; the halt row adds the halting transition). `lean/Map.lean` rewrites the moves onto S and R and
proves `halts_iff`: the machine halts iff these rules, from S(0, 4, 1), reach the halt row (its `Reach` statements
keep the tapes, not the counts). `lean/Doubling.lean` turns them into the doubling map on
(c, u, v) = (c, b + 1, a/2 + b + 2). Checked against direct simulation (`py/model.py rules`): each rule on 3,740
tapes, rule chains from 2,856 visits to the next visit or halt (28 halting), and all 377 visits of the first 10^7
steps of the run at the predicted step. A doubling (2b < a) takes 4b² + 12b + 24 = 4u² + 4u + 16 steps. Example:
S(1, 2, 6) → R(1, 0, 0, 5) (42) → R(0, 2, 1, 2) (carry, 22) → R(0, 0, 3, 0) (rounds, 16 + 24) → halt (79):
183 steps, as in direct simulation.

## The run

`c/odo.c` is `op` in C. In 10^11 operations (50,000,165,924 visits) there are 54 resets and 42 emptying carries, and no
halt; the last resets:

    reset 50: v = 7,978,846,065    2u − v = 4,575,522,867     new left block 3,403,323,196
    reset 51: v = 11,382,190,134   2u − v = 763,144,354       new left block 10,619,045,778
    reset 52: v = 22,001,393,633   2u − v = 20,665,750,627    new left block 1,335,643,004
    reset 53: v = 23,337,087,556   2u − v = 11,530,783,676    new left block 11,806,303,878
    reset 54: v = 35,143,437,691   2u − v = 1,095,845,857     new left block 34,047,591,832

The smallest (2u − v)/v at a reset so far is 0.028 (reset 11: v = 677, 2u − v = 19); a halt needs 0. The tape is then
about 6·10^10 cells long; a visit costs of the order of v² machine steps, so the run is far beyond 10^30 steps
(an estimate; the simulator does not count steps).

## Status

* **Lean, kernel: the machine halts from blank tape iff the doubling map halts** (`lean/Doubling.lean`,
  `halts_iff_op`):

      HaltsFromBlank ↔ ∃ n, opIter n (0, 2, 5) = none

  where `op` is exactly the five-line map above on (c, u, v). Nothing about the run is assumed; the axioms are
  `propext`, `Classical.choice`, `Quot.sound`. The proof has two layers:
  * `lean/Map.lean`, `halts_iff`: the machine halts iff the orbit of the visit S(0, 4, 1) (step 43) under the visit
    map `F` reaches `none`. `F` is the sweep of the odometer with its rounds, carries and resets, as a structural
    recursion (`inner`); `F_sem` proves each value of `F` on the tape, for every visit, from the rules of
    `lean/Rules.lean`. That file (generated by `py/rules.py` with `bbtools.symtm`) now also has the six boundary
    rules the assembly needed: `start_g` and `final_g` (pool of two), `carry_z2`, `carry_z1`, `carry_z0` (the
    emptying carry), `reset_z1`.
  * `lean/Doubling.lean`, `F_op` and `orbit_op`: pure arithmetic. A visit S(c, 2p+2, b) is the state
    (c, b + 1, p + b + 3) of `op`, a configuration inside a sweep is the state it will reach once the current doubling
    is done; a round does not move it, a carry or a reset is one operation. So one step of `F` is one or more
    operations of `op` and `F` halts exactly when `op` does.
* Lean: no halt in the first 10^4 operations of `op` (kernel, `op_kernel`) and 10^7 (`native_decide`, `op_native`).
* Trusted: the rule against direct simulation for c < 6, even 2 ≤ a < 30, b < 34 (2,856 configurations) and on every
  visit in the first 3·10^6 steps; the doubling map against the rule on the first 200,000 visits of the run
  (`py/model.py check`). These checks are now superseded by the Lean proof.
* Trusted: `c/odo.c` prints the same first 50,000 visits as `py/model.py`, and the same resets as
  `py/model.py resets` (reset 38: left block 44,140,926); 10^11 operations, 54 resets, no halt.
* Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* Heuristic: at a reset 2u − v is one of about v/2 values and one of them halts; the moduli at resets grow
  geometrically, so the chance of a halt after reset 54 is about 6/v ≈ 10^-10.
* Open: whether a reset ever hits 2u = v (that is b = a/2). There is no congruence obstruction: the halting state
  (u, v) = (v/2, v) has predecessors under the map for every even v, and the state after a reset is not constrained
  beyond v = u + 3.

## Structure of the map (round 11)

What the map does not allow one to say, and why. None of this is a proof of non-halting.

* **Every lap starts at the same place.** A reset sets v = (2u − v) + 3 and u = 2u − v, so every lap begins at
  u = v − 3, and its left block c and modulus v satisfy c + v = V + 1, where V is the modulus at the reset. A lap is a
  function of its starting modulus alone: the orbit of (v − 3, v) under the doubling map. The halting question is a
  question about a two-dimensional map (v, c) ↦ (v', c') on laps: the lap halts iff the (c + 1)-th wrap-around of the
  orbit of (v − 3, v) is exact (2u = v).
* **The wrap-arounds are binary digits.** Between two exact hits, u_s / 2^s − u_(s+1) / 2^(s+1) = ε_s m_s / 2^(s+1)
  with ε_s = 1 at a wrap-around and m_s = m_0 + s, so u_0 = Σ ε_s (m_0 + s) / 2^(s+1). Writing x = 0.ε_0 ε_1 ε_2 … in
  binary, u_0 = m_0 x + Σ_j ε_j j / 2^(j+1), so |m_0 x − u_0| ≤ 1: the pattern of carries is the binary expansion of
  a real number within 1/m_0 of u_0 / m_0, and an exact hit at operation n means that the expansion from position n
  starts with a 1 followed by about log₂ v zeros, to the exact integer. Deciding the machine is deciding where an
  explicit, implicitly defined binary expansion has such patterns: a normality-type question with no known method.
* **No congruence can exclude the halt.** Going backward one operation from (u, v): if v is even there is exactly
  one predecessor (u/2 if u is even, (u + v − 1)/2 if u is odd); if v is odd there are two when u is even and none
  when u is odd. So the backward tree of the halting states is a critical branching process (one predecessor on
  average), and the set of states that halt within a lap has density of order 1/v. This is the heuristic of the next
  bullet, now with a reason. It also leaves no room for an invariant modulo a power of 2: every class of (u, v, c)
  modulo 4 (64 classes) contains a halting state with v ≤ 16, and every class modulo 8 (512) one with v ≤ 85
  (search with unlimited credit, halting meaning an exact hit at the (c + 1)-th wrap-around).
* **The chance of a halt.** At a reset the modulus is V and 2u − V is spread over about V/2 values, one of which halts;
  V grows by about 1.47 per lap, so the remaining chance after lap 54 is about 2/(V (1 − 1/1.47)) ≈ 6/V ≈ 2·10^-10.

## Next steps

* A faster map: k operations at once are u ← 2^k u − Q v − R with Q = ⌊2^k u / v⌋ and R a table lookup in the bits of
  Q, valid when 2^k u mod v ≥ k·2^k (no intermediate value near 0) and at least popcount(Q) carries are left; with
  k ≈ 24 this is about ten times faster, worth about six more resets. It does not change the picture.

## Pages

- [`pages/holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/explainer.html`](../../pages/holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/explainer.html)
- [`pages/holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/proof-status.html`](../../pages/holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/proof-status.html)

The explainer's hand-written sections are `page/*.html`: one interactive picture per level of description (the tape
at its visits, the odometer, the doubling map, the laps) and the final definition. `python3 py/page.py` copies them
into `status.json`; `python3 holdouts/build_pages.py` then rebuilds the pages.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/lean/check.sh
cd holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC
python3 py/rules.py                     # regenerates lean/Rules.lean (Map.lean and Doubling.lean are by hand)
python3 py/model.py check
python3 py/model.py rules               # the rule table and its step counts against direct simulation
python3 py/model.py resets 1e8
gcc -O2 -o /tmp/odo c/odo.c
/tmp/odo 1000000000 dump 50000 | cmp - <(python3 py/model.py dump 50000)     # C against Python
/tmp/odo 100000000000                   # 10^11 operations, about 8 minutes: the resets, no halt
```
