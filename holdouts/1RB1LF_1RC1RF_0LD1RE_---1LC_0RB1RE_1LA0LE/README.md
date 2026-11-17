# 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE

bbchallenge id 21883. A BB(6) holdout whose halting from blank tape is open. Family: **doubling map with a growing modulus (odd-pool events)**. Decision: **open** (proved in Lean: it halts iff its right-end map reaches T(none, 1, b), and iff the doubling map in (u, v) below, odd pools and brackets included, reaches an odd pool 2^(k+2) − 2k − 3 without a bracket; no halt in 10^11 operations of the exact map, about 5·10^10 right-end visits; heuristically a later halt has probability of order 10^-11).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LF |
| B | 1RC | 1RF |
| C | 0LD | 1RE |
| D | --- | 1LC |
| E | 0RB | 1RE |
| F | 1LA | 0LE |

## What it does

At every visit of the right end in state B the tape is

    T(c, a, b) = 0^∞ [1^2 0 (10)^c] 1^a 0 (10)^b B>0 0^∞      (the bracket [...] present or not)

a *pool* of a 1s, a block of b pairs, and sometimes a *bracket* to the left. The run reaches T(none, 2, 0) at step 7.
The map from one visit to the next is now complete (`py/model.py`, function `step`; proved in Lean as `F` in
`lean/Map.lean`, and in the arithmetic form below as `op` in `lean/Doubling.lean`); it has three parts.

**1. An even pool: a doubling map.** The bracket is not touched. With u = b + 2 and v = a/2 + b + 3:

    2u < v     next visit T(c, a − 2b − 2, 2b + 2):    u ← 2u,      v ← v + 1
    2u > v     carry (no visit in between):            u ← 2u − v,  v stays     (as if at T(c, 2a + 2, b − a/2 − 1))
    2u = v     next visit T(c, 2v − 3, 0): the pool becomes odd

So u is doubled modulo v again and again, and the modulus v grows by one at every doubling that does not wrap.
Nothing else happens until the doubling lands exactly on a multiple of v.

**2. An odd pool.** From T(c, A, 0) the pair block doubles (b = 0, 2, 6, 14, …, the pool loses 2b + 2 each time)
until the pool cannot pay. Then, without a bracket, what the sweep has built stays behind as a new bracket and the
pool restarts as `1^2` (even); with a bracket, the bracket is unwound and merged into the pool (even, no bracket).

**3. Halting.** The only halting visits are T(none, 1, b) (`halt_T1` in Lean, for every b). An odd pool without
bracket always starts as T(none, A, 0), and it comes down to exactly 1 if and only if

    A = 2^(k+2) − 2k − 3  for some k:   1, 3, 9, 23, 53, 115, 241, 495, 1005, 2027, …

Since A = 2v − 3 at an event, **the machine halts iff, at a time with no bracket, the doubling map hits 2u = v with
v = 2^(k+1) − k**. (Two rarer sources of an odd pool without bracket: a merge that ends exactly as the tail runs
out gives T(none, 2c + p + 9, 0), which could also be a halting pool; an odd pool that overflows with a = 2b + 1 gives
T(none, 2a + 5, 0) = T(none, 2^(K+3) − 1, 0), which never is.) Example: T(none, 12, 19) → T(none, 53, 0) →
(51, 2) → (45, 6) → (31, 14) → (1, 30) → halt, so halting configurations of this form exist; the question is only
whether the run from blank tape ever meets one.

## The recursion in rule form

As the bbchallenge wiki writes Antihydra's: exact tapes, then rules with exact step counts. At a visit of the right end
in state B (subscript c: a bracket 1^2 0 (10)^c to the left; no subscript, no bracket):

    E_c(u, v) := 0^∞ 1^2 0 (10)^c 1^(2(v−u−1)) 0 (10)^(u−2) B> 0^∞     (even pool)
    O_c(A, b) := 0^∞ 1^2 0 (10)^c 1^A 0 (10)^b B> 0^∞                  (A = 2i + 3 odd)

    0^∞ A> 0^∞            --7-->                     E(2, 4)
    E_c(u, v)             --6u²-->                   E_c(2u, v + 1)                 2u < v
    (u, v)                --6d² − 4d + 2-->          (2u − v, v)                    2u > v, d = v − u (no visit)
    (u, v)                --6u² − 4u + 5-->          O_c(2v − 3, 0)                 2u = v
    O_c(2i+3, b)          --6(b + 2)²-->             O_c(2i − 2b + 1, 2b + 2)       b < i
    O(2i+3, i)          --6(i + 2)²-->             O(1, 2i + 2)
    O(1, b)             --2b + 7-->                HALT
    O_c(2i+3, i)          --6(i + 2)²-->             E(c + 2i + 5, c + 2i + 7)    bracket c
    O(2i+3, i+1)        --6i² + 44i + 78-->        O(4i + 11, 0)
    O(2i+3, i+2)        --6i² + 36i + 59-->        (2i + 6, 2i + 8), no bracket   (no visit)
    O(2i+3, i+r)        --6i² + 36i + 58-->        (r − 2, r), bracket 2i + 4     r ≥ 3 (no visit)
    O_c(2i+3, i+1)        --6i² + 32i + 4c + 51-->   O(2c + 4i + 11, 0)           bracket c
    O_c(2i+3, b)          --6i² + 32i + 4c + 48-->   (b − i − 1, c + i + b + 6)     bracket c, b ≥ i + 2 (no visit)

A bare pair (u, v) is not a visit: the next rule applies to it directly and the step counts add up. The rules are
`op` of `lean/Doubling.lean`, proved, with the halts-iff. The step counts are proved for the tape moves they are
built from (`lean/Rules.lean`); the totals are sums of those, checked against direct simulation (`py/model.py rules`:
7,640 tapes and every visit of the first 3·10^6 steps), not yet stated in Lean. Example: E(21, 28) = T(none, 12, 19)
halts after 268 + 1125 + 24 + 96 + 384 + 1536 + 67 = 3,500 steps.

## Inside one step

Between two visits the machine is in configurations `… 1^x 0 [A>1] 1^p tail`: pool 1^x, middle block 1^p, and a
tail `0 (10)^z 1` worth w = z + 2 rounds. One round is (x, p, w) → (x − 2, p + 4, w − 1); when the tail is used up
(w = 0) the middle block becomes the new pair block: T(x − 2, p/2 + 1). When the pool is down to `1^2` first, the
middle block becomes the new pool, (2, p, w) → (p + 4, 2, w − 2): the carry. Pool and tail running out together
(w = 0 at x = 2) gives T(p + 3, 0), an odd pool. Each of these moves is a Lean theorem (`lean/Rules.lean`).

## The run

`c/fast.c` is `step` in C. In 10^11 operations (doublings and carries; 50,000,005,600 visits; a/2 + b reaches
5.0·10^10, which by steps ≈ (a/2 + b)^3/3 is of the order of 10^31 machine steps; the simulator does not count
steps) there are 35 odd-pool events, 18 of them without bracket, and no halt. The 18 pools:

    5, 13, 165, 989, 1853, 13309, 26333, 44669, 49909, 19855861, 169438117, 283866789, 1487681501, 1992437437,
    3603147421, 10918121213, 46694013501, 51055443101

All are ≡ 5 (mod 8) (an event after at least one carry has v ≡ 0 mod 4), which rules out the targets with
k ≢ 0 (mod 4) for such events but not the others (53, 1005, 16357, …). The closest call was 989 against 1005
(v = 496 against 504). Events with a bracket repeat earlier pools (165, 13309, 26333, … appear twice or three times):
after a bracket forms, the right part restarts from a small seed (u = v − 2) and different seeds fall into the same
orbit of the doubling map.

## Status

* **Lean, kernel: the machine halts from blank tape iff the right-end map reaches T(none, 1, b)**
  (`lean/Map.lean`, `halts_iff_T1`; also `halts_iff`: iff the orbit of T(none, 2, 0), step 7, under the map `F`
  reaches `none`). `F` works on nodes: the visits T(c, a, b), and one more node for the fresh sweep that a pool of a
  single 1 without bracket starts at w = 1 (no visit comes in between). Inside a sweep `inner` follows the
  configurations `Cs c x n w` = `0^∞ [br] 1^x 0 A> 1 (11)^n tail_w` move by move: rounds, the end of a sweep, the
  carry at a pool of two (and at w = 3, 2), the even and odd events, the bracket an odd pool leaves behind (w ≥ 5,
  4, 3, 2), the merge of a pool of three into the bracket (w ≥ 3, 2, 1), the pool of one at w = 1 and w = 0. Each
  move is a theorem for all parameters (`m_*`, from `lean/Rules.lean`, which `py/rules.py` now generates with 15
  more rules in these forms), and `F_sem` assembles them. The axioms are `propext`, `Classical.choice`, `Quot.sound`.
* **Lean, kernel: the doubling map, a layer above `F` (`lean/Doubling.lean`).** `op` works on even states
  `ev c u v` and odd pools `od c A b` (the visit T(c, A, b), A = 2i + 3; one operation is one whole odd sweep):

      ev:  2u < v → ev c (2u) (v+1);   2u > v → ev c (2u−v) v;   2u = v → od c (2v−3) 0
      od:  b < i → od c (A−2b−2) (2b+2);   b = i → od none 1 (2b+2) (halt next) or, with bracket c,
           ev none (c+2b+5) (c+2b+7);   b = i + r, no bracket: r = 1 → od none (2A+5) 0, r = 2 → ev none (A+3) (A+5),
           r ≥ 3 → ev (some (A+1)) (r−2) r;   with bracket c: r = 1 → od none (2c+2A+5) 0, r ≥ 2 → ev none (r−1) (c+i+b+6)

  A visit with even a is `ev c (b+2) (a/2+b+3)`, inside a sweep `Cs c (2i+2) (2j+1) w` is `ev c (j+w+2) (i+2j+w+4)`
  (a round does not move it, a carry is one operation). `F_op`: every move of `F` is one or more operations of `op`.
  `halts_iff_op`: the machine halts from blank tape iff `op` from `ev none 2 4` (the visit at step 7) halts.
  `halts_iff_pool`: iff the orbit reaches `od none A 0` with A = 2^(k+2) − 2k − 3 (`pool_run` does the odd pool's
  doubling for every k, and `back` traces any halting visit back to the pool it started as). `pool_sources`: such a pool
  comes from an event 2u = v without bracket (and `event_pool`: 2v − 3 is a halting pool iff v = 2^(k+1) − k), from an
  odd pool that overflows by one (2A + 5), or from a merge that ends with the tail (2c + 2A + 5). The first 10^4
  operations (kernel) and 10^7 (`native_decide`) do not halt. Axioms `propext`, `Classical.choice`, `Quot.sound`. This
  makes the page's simple rule a proved halts-iff; `py/model.py` and the C runs remain the fast way to follow it.
* Lean: the first 100 nodes of the orbit do not halt (kernel), and the first 10^4 (`native_decide`).
* Lean, kernel: T(none, 1, n) halts for every n (`halt_T1`).
* Trusted (now superseded for `step` itself by the Lean map): `step` against direct simulation on 13,728 configurations (c ∈ {none, 0, 1, 2, 3, 4, 7, 10}, a < 40,
  b < 44), on every visit of the first 3·10^6 steps (`py/model.py check`) and on all 2,066 visits of the first
  3·10^9 steps (`py/model.py checkrec`); the doubling-map form and the list of halting pools against `step`.
* Trusted: `c/fast.c` prints the same first 20,000 visits as `py/model.py` (they include 13 odd events); 10^11
  operations without a halt.
* Lean (`lean/Blank.lean`): the halting configurations, no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* Heuristic: the map stays at a modulus v for about two operations, and each hits 2u = v with chance about 1/v, so
  a halt at the target v = 2^(k+1) − k has chance about 2^-k; the targets not yet passed start at k = 36, which
  gives about 10^-11 in total. The modulus is not monotone (a merge makes it jump, a new bracket restarts the right
  part at a small one, but those phases have a bracket and cannot halt), so this is an estimate, not a bound.
* Why no congruence helps (round 11). Write D = v − u. At a fixed modulus the carries double D, and the doubling
  that does not wrap is D ↦ 2D − (v − 1) with v ↦ v + 1; an event is D = v/2. So an event at modulus v needs the
  value of D on arrival at v to be v/2^i with 2^i dividing v: every event after the first arrival has 4 | v (this
  is the mod 8 fact above), and a target v = 2^(k+1) − k needs D = v/2^i with i ≤ ν₂(k). Backwards, (D, v) has
  two predecessors when D and v are even, none when D is odd and v even, and one otherwise: a critical branching
  process again, as for 1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC, so the states that reach a given target thin out
  like 1/v without any residue class being excluded.
* Open: whether an event ever falls on a target. The doubling map with a moving modulus is chaotic; no invariant
  that excludes the targets was found (mod 8 excludes three targets in four), and none is expected.

## Next steps

* Done (17 November 2026): the arithmetic layer, `lean/Doubling.lean` (see Status).
* Prove in Lean that the pool 2A + 5 never halts (the README's argument: an odd pool that overflows by one is
  2^(K+3) − 1), so that only events and merges remain as sources of halting pools.
* A faster simulator: k doublings at once are one multiplication by 2^k and one division by v with a small
  correction (the modulus moves by at most k), valid when the remainder is not near 0; this would give about 10^13
  operations and, with exact step counts added, a halting step if one is ever found.
* Describe the set of moduli v at which seeds u = v − 2 produce an event (4, 8, 12, 16, 32, 44, 48, 64, 84, 96,
  104, 112, 128, 496, …; many seeds share one): if it could be shown to miss 2^(k+1) − k, the bracketed phases
  would be understood, though not the phases after a merge.

## Mirror partner

Mirrored, with D and E swapped, the table of `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD` differs from this one only in the direction of A0. The two
pass maps agree while the pool is even and part only at odd events, the only places where either machine can halt.
After a parting, the runs become the same run again, a few passes apart. But the two lists of odd events are not the
same, and Lean (`together_forces_halts` in
`holdouts/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/lean/Partner.lean`) finds two pairs of mirror-image tapes where
one machine halts and the other rejoins its own run from blank tape. So whether the two halt together depends on their
runs from blank tape, not on their tables. Details are in `holdouts/EQUIVALENCES.md`.

## Pages

- [`pages/holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/explainer.html`](../../pages/holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/explainer.html)
- [`pages/holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/proof-status.html`](../../pages/holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/lean/check.sh
cd holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE
python3 py/rules.py                     # regenerates lean/Rules.lean (lean/Map.lean is by hand)
python3 py/model.py check               # the map against direct simulation
python3 py/model.py rules               # the rule table and its step counts against direct simulation
gcc -O2 -o /tmp/rec c/rec.c && /tmp/rec 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE 3000000000 R B 10000000 | python3 py/model.py checkrec
gcc -O2 -o /tmp/fast c/fast.c
/tmp/fast 1000000000 dump 20000 | cmp - <(python3 py/model.py dump 20000)     # C against Python
/tmp/fast 100000000000                  # 10^11 operations, about 12 minutes: the odd events, no halt
```
