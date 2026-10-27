# A lock for the extra-wall loops (October 27)

The question from `HANDOFF.md` (research step 5): does the one-extra-wall loop have a lock like the plain loop's
never-zero countdown L₁ ≡ 3 (mod 7), which every pass divides by 64? The pass P already had one (L₂, ÷64). The
detour Q did not, and mixtures of P and Q were known to have no fixed-point bound ("The general form of the lock"
in the lab notes).

**Short answer.**
- Q has a lock after all. It is quadratic: an integer quadratic D_Q that every Q pass divides by 4096 and that is
  never 0. So a stretch of Q, like a stretch of P or of the plain loop, covers at most two thirds of the halvings.
- Every periodic word in P and Q has a lock of the same kind. Repeating any one word covers at most 4/5 of the
  halvings (checked for all 747 primitive words up to length 12).
- No lock covers all mixtures, and none can: the hand-built P^a Q P^b tapes halt at every width tried. What locks
  still give is a block bound. A halt carried by P/Q passes alone has to change words at least once, and each change
  renews the lock.

All computations here use the proved model (`roundZ`), the Lean theorems below, or exact algebra on the pass maps;
none uses the Python or C simulators with the trailing-wall slip. Files are in this folder (`lock/`).

## Established

### 1. The pass maps P and Q are theorems about the machine

`lean_maps/PassMaps.lean` contains `P_pass` and `Q_pass`. Take every start in the pass's coset (the coset is in
`cosets.json` and comes from the forced run of `../conc/mixsolve.py`), with every gap w1, w2 − w1, …, E − w4 at least
Γ (Γ = 36 for P, 192 for Q). From such a start the machine runs (`steps`) to the round start computed by
`roundsZ 1000 8`, and the walls there are exactly

- P: 64w1' = w2 + w3 + 271, 64w2' = w2 + 5w3 + 12w4 + 16E + 899, 16w3' = w3 + 4w4 + 11E + 358, 16w4' = w4 + 15E + 369, E' = E + 24;
- Q: 128w1' = w2 + 514, 128w2' = 9w2 + 4w3 + 16w4 + 32E + 1710, 32w3' = 2w2 + w3 + 6w4 + 22E + 701, 16w4' as P, E' = E + 24.

The eight shapes of each pass are checked too (`P_shapes`, `Q_shapes`). No splits were needed.
- `PassMaps.lean` is evaluated by Lean's kernel (`decide +kernel`), so `P_pass` and `Q_pass` depend only on `propext`,
  `Classical.choice` and `Quot.sound`; it checks in about 6 s (4 minutes before the sign test went through a checked
  cone inverse, October 27; a `native_decide` copy is no longer needed). See `lean_maps/kernel_check.out`.
- Run `cd lean_maps && ./check.sh`, after building `../lean` with `./check.sh` there.

`verify_maps.py` (output `verify_maps.out`) also runs 10 coset points of each of 11 words (P, Q, PP, PQ, QP, QQ, PQQ,
QPQ, PPQP, QQQQ, PQPQP) at width 2^200 through the proved model. It uses `Harness.lean`, a thin I/O wrapper around
`roundZ`. Every shape and every position agrees with the composed maps.

### 2. The lock of Q

Only w2, w3, w4 and E matter, since both maps forget w1. Q's left block (w2, w3) is (1/128)·[[9, 4], [8, 4]]. Its
eigenvalues (13 ± 3√17)/256 are irrational, so no linear form can be a countdown. The product of the two conjugate
eigenforms can:

    D_Q = −58529536E² + 88773450E·w2 − 82739064E·w3 + 155524704E·w4 − 148647028E − 12044232w2² + 7527645w2·w3
          − 85313310w2·w4 − 9620823w2 + 6022116w3² + 68250648w3·w4 + 51198954w3 − 91000864w4² + 105148876w4 + 78740446

(`DQ.txt`, derived in `qlock_derive.py`). Proved in core Lean (`lean_maps/DQ.lean`, no compiler trust):
- `D_Q`: 4096·D_Q(Q x) = D_Q(x) for every integer x whose Q image is integral;
- `D_ne_zero`: D_Q(w2, w3, w4, E) ≠ 0 for all integers. D_Q is 17 times a square minus a square, up to a factor
  (`D_AB`). Zero would need both forms to vanish, and that forces 1505529·w2 = 7345640E − 6691240w4 − 2176218, which
  is impossible mod 409.

**Consequence** (two lines on paper, not in Lean). A run of n Q passes between integer states has
D_Q(x_n) = D_Q(x_0)/4096^n, a nonzero integer, so 2^(12n) ≤ |D_Q(x_0)| ≤ 2^30·E². Each pass divides R = E − w4 − 1
by 16, so the stretch makes **at most (2/3)·log₂E + 10 halvings**, the same two thirds as P and the plain loop. Along
a Q stretch, 3·log₂R − log₂|D_Q| is constant, the analogue of the plain loop's 3·log₂R − 2·log₂|L₁|.

This corrects the notes on two points:
- "The detour is a second pass type" says Q "has no dyadic left countdown at all". That is true of linear forms, but
  Q has a quadratic one.
- The fixed-point argument ("The general form of the lock") bounds a Q stretch only by Q's slowest real eigenvalue,
  2^−3.34 per pass. That allows 1.2·log₂E halvings, more than a halt needs. The norm form uses both 2-adic factors,
  2^−7 and 2^−5, at once.

### 3. Every periodic word has a lock, and covers at most 4/5 of the halvings

`periodic_locks.py`, output `periodic_locks_12.txt`. For any word w with n_P letters P and n_Q letters Q (length
ℓ), the composite map's characteristic polynomial is

    (λ − 1)² (16^ℓ λ − 1) q(λ)

The factor q(λ) belongs to the two left directions. Its determinant is exactly 2^−B, with B = 10n_P + 12n_Q.
- When q is irreducible, the norm form D_w of its two eigenforms is an integer quadratic with D_w∘w = 2^−B·D_w
  (`word_height.py` builds it by linear algebra and checks the identity).
- D_w vanishes only where two rational forms vanish together. Whether that happens at an integer point is decided
  exactly (`zsolve.py`).
- Repeating w n times then needs 2^(Bn) | D_w(x₀) ≠ 0. The stretch makes at most (8ℓ/B)·log₂E + 4ℓh_w/B halvings,
  where h_w = log₂(sum of D_w's coefficients) is a constant of the word.

Results for all 747 Lyndon words of length 1 to 12:
- Except P, every word has an irreducible q, and its D_w is **never 0 on any integer point**, not only on the tape's
  parity class. P is the rational case: L₂ (6 bits) is its lock, and its other left root, 1/16, is R's Jordan partner.
- The rate 8ℓ/B is at most 4/5 for any word. The largest found is 48/61 = 0.787, for P¹¹Q. P and Q have 2/3, and
  rates approach 4/5 only for P^kQ with k large.
- The fixed-point argument would give more than 1 for every word with a Q in it (largest 1.199, for Q), so it locks
  none of them. The norm forms lock all of them.

So **no single repeated word can carry a halt** on a wide tape: it falls at least a fifth of log₂E short.

### 4. No lock covers all mixtures

There are three separate facts.
- **No common countdown.** The only polynomials f of degree ≤ 3 with f∘P = λf and f∘Q = μf are 1, R, R² and R³
  (`common_inv.py`, outputs `common_inv2.out` and `common_inv3.out`). R cannot be a lock, since R → 0
  is the halt itself.
- **A word's own lock is empty unless the word is a power** (`word_height.txt`). For a power the height stays fixed:
  h(u^n) = h(u) (Q^n: 30, (PQ)^n: 60.6, (PPQ)^n: 88.0), so h/B → 0 and the bound is real. For aperiodic words
  (P^aQP^b, and random words of length 4 to 48), h ≈ 2.4 to 2.6·B. The bound B ≤ 2·log₂E + h then says nothing.
  This is the quantitative form of "the denominators grow with the word".
- **Mixtures really halt.** The hand-built tapes of "Halting at every scale" were rebuilt with the same construction
  (`mixed_halt_lean.py`, output `mixed_halt_lean.out`). For K = 16, 17, 20, 24, 32, 56, 100 and 200, the proved
  model follows the word P^aQP^b round for round to the endgame. Its last round is `uncovered`, the contact where
  the packet meets the block next to the end, which the mark rules do not cover. The bare transition table (`tm.c`,
  no marks or rules; output `tm_k16_17.out`) halts the K = 16 and K = 17 tapes after 15,940,135,477 and
  61,437,118,279 steps, exactly the counts in the notes.

  So take any integer-valued, never-zero F with |F| ≤ C·E^g that every P and every Q pass shrinks by at least 2^c.
  It would bound a P^aQP^b run to (4g/c)·log₂E + O(1) halvings. These tapes need about log₂E − 3.6 halvings at every
  width from 2^16 to 2^400, so 4g/c ≥ 1 − O(1/K): such an F cannot lock anything.

### 5. What the locks do give: a block bound

Split an extra-wall run in P and Q into maximal blocks, each a power of one primitive word. By 2 and 3, each block
covers at most 4/5·log₂E + O(1) halvings: 2/3 for P and Q blocks, with constants from the word's height. A halt from
a wide tape that uses only P and Q passes therefore **changes words at least once**. The change renews the lock. On
the 2^200 tape the notes record L₂ falling to 2^61.8 at the end of the first P block and jumping back to 2^203.2
after the single Q.

## Conjectured or open

- **Periodic words of any length.** The rate is at most 4/5 whenever the word's norm form never vanishes. Beyond
  length 12 the never-zero condition is checked only for the 40 sample words in `word_height.txt` (lengths up to
  48). No general reason has been found, like the fixed modulus 7 for L₁ or 409 for D_Q.
- **The full extra-wall alphabet.** The endgame search `../conc/endsym2.py` reaches closes through pass variants
  that are neither P nor Q, each also dividing R by 16. The method here applies to any variant whose map is
  affine (compose, factor, take the norm form), but the variants have not been listed or checked.
- **More extra walls** (k ≥ 2, `../conc/loopfamily.py`): their pure loops have linear locks. Their detours and
  mixtures have not been looked at with norm forms.
- **What limits mixtures on the machine's own tapes** is 2-adic, not a lock. GMM states have two free numbers, and
  each family has a cap on extra-wall passes (lab notes, "The extra-wall loop needs three free numbers"). That
  remains measured, not proved. Turning it into a statement that each change of word costs a fixed number of
  digits on two-number families is the natural next step.

## Files

| file | what it does |
|---|---|
| `passmaps.py` | the P and Q maps as exact rationals |
| `Harness.lean`, `verify_maps.py` | run starts through the proved `roundZ`; compare with composed maps (`verify_maps.out`) |
| `lean_maps/` | `PassMaps.lean` (P_pass, Q_pass; kernel-checked, no compiler trust), `DQ.lean` (D_Q identity and never-zero), `gen_passmaps.py`, `check.sh` |
| `qlock_derive.py`, `DQ.txt` | derivation of D_Q and its zero set |
| `periodic_locks.py`, `periodic_locks_12.txt` | locks and rates for all Lyndon words to length 12 |
| `word_height.py`, `word_height.txt` | the norm form of any word, its height, never-zero check |
| `zsolve.py` | integer solvability of linear systems (for never-zero checks) |
| `common_inv.py`, `common_inv*.out` | common eigen-polynomials of P and Q |
| `mixed_halt_lean.py`, `mixed_halt_lean.out`, `k16_17.txt`, `tm.c`, `tm_k16_17.out` | the hand-built mixed halts, on the proved model and on the bare machine |
