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
- **The open cases do not use the extra-wall loop** (section 6, added in the evening). Of the clean-tape classes that
  `blank_halt_pass` leaves open (1,255,963 at 36 digits), 0.09% meet an extra-wall pass start anywhere on their path;
  of the pass-start trees' open measure at 20 splits, under 1%. So no lock for these loops, of any form, can settle
  either case.
- **What keeps two-marker runs open** (section 7, added at night): they are words in about 14,000 exact return pieces
  (from one two-marker state to the next), which either halve the marker's gap or reset the marker into the tape. Each
  piece repeated is bounded (every reset has a never-zero countdown; the eight largest pieces and their countdowns are
  now Lean theorems), but the countdowns differ, so no lock or integrality argument settles a class: the classes of
  chains of returns multiply 1.66-fold per digit. The two-marker states up to width 262,143 that halt are (4, 9),
  (4, 13) and (12, 17), none reachable by the machine; the October 20 scan had missed the first and the last.

All computations here use the proved model (`roundZ`), the Lean theorems below, exact algebra on the pass maps, or
the bare machine; none uses the Python or C simulators with the trailing-wall slip (section 7 cites one older scan
that did). Files are in this folder (`lock/`).

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

### 6. The open cases do not run through the extra-wall loop (October 27, evening)

The point of a lock was to settle the two cases that `blank_halt_pass` leaves open (`../lean/END_TO_END.md`): a clean
tape of width ≥ 2⁴¹ in a cut class of the clean-tape tree with loop entries at every depth, or a pass start in a cut
class of its pass-start tree at every depth. Two drivers walk those trees step by step as the proved explorers build
them and record, for every cut leaf, the round shapes on its path (statistics only; no proof reads them):
`ShapeStats.lean` walks the clean-tape tree as `../lean/EntryStats.lean` does, and `PassShapes.lean` walks the
pass-start trees, with their cleaves, as `../lean/PassStats.lean` does (its cut measures agree with the ones recorded
there). A path meets the extra-wall loop if a round start on it is the extra-wall pass start `G W W W W`. In the
clean-tape tree that is the only round start with four walls that occurs; in the pass-start trees a few paths hold
four walls in other shapes, and the counts below include them. The drivers also count the paths that meet any round
shape of the loop or of its way in (`G W W W W`, `G B W W`, `G M M W W`, `G M W W W`, `G M B W`). That bounds the
loop's share from above, since `G M M W W` also occurs outside it.

- **Clean-tape tree** (Γ = 2⁴¹; `shapes_30.out`, `shapes_36.out`). At 36 digits, 1,098 of the 1,255,963 cut classes
  (0.09%) meet `G W W W W`, and 44,352 (3.5%) meet any of the five shapes, all but one of them first at `G M M W W`.
  1,061,623 (85%) never hold more than two walls in a round start, 192,933 hold three at most, 309 one at most. The
  paths are long, 32 to 47 rounds for 1,164,163 of them and 48 to 63 for 91,795, about one round per digit, and they
  stop at rounds with two or three marks: `G M M` 512,565 (41%), `G B` 191,369, `G W M M` 160,110, `G M W M` 80,133,
  `G W M M M` 73,480, `G M B` 52,830, `G M M M` 46,144, `G M M W` 43,711, `G M M M M` 37,945. At 30 digits, 22 of
  the 101,837 cut classes meet `G W W W W` and 3,133 any of the five.
- **Pass-start trees** (20 splits, `passCleaves` = 8; `passshapes_20*.out`, summed by `passshapes_sum.py` into
  `passshapes_20_sum.out`). For R ≥ 178 the cut leaves hold 3.82% of the class; 0.0365% of the class (0.95% of the cut
  measure) meets four walls, and 0.22% (5.7%) any of the five shapes. For R < 178, averaged over the 88 trees as
  `PassStats.lean` averages them, the cut leaves hold 1.96% of a class, of which 0.14% is R = 6's decided halt (a
  `G B` round that never meets four walls); of the other 1.81%, 0.82% meets four walls and 5.6% any of the five
  shapes. The largest share in one tree is 5.7% (R = 68). The cut paths stop at the same kinds of rounds as in the
  clean-tape tree (`G M M`, `G B`, `G W M M`, ...). The slices of the cleaves (measure 0) have 200,193 cut leaves for
  R < 178, 818 of them with four walls.

So **no lock for the extra-wall loops can settle either open case**: almost none of the open measure ever reaches the
loop, so a bound on what the loop can do leaves the rest untouched. What keeps these classes open is long runs of
rounds with two or three marks, mostly two-marker rounds (gap, marker, end marker), about one digit per round: the
growth of the class tree itself (lab notes, "Why the open classes grow 1.53-fold per digit"; and, under "How many free
numbers a halt needs", the second segment's classes still open at depth 46, which had come no nearer the end than 2
to 6 halvings). Together with 4, this answers the question of this note for the open cases, in the negative. The
locks of 2 and 3 remain statements about the extra-wall family: they bound halts carried by it, and would matter to
an argument that bounds right-end runs by the loops they use, not to the trees as they stand.

### 7. What keeps two-marker runs open: the return pieces (October 27, night)

Section 6 left the open classes as long runs of two- and three-mark rounds, mostly two-marker rounds. This section takes
those runs apart. A **two-marker state** is the round start G 1, M m, M E − 2 (m even, E odd: gap, marker, end marker;
the GMM state of the lab notes), and a **return** is the run from one two-marker state to the next. `Pieces.lean` walks
the route tree with loop entries (`routeTreeE`, Γ = 2²⁶, rooted at a two-marker state with m and E free) step by step as
the proved explorer builds it, and prints every leaf with its class and its round start as forms in the leaf's
coordinates; `pieces.py` solves these for exact maps of (m, E). Both are statistics only; the main pieces are then
proved in Lean (below).

- **Where a two-marker state goes** (`pieces_30.out`, 44,770 leaves at 30 digits; `pieces_24.out` at 24). 65.1% of the
  class reaches the bare one-marker tape (a clean tape) with no two-marker state on the way, 34.0% returns to two
  markers, 0.84% stops at a loop entry that cannot close, and 1.5 × 10⁻⁵ is cut (1.45 × 10⁻⁴ at 24 digits). Nearly all
  of it is decided within 12 digits.
- **The return pieces** (`pieces_30_locks.out`). The returns fall into 14,167 classes (14,105 words of round shapes).
  On each class the return is an exact affine map, m' = a·m + b·E + c and E' = E + e, with e a positive multiple of 6
  and a = u/2^r for an odd u, at most 1/4. There are two kinds:
  - **Pure halvings** (b = c = 0, so m' = m/2^r): 104 classes, measure 0.161. The largest is G M M → G M W → G M M,
    m' = m/4 on m ≡ 0 (mod 8), E ≡ 3 (mod 4), an eighth of all two-marker states. They move the marker toward the gap
    at 1, and m itself is their countdown: each divides it by at least 4, so at most log₄E of them follow one another.
    Their fixed point m = 0 is an integer point but not a state.
  - **Resets** (b > 0): 14,063 classes, measure 0.180. They put the marker back at a fraction of the width (b from
    under 1/8 to over 7/8; 40% of their measure has b in [3/4, 7/8)), and repeated they draw it toward a fixed line
    m = λE + μ inside the tape, λ = b/(1 − a). The scaled distance L = K·(m − λE − μ) to that line is an integer that
    each pass multiplies by a (divides by 2^r when u = 1, which holds for 0.319 of the 0.340 that returns), and **for
    all 14,063 the line has no integer point**, so L is never 0: every reset has a never-zero countdown like the plain
    loop's L₁, and repeats at most about log₂(E)/r times in a row.
- **No lock is shared** (`pieces_30_pairs.out`). The fixed lines differ from piece to piece (λ = 6/7, 2/5, 1/7, 2/15,
  30/31, 13/15 for the six largest resets), so no countdown survives a change of piece, as for P and Q in section 4.
  Two-piece words behave like single pieces: of the 90,000 ordered pairs of the 300 largest pieces, the only ones whose
  fixed line has integer points are the 121 pairs of their 11 pure halvings, at m = 0, and every pair with a reset has
  its own lock. Runs of pure halvings are also limited by E's residues: following E mod 2¹⁶ through all 104
  classes, at most 140 follow one another (`pieces_30_halving.out`).
- **Chains of returns branch** (`pieces_branching.out`). A return uses 4.85 digits on average. Counted as a branching
  process (a piece of k digits has measure 2^-k), the classes of chains of returns multiply by 1.657 per digit while
  their measure falls by 0.8285 per digit. This is the growth of the open classes; on the machine's own clean tapes,
  with one free number, the lab notes measure 1.53 per digit ("Why the open classes grow 1.53-fold per digit").

**The main pieces as theorems** (`lean_maps/GmmMaps.lean`, generated by `lean_maps/gen_gmmmaps.py` from
`gmm_pieces.json`, which `pieces.py DUMP emit` writes; checked in about 5 seconds, `lean_maps/gmm_check.out`). The
eight largest pieces, 39/128 ≈ 0.305 of the two-marker states (of the 0.340 that return), are proved as P and Q are in
section 1: the class is built with positions as forms in its coordinates (s, t), the proved symbolic model is run for
the piece's rounds, Lean's kernel checks the result (`decide +kernel`), and `pass_sound` turns it into a statement about
the machine (`gmm_*_return`): every two-marker state on the class with both gaps at least 32 runs, without halting, to
the two-marker state (m', E'), and this is also what `roundsZ` computes. For each reset, `*_countdown` proves
2^r·L(m', E') = L(m, E) and `*_ne_zero` that L has no integer zero; `countdown_chain` gives |L| ≥ 2^(r·k) at the start
of k repeats. Standard axioms only (the never-zero theorems use propext and Quot.sound alone).

| round starts after G M M | class | measure | map | countdown L |
|---|---|---|---|---|
| G M W | m ≡ 0 (mod 8), E ≡ 3 (mod 4) | 1/8 | 4m' = m, E' = E + 6 | none (pure halving) |
| G M M M, G W M M | m ≡ 2E + 6 (mod 16), E ≡ 3 (mod 4) | 1/16 | 8m' = m + 6E + 18, E' = E + 12 | 49m − 42E + 450 ≡ 2 (mod 7) |
| G M M M, G M W M | m ≡ 0 (mod 16), E ≡ 5 (mod 8) | 1/32 | 8m' = m, E' = E + 12 | none (pure halving) |
| G M W, G W W, G B, G W W, G B | m ≡ 2E + 26 (mod 32), E ≡ 1 (mod 4) | 1/32 | 16m' = m + 6E + 94, E' = E + 18 | 75m − 30E + 106 ≡ 1 (mod 15) |
| G M M M, G M W M, G W W M, G B M | m ≡ 8 (mod 16), E ≡ 13 (mod 16) | 1/64 | 8m' = m + E + 27, E' = E + 18 | 49m − 7E − 45 ≡ 4 (mod 7) |
| G M W, G W W, G B, G M W M | m ≡ 2E + 2 (mod 32), E ≡ 1 (mod 8) | 1/64 | 16m' = m + 2E + 26, E' = E + 18 | 75m − 10E + 62 ≡ 2 (mod 5) |
| G M W, G W W, G B, G W W, G B, G W M M | m ≡ 2E + 42 (mod 64), E ≡ 1 (mod 4) | 1/64 | 32m' = m + 30E + 438, E' = E + 24 | 961m − 930E + 9462 ≡ 7 (mod 31) |
| G M M M, G M W M, G W W M, G B M, G W M M | m ≡ E + 19 (mod 32), E ≡ 5 (mod 16) | 1/128 | 16m' = m + 13E + 199, E' = E + 24 | 75m − 65E + 669 ≡ 4 (mod 5) |

**Which two-marker states halt** (`GmmHalts.lean`, `gmm_halts.out`; `GmmNarrow.lean`, `gmm_narrow.out`;
`GmmEdge.lean`, `gmm_edge.out`; `gmm_tm.out`). By the lab notes' two-marker reduction (October 20), a halt from a clean
tape needs a two-marker state whose own segment halts (the set H), and their scan found H ∩ {E ≤ 262,143} = {(4, 13)}.
That scan stopped at m = E − 7, and the edge m = E − 5 holds two more:
- On the proved model (`roundZ`), run until the bare one-marker tape, every one of the 31,980,003 two-marker states
  with E ≤ 16,001 gets there, within 83 rounds and 16 returns, except (4, 9), (4, 13) and (12, 17). These three leave
  the model (marks touch) and halt on the bare machine after 197, 567 and 817 steps.
- At the narrowest gaps (m = 4, 6, 8, 10 and E − m = 5, 7, 9, 11) at every width up to 262,143 there is no other, so
  with the October 20 scan **H ∩ {E ≤ 262,143} = {(4, 9), (4, 13), (12, 17)}**. Above E = 16,001 the wider gaps rest
  on that scan alone, which ran the C mark model `../csearch/gmmseg.c` before the trailing-wall fix.
- None of the three is on the machine's path. Its two-marker states are (n + 2, 2n + 11) for its even clean tapes n and
  the states their segments lead to, the model's width never shrinks, and the only one of them with E ≤ 17 is (4, 15)
  (n = 2), whose segment leads to (14, 27).
- One small gap at a large width does not halt either: gaps 4 to 64 at 200 widths in [10⁶, 2·10⁶), and 4 to 200 at 100
  widths in [2⁴⁰, 2⁴¹), on both sides, all reach the bare one-marker tape, within 48 and 59 rounds.

**What this says.** A two-marker run is a word in the return pieces, ended by a run to the bare one-marker tape. Each
piece repeated is bounded, by m for the pure halvings and by a never-zero countdown for the resets, and the eight
largest are theorems with their countdowns. But the countdowns differ and a change of piece renews them, so **no lock
settles a class, and no integrality argument does either**: a countdown removes only the branch where its own piece
repeats, one 2-adic branch among mixtures whose classes multiply 1.66-fold per digit. The two kinds pull opposite ways,
the pure halvings toward the gap and the resets back into the tape. A halt needs marks to touch, and the only
two-marker states found whose runs make them touch are the three tiny ones above, which the machine never visits. What
is left is the branching itself: the open chains lose measure about 0.83-fold per digit while their classes multiply.

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
- **H = {(4, 9), (4, 13), (12, 17)}** (section 7). Checked to width 262,143, every state to 16,001 on the proved
  model. The universal statement would imply that the machine never halts from any clean tape, as "H = {(4, 13)}"
  would have in the lab notes. Section 7 shows why locks alone cannot prove it.
- **The rest of the return alphabet.** Only the eight largest return pieces (0.305 of the 0.340 that returns) are
  theorems. `gen_gmmmaps.py` proves any piece that `pieces.py DUMP emit` writes out, and every reset has a never-zero
  countdown, but the other 14,159 classes are exact algebra on the route tree's leaves, not checked in Lean.

## Files

| file | what it does |
|---|---|
| `passmaps.py` | the P and Q maps as exact rationals |
| `Harness.lean`, `verify_maps.py` | run starts through the proved `roundZ`; compare with composed maps (`verify_maps.out`) |
| `lean_maps/` | `PassMaps.lean` (P_pass, Q_pass; kernel-checked, no compiler trust), `DQ.lean` (D_Q identity and never-zero), `gen_passmaps.py`, `check.sh` (checks these and `GmmMaps.lean`) |
| `qlock_derive.py`, `DQ.txt` | derivation of D_Q and its zero set |
| `periodic_locks.py`, `periodic_locks_12.txt` | locks and rates for all Lyndon words to length 12 |
| `word_height.py`, `word_height.txt` | the norm form of any word, its height, never-zero check |
| `zsolve.py` | integer solvability of linear systems (for never-zero checks) |
| `common_inv.py`, `common_inv*.out` | common eigen-polynomials of P and Q |
| `mixed_halt_lean.py`, `mixed_halt_lean.out`, `k16_17.txt`, `tm.c`, `tm_k16_17.out` | the hand-built mixed halts, on the proved model and on the bare machine |
| `ShapeStats.lean`, `shapes_30.out`, `shapes_36.out` | the round shapes on the cut paths of the clean-tape tree with loop entries (section 6) |
| `PassShapes.lean`, `passshapes_20*.out`, `passshapes_sum.py` | the same for the pass-start trees, and their sum over R (section 6) |
| `PathSamples.lean` | sample cut paths of the route tree or the clean-tape tree, every round start with exact positions (section 7) |
| `Pieces.lean`, `pieces.py`, `pieces_24.out`, `pieces_30*.out`, `pieces_branching.out` | the route tree's leaves; the return pieces' exact maps, branching rate, locks, pairs and runs of pure halvings (section 7) |
| `gmm_pieces.json` | the eight largest return pieces, for `lean_maps/gen_gmmmaps.py` |
| `lean_maps/GmmMaps.lean`, `lean_maps/gen_gmmmaps.py`, `lean_maps/gmm_check.out` | the eight pieces as theorems about the machine, their countdowns and never-zero proofs (section 7; `check.sh` runs it) |
| `GmmHalts.lean`, `gmm_halts.out` | every two-marker state to width 16,001 on the proved model: which reach the bare one-marker tape (section 7) |
| `GmmNarrow.lean`, `gmm_narrow.out`, `GmmEdge.lean`, `gmm_edge.out`, `gmm_tm.out` | the narrowest gaps at every width to 262,143, one small gap at large widths, and the three halting states on the bare machine (section 7) |
