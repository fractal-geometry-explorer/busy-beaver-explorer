import BB6.Ends
import BB6.RouteTree

/-!
# Loop entries whose loop cannot close

A route that reaches a phase-0 pass start (three walls a, b, c, width W, with a odd, b even, W even, right end
R = W − c − 1 even and at least 2, every gap at least 448: `PassStart448`) hands the run to the loop.  From there the
loop's run makes some number p of full passes, each dividing R by 16 and the left countdown L₁ = 147b + 280W − 392c − 578
by 64, and a close needs, at the last pass start, a right end r in the closing set and a left countdown ℓ in r's class
(`thm/LoopTheorem.lean`).  So a close needs R = 16^p·r and L₁ = 64^p·ℓ.  On a route's class R and L₁ are affine in
the class coordinates, and this file checks, for the whole class at once, that this never happens (`NoCloseAt`).

The check (`exclOK`): on the cone, α·R + α₀ ≤ L₁ ≤ β·R + β₀ (decided by `ltDec`).  At a close that gives
α·16^p·r + α₀ ≤ 64^p·ℓ ≤ β·16^p·r + β₀, so for p ≥ P (4^P above |α|·176 + |α₀| and |β|·176 + |β₀|) only ℓ = 0 is
left, which no left countdown is (L₁ ≡ 3 mod 7); for each p < P and each r the window of ℓ is finite, and each ℓ in
it, with R = 16^p·r and L₁ = 64^p·ℓ, fixes the point of the class by Cramer's rule, which must not be an integer
point of the cone (`solveOut`; on a class of one coordinate, as in the clean-tape trees, R = 16^p·r fixes it directly,
`solveOut1`).  The bounds α, β, α₀, β₀ and P are computed from the forms (`exclCert`: the ratio L₁/R along the edges
of the cone, and the value at its corner), and only checked.

A run can also start the loop with a half pass (R → R/2, 2·L₁′ = L₁ + 35W − 147R − 60, from W ≡ 2 mod 4) and then
make full passes; `entryOK` checks that case as well, with those forms, unless W ≡ 0 (mod 4) on the class, and then
also asks for the middle wall at least 896 below the width, so that the half pass lands on a pass start with every
gap at least 448 again (`landing_wide`).
-/

namespace BB6.Sym
open BB6

/-- The closing set with the class (modulus, residue) of the left countdown that a close from each right end needs
(`closeClasses` in `thm/EndgameStart.lean`). -/
def closeTable : List (Nat × Int × Int) :=
  [(2, 2, 0), (4, 2, 0), (8, 8, 0), (16, 32, 0), (24, 64, 32), (32, 64, 0), (48, 128, 0), (64, 128, 0),
   (176, 128, 0)]

/-- No close after any number of full passes from right end R and left countdown L: never R = 16^p·r with r in the
closing set and L = 64^p·ℓ with ℓ in r's class and ℓ ≡ 3 (mod 7), as every left countdown is. -/
def NoCloseAt (R L : Int) : Prop :=
  ∀ (p r : Nat) (M c ℓ : Int), (r, M, c) ∈ closeTable → R = (16 : Int) ^ p * (r : Int) → L = (64 : Int) ^ p * ℓ →
    ℓ % M = c → ℓ % 7 = 3 → False

/-! ## One point of the class -/

/-- The point where R = N and L = S (Cramer's rule), when it is an integer point, lies outside the cone (some gap
form is below Γ there).  `false` when R and L are parallel. -/
def solveOut (R L : YForm) (ts : List YForm) (Γ N S : Int) : Bool :=
  let r1 := R.c.getD 0 0
  let r2 := R.c.getD 1 0
  let l1 := L.c.getD 0 0
  let l2 := L.c.getD 1 0
  let det := r1 * l2 - r2 * l1
  let X0 := (N - R.k) * l2 - (S - L.k) * r2
  let X1 := r1 * (S - L.k) - l1 * (N - R.k)
  det != 0 && (X0 % det != 0 || X1 % det != 0 || ts.any (fun t => decide (t.eval [X0 / det, X1 / det] < Γ)))

theorem solveOut_sound {R L : YForm} {ts : List YForm} {Γ N S : Int} (h : solveOut R L ts Γ N S = true)
    {y0 y1 : Int} (hy : inCone ts Γ [y0, y1]) (hR : R.eval [y0, y1] = N) (hL : L.eval [y0, y1] = S) : False := by
  simp only [solveOut, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true,
    decide_eq_true_eq] at h
  rw [eval_two] at hR hL
  obtain ⟨hdet, h⟩ := h
  have c0 : (R.c.getD 0 0 * L.c.getD 1 0 - R.c.getD 1 0 * L.c.getD 0 0) * y0 =
      (N - R.k) * L.c.getD 1 0 - (S - L.k) * R.c.getD 1 0 := by grind
  have c1 : (R.c.getD 0 0 * L.c.getD 1 0 - R.c.getD 1 0 * L.c.getD 0 0) * y1 =
      R.c.getD 0 0 * (S - L.k) - L.c.getD 0 0 * (N - R.k) := by grind
  rw [← c0, ← c1, Int.mul_emod_right, Int.mul_emod_right, Int.mul_ediv_cancel_left _ hdet,
    Int.mul_ediv_cancel_left _ hdet] at h
  rcases h with (h | h) | ⟨t, ht, hlt⟩
  · exact h rfl
  · exact h rfl
  · exact absurd (hy t ht) (by omega)

/-- The same for a class of one coordinate (R, L and the cone free of y₁): R = N fixes y₀, and the check is that y₀
is not an integer, or L ≠ S there, or the point is outside the cone. -/
def solveOut1 (R L : YForm) (ts : List YForm) (Γ N S : Int) : Bool :=
  let r0 := R.c.getD 0 0
  let y0 := (N - R.k) / r0
  R.c.getD 1 0 == 0 && L.c.getD 1 0 == 0 && ts.all (fun t => t.c.getD 1 0 == 0) && r0 != 0 &&
    ((N - R.k) % r0 != 0 || L.k + L.c.getD 0 0 * y0 != S ||
      ts.any (fun t => decide (t.k + t.c.getD 0 0 * y0 < Γ)))

theorem solveOut1_sound {R L : YForm} {ts : List YForm} {Γ N S : Int} (h : solveOut1 R L ts Γ N S = true)
    {y0 y1 : Int} (hy : inCone ts Γ [y0, y1]) (hR : R.eval [y0, y1] = N) (hL : L.eval [y0, y1] = S) : False := by
  simp only [solveOut1, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hR1, hL1⟩, hts⟩, hr0⟩, h⟩ := h
  rw [eval_two, hR1] at hR
  rw [eval_two, hL1] at hL
  have e : N - R.k = R.c.getD 0 0 * y0 := by omega
  rw [e, Int.mul_emod_right, Int.mul_ediv_cancel_left _ hr0] at h
  rcases h with (h | h) | ⟨t, ht, hlt⟩
  · exact h rfl
  · exact h (by omega)
  · have := hy t ht
    rw [eval_two, hts t ht] at this
    omega

/-! ## A window of left countdowns -/

/-- `f ℓ` for ℓ = ℓ₀, ℓ₀ + M, ℓ₀ + 2M, … as long as ℓ ≤ hi (`false` if `n` steps do not get past hi). -/
def stepAll (f : Int → Bool) (M hi : Int) : Nat → Int → Bool
  | 0, ℓ => decide (hi < ℓ)
  | n + 1, ℓ => decide (hi < ℓ) || (f ℓ && stepAll f M hi n (ℓ + M))

theorem stepAll_sound (f : Int → Bool) (M hi : Int) : ∀ (n : Nat) (ℓ₀ : Int), stepAll f M hi n ℓ₀ = true →
    ∀ ℓ, ℓ₀ ≤ ℓ → ℓ ≤ hi → M ∣ (ℓ - ℓ₀) → 0 < M → f ℓ = true := by
  intro n
  induction n with
  | zero => intro ℓ₀ h ℓ h1 h2 _ _; simp only [stepAll, decide_eq_true_eq] at h; omega
  | succ n ih =>
    intro ℓ₀ h ℓ h1 h2 hd hM
    simp only [stepAll, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨hf, hr⟩
    · omega
    · by_cases he : ℓ = ℓ₀
      · subst he; exact hf
      · have hpos : 0 < ℓ - ℓ₀ := by omega
        have hle := Int.le_of_dvd hpos hd
        refine ih (ℓ₀ + M) hr ℓ (by omega) h2 ?_ hM
        have : ℓ - (ℓ₀ + M) = (ℓ - ℓ₀) - M := by omega
        rw [this]
        exact Int.dvd_sub hd (Int.dvd_refl M)

/-- The first member of the class c mod M that is at least lo. -/
def firstAbove (lo M c : Int) : Int := lo + (c - lo) % M

theorem firstAbove_le {lo M c ℓ : Int} (hM : 0 < M) (hl : lo ≤ ℓ) (hc : ℓ % M = c) :
    firstAbove lo M c ≤ ℓ ∧ M ∣ (ℓ - firstAbove lo M c) := by
  unfold firstAbove
  have e1 := Int.mul_ediv_add_emod ℓ M
  have e2 := Int.mul_ediv_add_emod (c - lo) M
  have q0 := Int.emod_nonneg (c - lo) (by omega : M ≠ 0)
  have q1 := Int.emod_lt_of_pos (c - lo) hM
  rw [hc] at e1
  -- ℓ − first = M (ℓ/M + (c − lo)/M)
  have hk : ℓ - (lo + (c - lo) % M) = M * (ℓ / M + (c - lo) / M) := by rw [Int.mul_add]; omega
  refine ⟨?_, ⟨_, hk⟩⟩
  -- a multiple of M above −M is at least 0
  rcases Int.lt_or_le (ℓ / M + (c - lo) / M) 0 with hneg | hk0
  · have : M * (ℓ / M + (c - lo) / M) ≤ M * (-1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  · have := Int.mul_nonneg (by omega : (0 : Int) ≤ M) hk0
    omega

/-! ## The bounds and the check -/

/-- The bounds of the check: α·R + α₀ ≤ L ≤ β·R + β₀ on the cone, and P with 4^P above both |α|·176 + |α₀| and
|β|·176 + |β₀|. -/
structure ExclCert where
  α : Int
  α₀ : Int
  β : Int
  β₀ : Int
  P : Nat
  deriving Repr

/-- The window for right end r after p passes: every ℓ ≡ c (mod M) with α·16^p·r + α₀ ≤ 64^p·ℓ ≤ β·16^p·r + β₀ and
ℓ ≡ 3 (mod 7) gives a point outside the cone. -/
def winOK (R L : YForm) (ts : List YForm) (Γ : Int) (q : ExclCert) (r : Nat) (M c : Int) (p : Nat) : Bool :=
  let N : Int := 16 ^ p * (r : Int)
  let S : Int := 64 ^ p
  let lo := -((-(q.α * N + q.α₀)) / S)
  let hi := (q.β * N + q.β₀) / S
  let st := firstAbove lo M c
  stepAll (fun ℓ => ℓ % 7 != 3 || solveOut R L ts Γ N (S * ℓ) || solveOut1 R L ts Γ N (S * ℓ)) M hi
    ((hi - st) / M).toNat.succ.succ st

/-- No close from any point of the class inside the cone, after any number of full passes (`exclOK_sound`). -/
def exclOK (R L : YForm) (ts : List YForm) (Γ : Int) (q : ExclCert) : Bool :=
  ltDec L ((R.smul q.β).addc (q.β₀ + 1)) ts Γ == some true &&
  ltDec ((R.smul q.α).addc (q.α₀ - 1)) L ts Γ == some true &&
  decide ((q.β.natAbs : Int) * 176 + (q.β₀.natAbs : Int) < (4 : Int) ^ q.P) &&
  decide ((q.α.natAbs : Int) * 176 + (q.α₀.natAbs : Int) < (4 : Int) ^ q.P) &&
  closeTable.all (fun e => decide (0 < e.2.1) && decide (0 ≤ e.2.2) && decide (e.2.2 < e.2.1) &&
    decide (e.1 ≤ 176) && (List.range q.P).all (fun p => winOK R L ts Γ q e.1 e.2.1 e.2.2 p))

theorem winOK_sound {R L : YForm} {ts : List YForm} {Γ : Int} {q : ExclCert} {r : Nat} {M c : Int} {p : Nat}
    (h : winOK R L ts Γ q r M c p = true) (hM : 0 < M) {y0 y1 : Int} (hy : inCone ts Γ [y0, y1]) {ℓ : Int}
    (hR : R.eval [y0, y1] = (16 : Int) ^ p * (r : Int)) (hL : L.eval [y0, y1] = (64 : Int) ^ p * ℓ)
    (hlo : q.α * ((16 : Int) ^ p * (r : Int)) + q.α₀ ≤ (64 : Int) ^ p * ℓ)
    (hhi : (64 : Int) ^ p * ℓ ≤ q.β * ((16 : Int) ^ p * (r : Int)) + q.β₀) (hc : ℓ % M = c) (h7 : ℓ % 7 = 3) :
    False := by
  unfold winOK at h
  have hS : (0 : Int) < 64 ^ p := Int.pow_pos (by decide)
  have hl : -((-(q.α * ((16 : Int) ^ p * (r : Int)) + q.α₀)) / 64 ^ p) ≤ ℓ := by
    have := Int.le_ediv_of_mul_le hS (show -ℓ * 64 ^ p ≤ -(q.α * ((16 : Int) ^ p * (r : Int)) + q.α₀) by
      rw [Int.neg_mul, Int.mul_comm]; omega)
    omega
  have hh : ℓ ≤ (q.β * ((16 : Int) ^ p * (r : Int)) + q.β₀) / 64 ^ p :=
    Int.le_ediv_of_mul_le hS (by rw [Int.mul_comm]; exact hhi)
  obtain ⟨hst, hd⟩ := firstAbove_le hM hl hc
  have := stepAll_sound _ _ _ _ _ h ℓ hst hh hd hM
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
  rcases this with (h1 | h2) | h3
  · exact h1 h7
  · exact solveOut_sound h2 hy hR hL
  · exact solveOut1_sound h3 hy hR hL

/-- Past P passes the window holds only ℓ = 0. -/
theorem big_p {X Y B ℓ : Int} (hX : 0 < X) (hY : B < Y) (hB : 0 ≤ B) (h : X * Y * ℓ ≤ X * B) (hℓ : 1 ≤ ℓ) :
    False := by
  have hXY : 0 ≤ X * Y := Int.mul_nonneg (by omega) (by omega)
  have h1 : X * Y * 1 ≤ X * Y * ℓ := Int.mul_le_mul_of_nonneg_left hℓ hXY
  rw [Int.mul_one] at h1
  have h2 : X * Y ≤ X * B := Int.le_trans h1 h
  have h3 := Int.le_of_mul_le_mul_left h2 hX
  omega

theorem lin_bound {X a a₀ r : Int} (hX : 1 ≤ X) (hr0 : 0 ≤ r) (hr : r ≤ 176) :
    a * (X * r) + a₀ ≤ X * ((a.natAbs : Int) * 176 + (a₀.natAbs : Int)) := by
  have ha : a ≤ (a.natAbs : Int) := Int.le_natAbs
  have ha₀ : a₀ ≤ (a₀.natAbs : Int) := Int.le_natAbs
  have hn : (0 : Int) ≤ (a.natAbs : Int) := Int.natCast_nonneg _
  have hn₀ : (0 : Int) ≤ (a₀.natAbs : Int) := Int.natCast_nonneg _
  have e1 : a * (X * r) ≤ (a.natAbs : Int) * (X * r) :=
    Int.mul_le_mul_of_nonneg_right ha (Int.mul_nonneg (by omega) hr0)
  have e2 : (a.natAbs : Int) * (X * r) ≤ (a.natAbs : Int) * (X * 176) :=
    Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left hr (by omega)) hn
  have e3 : (a₀.natAbs : Int) ≤ X * (a₀.natAbs : Int) := by
    have := Int.mul_le_mul_of_nonneg_right hX hn₀
    rw [Int.one_mul] at this; exact this
  have e4 : X * ((a.natAbs : Int) * 176 + (a₀.natAbs : Int)) =
      (a.natAbs : Int) * (X * 176) + X * (a₀.natAbs : Int) := by grind
  omega

theorem exclOK_sound {R L : YForm} {ts : List YForm} {Γ : Int} {q : ExclCert} (h : exclOK R L ts Γ q = true)
    {y0 y1 : Int} (hy : inCone ts Γ [y0, y1]) : NoCloseAt (R.eval [y0, y1]) (L.eval [y0, y1]) := by
  intro p r M c ℓ hmem hR hL hc h7
  simp only [exclOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hb, ha⟩, hPb⟩, hPa⟩, hall⟩ := h
  have ub := (ltDec_sound _ _ ts Γ _ hy true hb).mpr rfl
  have lb := (ltDec_sound _ _ ts Γ _ hy true ha).mpr rfl
  simp only [eval_addc, eval_smul] at ub lb
  rw [hR, hL] at ub lb
  have hall' := hall (r, M, c) hmem
  dsimp only at hall'
  obtain ⟨⟨⟨⟨hM, hc0⟩, hcM⟩, hr176⟩, hwin⟩ := hall'
  by_cases hp : p < q.P
  · exact winOK_sound (hwin p (List.mem_range.mpr hp)) hM hy hR hL (by omega) (by omega) hc h7
  · -- p ≥ P: 64^p = 16^p · 4^p and 4^p ≥ 4^P, so the window holds only ℓ = 0
    have hPp : q.P ≤ p := by omega
    have hX : (0 : Int) < 16 ^ p := Int.pow_pos (by decide)
    have h64 : (64 : Int) ^ p = 16 ^ p * 4 ^ p := by
      rw [show (64 : Int) = 16 * 4 by decide, Int.mul_pow]
    have h4 : (4 : Int) ^ q.P ≤ (4 : Int) ^ p := by exact_mod_cast Nat.pow_le_pow_right (by decide) hPp
    have hr0 : (0 : Int) ≤ (r : Int) := Int.natCast_nonneg r
    have hr1 : (r : Int) ≤ 176 := by omega
    have h70 : ℓ ≠ 0 := by omega
    rcases Int.lt_or_le 0 ℓ with hpos | hneg
    · have lb' := lin_bound (X := 16 ^ p) (a := q.β) (a₀ := q.β₀) (by omega) hr0 hr1
      have hb : (16 : Int) ^ p * 4 ^ p * ℓ ≤ 16 ^ p * ((q.β.natAbs : Int) * 176 + (q.β₀.natAbs : Int)) := by
        rw [← h64]; omega
      exact big_p hX (by omega) (by omega) hb (by omega)
    · have lb' := lin_bound (X := 16 ^ p) (a := -q.α) (a₀ := -q.α₀) (by omega) hr0 hr1
      simp only [Int.natAbs_neg] at lb'
      have hm : (16 : Int) ^ p * 4 ^ p * (-ℓ) ≤
          16 ^ p * ((q.α.natAbs : Int) * 176 + (q.α₀.natAbs : Int)) := by
        rw [Int.mul_neg, ← h64]
        have : -q.α * (16 ^ p * (r : Int)) = -(q.α * (16 ^ p * (r : Int))) := Int.neg_mul _ _
        omega
      exact big_p hX (by omega) (by omega) hm (by omega)

/-! ## The bounds, computed -/

/-- ⌈a / b⌉ for b > 0. -/
def ceilDiv (a b : Int) : Int := -((-a) / b)

/-- The least P ≥ P₀ with B < 4^P, searching `n` steps. -/
def log4Above (B : Int) : Nat → Nat → Nat
  | 0, P => P
  | n + 1, P => if B < (4 : Int) ^ P then P else log4Above B n (P + 1)

/-- Bounds for `exclOK`, computed from the forms (only checked, never trusted): the ratio L/R along the two edges of
the cone, rounded outwards, and the constants that make both bounds hold at the cone's corner (where both gap forms
equal Γ); for a cone of one form (the classes of one coordinate), the ratio along its ray and the constants at its
corner. -/
def exclCert (R L : YForm) (ts : List YForm) (Γ : Int) : ExclCert :=
  match ts with
  | [t1, t2] =>
    let u10 := t1.c.getD 0 0
    let u11 := t1.c.getD 1 0
    let u20 := t2.c.getD 0 0
    let u21 := t2.c.getD 1 0
    let dt := u10 * u21 - u11 * u20
    -- the edges: d1 ⊥ u1 with u2·d1 > 0, d2 ⊥ u2 with u1·d2 > 0
    let d1 : Int × Int := if 0 < -dt then (u11, -u10) else (-u11, u10)
    let d2 : Int × Int := if 0 < dt then (u21, -u20) else (-u21, u20)
    let rl (d : Int × Int) : Int := R.c.getD 0 0 * d.1 + R.c.getD 1 0 * d.2
    let ll (d : Int × Int) : Int := L.c.getD 0 0 * d.1 + L.c.getD 1 0 * d.2
    let α := min (ll d1 / rl d1) (ll d2 / rl d2) - 1
    let β := max (ceilDiv (ll d1) (rl d1)) (ceilDiv (ll d2) (rl d2)) + 1
    -- the corner is (ax, ay)/dt; ⌈−f(corner)⌉
    let ax := (Γ - t1.k) * u21 - (Γ - t2.k) * u11
    let ay := u10 * (Γ - t2.k) - u20 * (Γ - t1.k)
    let num (f : YForm) : Int := f.k * dt + f.c.getD 0 0 * ax + f.c.getD 1 0 * ay
    let negCeil (f : YForm) : Int := if 0 < dt then ceilDiv (-(num f)) dt else ceilDiv (num f) (-dt)
    let β₀ := max 0 (negCeil ((R.smul β).sub L)) + 1
    let α₀ := -(max 0 (negCeil (L.sub (R.smul α))) + 1)
    let B := max ((α.natAbs : Int) * 176 + α₀.natAbs) ((β.natAbs : Int) * 176 + β₀.natAbs)
    ⟨α, α₀, β, β₀, log4Above B 64 0⟩
  | [t] =>
    -- a cone of one form (the classes of one coordinate): the ray from the corner y₀ = (Γ − t.k)/u0
    let u0 := t.c.getD 0 0
    let e : Int := if 0 < u0 then 1 else -1
    let rl := R.c.getD 0 0 * e
    let ll := L.c.getD 0 0 * e
    let α := ll / rl - 1
    let β := ceilDiv ll rl + 1
    let num (f : YForm) : Int := f.k * u0 + f.c.getD 0 0 * (Γ - t.k)
    let negCeil (f : YForm) : Int := if 0 < u0 then ceilDiv (-(num f)) u0 else ceilDiv (num f) (-u0)
    let β₀ := max 0 (negCeil ((R.smul β).sub L)) + 1
    let α₀ := -(max 0 (negCeil (L.sub (R.smul α))) + 1)
    let B := max ((α.natAbs : Int) * 176 + α₀.natAbs) ((β.natAbs : Int) * 176 + β₀.natAbs)
    ⟨α, α₀, β, β₀, log4Above B 64 0⟩
  | _ => ⟨0, 0, 0, 0, 0⟩

/-! ## The entry -/

/-- The left countdown's form after a half pass, times 2: L₁ + 35W − 147R − 60. -/
def halfL (L sW R : YForm) : YForm := ((L.add (sW.smul 35)).sub (R.smul 147)).addc (-60)

/-- The round start is a phase-0 pass start with every gap at least 448, width at least 2²⁴ and, when W ≡ 2 mod 4,
the middle wall at least 896 below the width (decided on the class), and no point of the class closes through the
loop from it, after full passes or after a half pass and full passes. -/
def entryOK (Γ : Int) (ts : List YForm) (ss : List SMark) (sW : YForm) : Bool :=
  match swwwOf ss with
  | none => false
  | some (a, b, c) =>
    let R := (sW.sub c).addc (-1)
    let L := L1Form b c sW
    a.modDec 2 == some 1 && b.modDec 2 == some 0 && sW.modDec 2 == some 0 && R.modDec 2 == some 0 &&
    ltDec (YForm.const 1) R ts Γ == some true && ltDec (YForm.const 447) a ts Γ == some true &&
    ltDec (a.addc 447) b ts Γ == some true && ltDec (b.addc 447) c ts Γ == some true &&
    ltDec (YForm.const (2 ^ 24 - 1)) sW ts Γ == some true &&
    (sW.modDec 4 == some 0 || ltDec (b.addc 895) sW ts Γ == some true) &&
    exclOK R L ts Γ (exclCert R L ts Γ) &&
    (sW.modDec 4 == some 0 ||
      match R.half?, (halfL L sW R).half? with
      | some Rh, some Lh => exclOK Rh Lh ts Γ (exclCert Rh Lh ts Γ)
      | _, _ => false)

/-- A pass start with every gap at least 448 and width at least 2²⁴ (where a close through the loop is full passes
after at most one half pass, `LoopChain.close_wide`), and with the middle wall at least 896 below the width when
W ≡ 2 mod 4 (where a half pass can start the loop; then its landing keeps every gap at least 448, `loop_halt_leaves`),
from which the loop cannot close: not after full passes, and (when W ≡ 2 mod 4) not after a half pass
(2R′ = R, 2L₁′ = L₁ + 35W − 147R − 60) and full passes. -/
def EntryNoClose (ms : List Mark) (W : Nat) : Prop :=
  2 ^ 24 ≤ W ∧ ∃ R a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧ PassStart448 ms W R ∧
    (W % 4 = 2 → b + 896 ≤ W) ∧ NoCloseAt R (passL1 ms W) ∧
    (W % 4 = 2 → ∀ R' L' : Int, 2 * R' = (R : Int) → 2 * L' = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60 →
      NoCloseAt R' L')

theorem entryOK_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW : YForm} (h : entryOK Γ ts ss sW = true)
    {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y) {ms : List Mark} {W : Nat} (hs : agL y ss ms)
    (hW : agN y sW W) : EntryNoClose ms W := by
  obtain ⟨y0, y1, rfl⟩ : ∃ y0 y1, y = [y0, y1] := by
    match y, hlen with
    | [y0, y1], _ => exact ⟨y0, y1, rfl⟩
  have hag := wwwOf_agree hs
  unfold entryOK at h
  cases hsw : swwwOf ss with
  | none => rw [hsw] at h; cases h
  | some f =>
    obtain ⟨fa, fb, fc⟩ := f
    rw [hsw] at h
    obtain ⟨a, b, c, rfl, h1, h2, h3⟩ := hag.2 fa fb fc hsw
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨pa, pb⟩, pW⟩, pR⟩, g1⟩, ga⟩, gb⟩, gc⟩, gw⟩, g896⟩, hx⟩, hh⟩ := h
    have ma := modDec_nat h1 (m := 2) pa
    have mb := modDec_nat h2 (m := 2) pb
    have mW := modDec_nat hW (m := 2) pW
    have l1 := (ltDec_sound _ _ ts Γ _ hy true g1).mpr rfl
    have la := (ltDec_sound _ _ ts Γ _ hy true ga).mpr rfl
    have lb := (ltDec_sound _ _ ts Γ _ hy true gb).mpr rfl
    have lc := (ltDec_sound _ _ ts Γ _ hy true gc).mpr rfl
    have lw := (ltDec_sound _ _ ts Γ _ hy true gw).mpr rfl
    have pR' := eval_mod _ 2 0 pR [y0, y1]
    have hL := eval_L1Form fb fc sW [y0, y1]
    unfold agN at h1 h2 h3 hW
    simp only [eval_const, eval_addc, eval_sub] at l1 la lb lc lw pR'
    have hx' := exclOK_sound hx hy
    simp only [eval_addc, eval_sub] at hx'
    have h24 : (2 : Nat) ^ 24 = 16777216 := rfl
    have hc' : W - (W - c - 1) - 1 = c := by omega
    refine ⟨by rw [h24]; omega, W - c - 1, a, b, by rw [hc'],
      ⟨a, b, by rw [hc'], by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, ?_, ?_, ?_⟩
    · intro h4
      rcases g896 with g | g
      · have := modDec_nat hW (m := 4) g; omega
      · have := (ltDec_sound _ _ ts Γ _ hy true g).mpr rfl
        simp only [eval_addc] at this
        omega
    · have e1 : ((W - c - 1 : Nat) : Int) = sW.eval [y0, y1] - fc.eval [y0, y1] - 1 := by omega
      have e2 : passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W = (L1Form fb fc sW).eval [y0, y1] := by
        simp only [passL1, loopL1]; rw [hL]; omega
      rw [e1, e2]; exact hx'
    · intro h4 R' L' hR' hL'
      rcases hh with hh | hh
      · have := modDec_nat hW (m := 4) hh; omega
      · cases hRh : ((sW.sub fc).addc (-1)).half? with
        | none => rw [hRh] at hh; simp at hh
        | some Rh =>
          cases hLh : (halfL (L1Form fb fc sW) sW ((sW.sub fc).addc (-1))).half? with
          | none => rw [hRh, hLh] at hh; simp at hh
          | some Lh =>
            rw [hRh, hLh] at hh
            have hn := exclOK_sound hh hy
            have eR := eval_half _ _ hRh [y0, y1]
            have eL := eval_half _ _ hLh [y0, y1]
            simp only [halfL, eval_addc, eval_sub, eval_add, eval_smul] at eR eL
            have e2 : passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W = (L1Form fb fc sW).eval [y0, y1] := by
              simp only [passL1, loopL1]; rw [hL]; omega
            have r1 : Rh.eval [y0, y1] = R' := by omega
            have r2 : Lh.eval [y0, y1] = L' := by omega
            rw [← r1, ← r2]; exact hn

end BB6.Sym
