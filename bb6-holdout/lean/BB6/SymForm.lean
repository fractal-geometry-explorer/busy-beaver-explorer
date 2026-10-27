import BB6.Round

/-!
# Symbolic positions: integer affine forms on a leaf's coordinates

A certificate leaf is a residue class of start states, x = x0 + B y with y free.  Substituting it into the start
state makes every position an integer affine form in y (`YForm`: a constant and a coefficient list), and every step
of the mark model stays integral as long as a halving is only done when every coefficient is even.  The three kinds
of decision the model needs are:

* a residue (`d % 2`, `d % 4`): decided when every coefficient is divisible by the modulus (`modDec`);
* an equality with a constant: decided when every coefficient is zero (`constVal`);
* an order: decided on the cone of large gaps by an identity `D · p = Σ μⱼ tⱼ + c` with `D > 0`: then `p > 0`
  whenever every gap `tⱼ ≥ Γ`, every `μⱼ ≥ 0` and `c + Γ Σ μⱼ > 0` (and `p < 0` when every `μⱼ ≤ 0` and
  `c + Γ Σ μⱼ < 0`).  The identity comes from an inverse of the gap forms' coefficient matrix, `D yᵢ + κᵢ = Σⱼ uᵢⱼ tⱼ`,
  which is checked once per cone (`invCheck`); then `μ = Σᵢ pᵢ uᵢ` and `c = D p₀ − Σᵢ pᵢ κᵢ` for every `p` (`sgnInv`).
  How the inverse is found (`coneInv`, Cramer's rule) is not part of the trusted base; only the check is.

Coefficient lists are padded with zeros, so no length conditions appear in the lemmas.
-/

namespace BB6.Sym

/-- Dot product, truncated to the shorter list. -/
def dot : List Int → List Int → Int
  | a :: as, y :: ys => a * y + dot as ys
  | _, _ => 0

/-- Coefficientwise sum, padding the shorter list with zeros. -/
def addL : List Int → List Int → List Int
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addL as bs

def smulL (k : Int) (a : List Int) : List Int := a.map (k * ·)

@[simp] theorem dot_nil_left (y : List Int) : dot [] y = 0 := by cases y <;> rfl
@[simp] theorem dot_nil_right (a : List Int) : dot a [] = 0 := by cases a <;> rfl

theorem dot_addL (a b y : List Int) : dot (addL a b) y = dot a y + dot b y := by
  induction a generalizing b y with
  | nil => simp [addL]
  | cons x as ih =>
    cases b with
    | nil => simp [addL]
    | cons z bs =>
      cases y with
      | nil => simp [addL]
      | cons w ys =>
        simp only [addL, dot, ih]
        rw [Int.add_mul]; omega

theorem dot_smulL (k : Int) (a y : List Int) : dot (smulL k a) y = k * dot a y := by
  induction a generalizing y with
  | nil => simp [smulL]
  | cons x as ih =>
    cases y with
    | nil => simp [smulL]
    | cons w ys =>
      simp only [smulL, List.map, dot] at ih ⊢
      rw [ih, Int.mul_add, Int.mul_assoc]

/-- An integer affine form `k + Σ cᵢ yᵢ`. -/
structure YForm where
  k : Int
  c : List Int
  deriving Repr, BEq, DecidableEq

def YForm.eval (f : YForm) (y : List Int) : Int := f.k + dot f.c y

def YForm.const (k : Int) : YForm := ⟨k, []⟩
def YForm.add (f g : YForm) : YForm := ⟨f.k + g.k, addL f.c g.c⟩
def YForm.neg (f : YForm) : YForm := ⟨-f.k, smulL (-1) f.c⟩
def YForm.sub (f g : YForm) : YForm := f.add g.neg
def YForm.addc (f : YForm) (n : Int) : YForm := ⟨f.k + n, f.c⟩
def YForm.smul (n : Int) (f : YForm) : YForm := ⟨n * f.k, smulL n f.c⟩

@[simp] theorem eval_const (k : Int) (y : List Int) : (YForm.const k).eval y = k := by
  simp [YForm.const, YForm.eval]
@[simp] theorem eval_add (f g : YForm) (y : List Int) : (f.add g).eval y = f.eval y + g.eval y := by
  simp only [YForm.add, YForm.eval, dot_addL]; omega
@[simp] theorem eval_neg (f : YForm) (y : List Int) : f.neg.eval y = - f.eval y := by
  simp only [YForm.neg, YForm.eval, dot_smulL]; omega
@[simp] theorem eval_sub (f g : YForm) (y : List Int) : (f.sub g).eval y = f.eval y - g.eval y := by
  simp only [YForm.sub, eval_add, eval_neg]; omega
@[simp] theorem eval_addc (f : YForm) (n : Int) (y : List Int) : (f.addc n).eval y = f.eval y + n := by
  simp only [YForm.addc, YForm.eval]; omega
@[simp] theorem eval_smul (n : Int) (f : YForm) (y : List Int) : (f.smul n).eval y = n * f.eval y := by
  simp only [YForm.smul, YForm.eval, dot_smulL, Int.mul_add]

/-! ## Halving and residues -/

def allDiv (m : Int) (c : List Int) : Bool := c.all (fun a => a % m == 0)

/-- `f / 2`, defined when every coefficient and the constant are even. -/
def YForm.half? (f : YForm) : Option YForm :=
  if f.k % 2 == 0 && allDiv 2 f.c then some ⟨f.k / 2, f.c.map (· / 2)⟩ else none

theorem dot_div (m : Int) (c y : List Int) (h : allDiv m c = true) : dot c y = m * dot (c.map (· / m)) y := by
  induction c generalizing y with
  | nil => simp
  | cons a as ih =>
    simp only [allDiv, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    cases y with
    | nil => simp
    | cons w ys =>
      simp only [List.map, dot]
      rw [ih ys (by simpa [allDiv] using h.2), Int.mul_add]
      have ha : a = m * (a / m) := (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h.1)).symm
      conv => lhs; rw [ha]
      rw [Int.mul_assoc]

theorem eval_half (f g : YForm) (h : f.half? = some g) (y : List Int) : f.eval y = 2 * g.eval y := by
  unfold YForm.half? at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    cases h
    simp only [YForm.eval]
    rw [Int.mul_add, ← dot_div 2 f.c y hc.2]
    have : f.k = 2 * (f.k / 2) := (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hc.1)).symm
    omega
  · cases h

/-- The residue of `f` modulo `m`, when every coefficient is divisible by `m`. -/
def YForm.modDec (f : YForm) (m : Int) : Option Int :=
  if allDiv m f.c then some (f.k % m) else none

theorem eval_mod (f : YForm) (m r : Int) (h : f.modDec m = some r) (y : List Int) : f.eval y % m = r := by
  unfold YForm.modDec at h
  split at h
  · rename_i hc
    cases h
    simp only [YForm.eval]
    rw [dot_div m f.c y hc, Int.add_mul_emod_self_left]
  · cases h

/-- The value of `f`, when every coefficient is zero. -/
def YForm.constVal (f : YForm) : Option Int := if f.c.all (· == 0) then some f.k else none

theorem dot_zero (c y : List Int) (h : c.all (· == 0) = true) : dot c y = 0 := by
  induction c generalizing y with
  | nil => simp
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    cases y with
    | nil => simp
    | cons w ys => simp only [dot, h.1, Int.zero_mul, Int.zero_add]; exact ih ys h.2

theorem eval_constVal (f : YForm) (v : Int) (h : f.constVal = some v) (y : List Int) : f.eval y = v := by
  unfold YForm.constVal at h
  split at h
  · rename_i hc; cases h; simp only [YForm.eval, dot_zero f.c y hc, Int.add_zero]
  · cases h

/-! ## Order on the cone of large gaps -/

/-- The cone: every gap form is at least `Γ`. -/
def inCone (ts : List YForm) (Γ : Int) (y : List Int) : Prop := ∀ t ∈ ts, Γ ≤ t.eval y

def combo : List Int → List YForm → YForm
  | m :: ms, t :: ts => (t.smul m).add (combo ms ts)
  | _, _ => YForm.const 0

theorem eval_combo (ms : List Int) (ts : List YForm) (y : List Int) :
    (combo ms ts).eval y = dot ms (ts.map (·.eval y)) := by
  induction ms generalizing ts with
  | nil => cases ts <;> simp [combo, dot]
  | cons m ms ih =>
    cases ts with
    | nil => simp [combo, dot]
    | cons t ts => simp only [combo, eval_add, eval_smul, ih, List.map, dot]

/-- Coefficientwise equality of two forms (padding with zeros). -/
def coeffEq : List Int → List Int → Bool
  | [], bs => bs.all (· == 0)
  | as, [] => as.all (· == 0)
  | a :: as, b :: bs => a == b && coeffEq as bs

theorem dot_coeffEq (a b y : List Int) (h : coeffEq a b = true) : dot a y = dot b y := by
  induction a generalizing b y with
  | nil => rw [dot_nil_left, dot_zero b y (by cases b <;> simpa [coeffEq] using h)]
  | cons x as ih =>
    cases b with
    | nil => rw [dot_nil_left, dot_zero (x :: as) y (by simpa [coeffEq] using h)]
    | cons z bs =>
      simp only [coeffEq, Bool.and_eq_true, beq_iff_eq] at h
      cases y with
      | nil => simp
      | cons w ys => simp only [dot, h.1, ih bs ys h.2]

def sumL : List Int → Int
  | [] => 0
  | a :: as => a + sumL as

/-- The check of a positivity certificate for `p` (with the constant `c` it implies). -/
theorem dot_ge (ms : List Int) (vs : List Int) (Γ : Int) (hm : ms.all (0 ≤ ·) = true) (hl : ms.length ≤ vs.length)
    (hv : ∀ v ∈ vs, Γ ≤ v) : Γ * sumL ms ≤ dot ms vs := by
  induction ms generalizing vs with
  | nil => simp [sumL]
  | cons m ms ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hm
      simp only [sumL, dot, Int.mul_add]
      have h1 : Γ * m ≤ m * v := by
        rw [Int.mul_comm]; exact Int.mul_le_mul_of_nonneg_left (hv v (by simp)) hm.1
      have h2 := ih vs hm.2 (by simp at hl; omega) (fun w hw => hv w (by simp [hw]))
      omega

theorem dot_le (ms : List Int) (vs : List Int) (Γ : Int) (hm : ms.all (· ≤ 0) = true) (hl : ms.length ≤ vs.length)
    (hv : ∀ v ∈ vs, Γ ≤ v) : dot ms vs ≤ Γ * sumL ms := by
  induction ms generalizing vs with
  | nil => simp [sumL]
  | cons m ms ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hm
      simp only [sumL, dot, Int.mul_add]
      have h1 : m * v ≤ Γ * m := by
        rw [Int.mul_comm Γ m]; exact Int.mul_le_mul_of_nonpos_left hm.1 (hv v (by simp))
      have h2 := ih vs hm.2 (by simp at hl; omega) (fun w hw => hv w (by simp [hw]))
      omega

/-- The list `[0, …, 0, v]` with `v` at index `j`. -/
def unitL : Nat → Int → List Int
  | 0, v => [v]
  | j + 1, v => 0 :: unitL j v

theorem dot_unitL : ∀ (j : Nat) (v : Int) (y : List Int), dot (unitL j v) y = v * y.getD j 0
  | 0, v, [] => by simp [unitL]
  | 0, v, w :: _ => by simp [unitL, dot]
  | j + 1, v, [] => by simp [unitL]
  | j + 1, v, w :: ws => by
    simp only [unitL, dot, List.getD_cons_succ]
    rw [dot_unitL j v ws]; omega

/-- `Σᵢ aᵢ uᵢ`, coefficientwise (zero coefficients skipped). -/
def lincomb : List Int → List (List Int) → List Int
  | a :: as, u :: us => if a == 0 then lincomb as us else addL (smulL a u) (lincomb as us)
  | _, _ => []

theorem dot_lincomb (as : List Int) (us : List (List Int)) (v : List Int) :
    dot (lincomb as us) v = dot as (us.map (dot · v)) := by
  induction as generalizing us with
  | nil => simp [lincomb]
  | cons a as ih =>
    cases us with
    | nil => simp [lincomb]
    | cons u us =>
      simp only [lincomb, List.map, dot]
      split
      · rename_i h
        simp only [beq_iff_eq] at h
        subst h
        rw [ih]; simp
      · rw [dot_addL, dot_smulL, ih]

theorem dot_cons_drop (a : Int) (as : List Int) : ∀ (y : List Int) (i : Nat),
    dot (a :: as) (y.drop i) = a * y.getD i 0 + dot as (y.drop (i + 1))
  | [], i => by simp
  | w :: ws, 0 => by simp [dot]
  | w :: ws, i + 1 => by
    simp only [List.drop_succ_cons, List.getD_cons_succ]
    exact dot_cons_drop a as ws i

/-- A claimed inverse of the gap forms' coefficient matrix, scaled by `D`: the combination `Σⱼ uᵢⱼ tⱼ` of the gap
forms, with `uᵢ` the i-th entry of `us`, is the form `D yᵢ + κᵢ`.  `invCheck` decides the claim, so where the
inverse comes from (`coneInv`) is not part of the trusted base. -/
structure ConeInv where
  D : Int
  us : List (List Int)
  κ : List Int

/-- `combo uᵢ ts = D yᵢ + κᵢ` for `i = i₀, i₀ + 1, …`, as forms. -/
def invRows (ts : List YForm) (D : Int) : Nat → List (List Int) → List Int → Bool
  | _, [], [] => true
  | i, u :: us, κ :: κs =>
    (combo u ts).k == κ && coeffEq (combo u ts).c (unitL i D) && invRows ts D (i + 1) us κs
  | _, _, _ => false

def invCheck (ts : List YForm) (ci : ConeInv) : Bool := 0 < ci.D && invRows ts ci.D 0 ci.us ci.κ

theorem invRows_sound (ts : List YForm) (D : Int) (y : List Int) :
    ∀ (i : Nat) (us : List (List Int)) (κs : List Int), invRows ts D i us κs = true →
    ∀ as : List Int, as.length ≤ us.length →
    dot (lincomb as us) (ts.map (·.eval y)) = dot as κs + D * dot as (y.drop i) := by
  intro i us
  induction us generalizing i with
  | nil =>
    intro κs _ as has
    have : as = [] := List.eq_nil_of_length_eq_zero (by simpa using has)
    subst this; simp [lincomb]
  | cons u us ih =>
    intro κs h as has
    cases κs with
    | nil => simp [invRows] at h
    | cons κ κs =>
      simp only [invRows, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hk, hc⟩, hr⟩ := h
      cases as with
      | nil => simp [lincomb]
      | cons a as =>
        have hu : dot u (ts.map (·.eval y)) = κ + D * y.getD i 0 := by
          rw [← eval_combo, YForm.eval, dot_coeffEq _ _ y hc, dot_unitL, hk]
        have hih := ih (i + 1) κs hr as (by simp at has; omega)
        rw [dot_lincomb] at hih ⊢
        simp only [List.map, dot, dot_cons_drop, hu, hih]
        rw [Int.mul_add, Int.mul_add, Int.mul_left_comm a D]; omega

theorem pos_of_mul_pos {D x : Int} (hD : 0 < D) (h : 0 < D * x) : 0 < x := by
  rcases Int.lt_or_le 0 x with h1 | h1
  · exact h1
  · have h2 : D * x ≤ D * 0 := Int.mul_le_mul_of_nonneg_left h1 (Int.le_of_lt hD)
    rw [Int.mul_zero] at h2; omega

theorem neg_of_mul_neg {D x : Int} (hD : 0 < D) (h : D * x < 0) : x < 0 := by
  rcases Int.lt_or_le x 0 with h1 | h1
  · exact h1
  · have h2 : D * 0 ≤ D * x := Int.mul_le_mul_of_nonneg_left h1 (Int.le_of_lt hD)
    rw [Int.mul_zero] at h2; omega

end BB6.Sym

namespace BB6.Sym

/-! ## Finding the cone inverse (untrusted; only `invCheck` is trusted)

The inverse of the gap forms' coefficient matrix `M` (first `k = ts.length` coordinates), scaled by `D = |det M|`, is
`±` the adjugate: `uᵢⱼ = ±Cⱼᵢ` with `Cⱼᵢ` the cofactor of `M` at row j, column i.  The functions are written for the
kernel (`decide +kernel`): plain structural recursion, no `List.range`, `getD` or `set`, whose library definitions are
slow to unfold. -/

/-- The first `k` coefficients of a coefficient list, padded with zeros. -/
def cutK : Nat → List Int → List Int
  | 0, _ => []
  | k + 1, [] => 0 :: cutK k []
  | k + 1, a :: as => a :: cutK k as

/-- The list without its entry at index `j`. -/
def dropAt {α : Type} : Nat → List α → List α
  | _, [] => []
  | 0, _ :: as => as
  | j + 1, a :: as => a :: dropAt j as

/-- Laplace expansion along the row `r` (column index `j`, sign `s`), given the determinant of the minors. -/
def rowDet (det : List (List Int) → Int) (rs : List (List Int)) : Nat → Int → List Int → Int
  | _, _, [] => 0
  | j, s, a :: as =>
    (if a == 0 then 0 else s * a * det (rs.map (dropAt j))) + rowDet det rs (j + 1) (-s) as

/-- The determinant of an `n × n` matrix given by its rows. -/
def detN : Nat → List (List Int) → Int
  | 0, _ => 1
  | _ + 1, [] => 0
  | n + 1, r :: rs => rowDet (detN n) rs 0 1 r

/-- Column i of the signed cofactors: `s Cⱼᵢ` for `j = j₀, j₀ + 1, …` (the sign `s` alternating with j, `r` a counter
for the rows), from the matrix `mi` without column i. -/
def cofCol (n : Nat) (mi : List (List Int)) : Nat → Int → List (List Int) → List Int
  | _, _, [] => []
  | j, s, _ :: r => s * detN n (dropAt j mi) :: cofCol n mi (j + 1) (-s) r

/-- The columns `i = i₀, i₀ + 1, …` of the signed cofactors (`r` a counter for the columns). -/
def cofCols (n : Nat) (m : List (List Int)) : Nat → Int → List (List Int) → List (List Int)
  | _, _, [] => []
  | i, s, _ :: r => cofCol n (m.map (dropAt i)) 0 s m :: cofCols n m (i + 1) (-s) r

/-- The inverse of the gap forms' matrix by Cramer's rule: `D = |det M|`, `uᵢ = sign(det M) · (C₀ᵢ, C₁ᵢ, …)` and
`κᵢ = Σⱼ uᵢⱼ tⱼ(0)`.  It depends only on `ts`, so the kernel evaluates it, and `invCheck` on it, once per cone (its
cache keys on the term) and every sign on that cone reuses them. -/
def coneInv (ts : List YForm) : ConeInv :=
  let k := ts.length
  let m := ts.map (cutK k ·.c)
  let d := detN k m
  let s : Int := if d < 0 then -1 else 1
  let us := cofCols (k - 1) m 0 s m
  ⟨s * d, us, us.map (dot · (ts.map (·.k)))⟩

/-! ## Signs on the cone -/

inductive Sgn | pos | neg | zero
  deriving Repr, DecidableEq

/-- The verdict from `D · p = Σⱼ μⱼ tⱼ + c` on the cone of `n` gap forms, with `e = c + Γ Σⱼ μⱼ`. -/
def sgnMu (μ : List Int) (e : Int) (n : Nat) : Option Sgn :=
  if μ.length ≤ n then
    if μ.all (0 ≤ ·) && decide (0 < e) then some .pos
    else if μ.all (· ≤ 0) && decide (e < 0) then some .neg
    else none
  else none

/-- The sign of `p` on the cone from a checked inverse: `μ = Σᵢ pᵢ uᵢ` and `c = D p₀ − Σᵢ pᵢ κᵢ` give
`D · p = Σⱼ μⱼ tⱼ + c`. -/
def sgnInv (p : YForm) (ts : List YForm) (Γ : Int) (ci : ConeInv) : Option Sgn :=
  if invCheck ts ci && decide (p.c.length ≤ ci.us.length) then
    sgnMu (lincomb p.c ci.us) (ci.D * p.k - dot p.c ci.κ + Γ * sumL (lincomb p.c ci.us)) ts.length
  else none

theorem sgnInv_sound (p : YForm) (ts : List YForm) (Γ : Int) (ci : ConeInv) (y : List Int) (hy : inCone ts Γ y) :
    (sgnInv p ts Γ ci = some .pos → 0 < p.eval y) ∧ (sgnInv p ts Γ ci = some .neg → p.eval y < 0) ∧
    (sgnInv p ts Γ ci = some .zero → p.eval y = 0) := by
  unfold sgnInv
  split
  · rename_i hc
    simp only [invCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hD, hinv⟩, hlen⟩ := hc
    have key := invRows_sound ts ci.D y 0 ci.us ci.κ hinv p.c hlen
    rw [List.drop_zero] at key
    have hvs : ∀ v ∈ ts.map (·.eval y), Γ ≤ v := by
      intro v hv
      simp only [List.mem_map] at hv
      obtain ⟨t, ht, rfl⟩ := hv
      exact hy t ht
    have hx : ci.D * p.eval y = ci.D * p.k - dot p.c ci.κ + dot (lincomb p.c ci.us) (ts.map (·.eval y)) := by
      rw [key]; unfold YForm.eval; rw [Int.mul_add]; omega
    unfold sgnMu
    split
    · rename_i hl
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · split at h
        · rename_i hp
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
          have := dot_ge _ _ Γ hp.1 (by simpa using hl) hvs
          exact pos_of_mul_pos hD (by omega)
        · split at h <;> cases h
      · split at h
        · cases h
        · split at h
          · rename_i hp
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
            have := dot_le _ _ Γ hp.1 (by simpa using hl) hvs
            exact neg_of_mul_neg hD (by omega)
          · cases h
      · split at h
        · cases h
        · split at h <;> cases h
    · simp
  · simp

/-- The sign of `p` at every point of the cone (gaps ≥ Γ), when decided. -/
def sgn (p : YForm) (ts : List YForm) (Γ : Int) : Option Sgn :=
  match p.constVal with
  | some v => if 0 < v then some .pos else if v < 0 then some .neg else some .zero
  | none => sgnInv p ts Γ (coneInv ts)

theorem sgn_sound (p : YForm) (ts : List YForm) (Γ : Int) (y : List Int) (hy : inCone ts Γ y) :
    (sgn p ts Γ = some .pos → 0 < p.eval y) ∧ (sgn p ts Γ = some .neg → p.eval y < 0) ∧
    (sgn p ts Γ = some .zero → p.eval y = 0) := by
  unfold sgn
  cases hcv : p.constVal with
  | some v =>
    have hv := eval_constVal p v hcv y
    simp only
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · split at h
      · omega
      · split at h <;> cases h
    · split at h
      · cases h
      · split at h
        · omega
        · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · omega
  | none => exact sgnInv_sound p ts Γ (coneInv ts) y hy

/-- `a < b` on the cone, when decided. -/
def ltDec (a b : YForm) (ts : List YForm) (Γ : Int) : Option Bool :=
  match sgn (b.sub a) ts Γ with
  | some .pos => some true
  | some _ => some false
  | none => none

theorem ltDec_sound (a b : YForm) (ts : List YForm) (Γ : Int) (y : List Int) (hy : inCone ts Γ y) (r : Bool)
    (h : ltDec a b ts Γ = some r) : (a.eval y < b.eval y ↔ r = true) := by
  have hs := sgn_sound (b.sub a) ts Γ y hy
  unfold ltDec at h
  cases hsg : sgn (b.sub a) ts Γ with
  | none => rw [hsg] at h; cases h
  | some s =>
    rw [hsg] at h
    cases s with
    | pos => cases h; have := hs.1 hsg; simp only [eval_sub] at this; simp; omega
    | neg => cases h; have := hs.2.1 hsg; simp only [eval_sub] at this; simp; omega
    | zero => cases h; have := hs.2.2 hsg; simp only [eval_sub] at this; simp; omega

/-- `a = b` on the cone, when decided. -/
def eqDec (a b : YForm) (ts : List YForm) (Γ : Int) : Option Bool :=
  match sgn (b.sub a) ts Γ with
  | some .zero => some true
  | some _ => some false
  | none => none

theorem eqDec_sound (a b : YForm) (ts : List YForm) (Γ : Int) (y : List Int) (hy : inCone ts Γ y) (r : Bool)
    (h : eqDec a b ts Γ = some r) : (a.eval y = b.eval y ↔ r = true) := by
  have hs := sgn_sound (b.sub a) ts Γ y hy
  unfold eqDec at h
  cases hsg : sgn (b.sub a) ts Γ with
  | none => rw [hsg] at h; cases h
  | some s =>
    rw [hsg] at h
    cases s with
    | pos => cases h; have := hs.1 hsg; simp only [eval_sub] at this; simp; omega
    | neg => cases h; have := hs.2.1 hsg; simp only [eval_sub] at this; simp; omega
    | zero => cases h; have := hs.2.2 hsg; simp only [eval_sub] at this; simp; omega

end BB6.Sym
