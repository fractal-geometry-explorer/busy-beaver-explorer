import BB6.Round

/-!
# Symbolic positions: integer affine forms on a leaf's coordinates

A certificate leaf is a residue class of start states, x = x0 + B y with y free.  Substituting it into the start
state makes every position an integer affine form in y (`YForm`: a constant and a coefficient list), and every step
of the mark model stays integral as long as a halving is only done when every coefficient is even.  The three kinds
of decision the model needs are:

* a residue (`d % 2`, `d % 4`): decided when every coefficient is divisible by the modulus (`modDec`);
* an equality with a constant: decided when every coefficient is zero (`constVal`);
* an order: decided on the cone of large gaps by a certificate `D · p = Σ μⱼ tⱼ + c` with `D > 0`, `μⱼ ≥ 0`, checked
  coefficient by coefficient (`posCheck`): then `p > 0` whenever every gap `tⱼ ≥ Γ` and `c + Γ Σ μⱼ > 0`.  How `μ`
  is found (`posCert`, fraction-free back substitution) is not part of the trusted base; only the check is.

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

/-- A positivity certificate: `D · p = Σ μⱼ tⱼ + c` as forms (checked coefficientwise and on the constant), `D > 0`,
`μⱼ ≥ 0`, and `c + Γ Σ μⱼ > 0`. -/
structure PosCert where
  D : Int
  μ : List Int
  deriving Repr

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
def posCheck (p : YForm) (ts : List YForm) (Γ : Int) (cert : PosCert) : Bool :=
  let r := (p.smul cert.D).sub (combo cert.μ ts)
  0 < cert.D && cert.μ.all (0 ≤ ·) && cert.μ.length ≤ ts.length && coeffEq r.c [] && 0 < r.k + Γ * sumL cert.μ

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

theorem posCheck_sound (p : YForm) (ts : List YForm) (Γ : Int) (cert : PosCert) (h : posCheck p ts Γ cert = true)
    (y : List Int) (hy : inCone ts Γ y) : 0 < p.eval y := by
  simp only [posCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hD, hμ⟩, hl⟩, hc⟩, hk⟩ := h
  have hr : ((p.smul cert.D).sub (combo cert.μ ts)).eval y = ((p.smul cert.D).sub (combo cert.μ ts)).k := by
    simp only [YForm.eval]; rw [dot_coeffEq _ [] y hc]; simp
  simp only [eval_sub, eval_smul, eval_combo] at hr
  have hvs : ∀ v ∈ ts.map (·.eval y), Γ ≤ v := by
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨t, ht, rfl⟩ := hv
    exact hy t ht
  have hge := dot_ge cert.μ (ts.map (·.eval y)) Γ hμ (by simpa using hl) hvs
  have hpos : 0 < cert.D * p.eval y := by omega
  rcases Int.lt_or_le 0 (p.eval y) with h1 | h1
  · exact h1
  · have h2 : cert.D * p.eval y ≤ cert.D * 0 := Int.mul_le_mul_of_nonneg_left h1 (Int.le_of_lt hD)
    rw [Int.mul_zero] at h2
    exact absurd hpos (Int.not_lt.mpr h2)

end BB6.Sym

namespace BB6.Sym

/-! ## Finding positivity certificates (untrusted search; only `posCheck` is trusted) -/

/-- A fraction `n / d` with `d > 0`, normalised. -/
structure Frac where
  n : Int
  d : Int
  deriving Repr, Inhabited

def Frac.norm (f : Frac) : Frac :=
  let g : Int := Int.ofNat (Nat.gcd f.n.natAbs f.d.natAbs)
  if g == 0 then ⟨0, 1⟩ else
  let s : Int := if f.d < 0 then -1 else 1
  ⟨s * (f.n / g), s * (f.d / g)⟩
def Frac.ofInt (n : Int) : Frac := ⟨n, 1⟩
def Frac.add (a b : Frac) : Frac := Frac.norm ⟨a.n * b.d + b.n * a.d, a.d * b.d⟩
def Frac.sub (a b : Frac) : Frac := Frac.norm ⟨a.n * b.d - b.n * a.d, a.d * b.d⟩
def Frac.mul (a b : Frac) : Frac := Frac.norm ⟨a.n * b.n, a.d * b.d⟩
def Frac.div (a b : Frac) : Frac := Frac.norm ⟨a.n * b.d, a.d * b.n⟩
def Frac.isZero (a : Frac) : Bool := a.n == 0

/-- Solve `Σⱼ λⱼ Mⱼᵢ = pᵢ` (i, j < k; `rows` are the coefficient lists of the gap forms) by Gauss–Jordan elimination on
the transposed system; `none` if singular. -/
def solveT (rows : List (List Int)) (p : List Int) (k : Nat) : Option (List Frac) := Id.run do
  -- augmented matrix A (k × (k+1)): A[i][j] = M[j][i], A[i][k] = p[i]
  let get (l : List Int) (i : Nat) : Int := l.getD i 0
  let mut A : Array (Array Frac) := #[]
  for i in [0:k] do
    let mut row : Array Frac := #[]
    for j in [0:k] do row := row.push (Frac.ofInt (get (rows.getD j []) i))
    row := row.push (Frac.ofInt (get p i))
    A := A.push row
  for col in [0:k] do
    -- pivot
    let mut piv := none
    for r in [col:k] do
      if piv.isNone && !(A[r]![col]!).isZero then piv := some r
    match piv with
    | none => return none
    | some r =>
      let tmp := A[r]!; A := A.set! r A[col]!; A := A.set! col tmp
      let pv := A[col]![col]!
      A := A.set! col (A[col]!.map (fun x => x.div pv))
      for r2 in [0:k] do
        if r2 != col then
          let f := A[r2]![col]!
          if !f.isZero then
            A := A.set! r2 ((A[r2]!.zip A[col]!).map (fun (x, y) => x.sub (f.mul y)))
  return some ((List.range k).map (fun i => A[i]![k]!))

def lcmL : List Int → Int
  | [] => 1
  | a :: as => let l := lcmL as; Int.ofNat (Nat.lcm a.natAbs l.natAbs)

/-- A candidate certificate for `p > 0`: `D = lcm` of the denominators of `λ`, `μ = D λ`. -/
def posCert (p : YForm) (ts : List YForm) : Option PosCert :=
  match solveT (ts.map (·.c)) p.c ts.length with
  | none => none
  | some lam =>
    let D := lcmL (lam.map (·.d))
    some ⟨D, lam.map (fun f => f.n * (D / f.d))⟩

/-! ## Signs on the cone -/

inductive Sgn | pos | neg | zero
  deriving Repr, DecidableEq

/-- The sign of `p` at every point of the cone (gaps ≥ Γ), when the certificates decide it. -/
def sgn (p : YForm) (ts : List YForm) (Γ : Int) : Option Sgn :=
  match p.constVal with
  | some v => if 0 < v then some .pos else if v < 0 then some .neg else some .zero
  | none =>
    match posCert p ts with
    | some c => if posCheck p ts Γ c then some .pos else
        match posCert p.neg ts with
        | some c' => if posCheck p.neg ts Γ c' then some .neg else none
        | none => none
    | none => none

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
  | none =>
    simp only
    cases hc : posCert p ts with
    | none => simp
    | some c =>
      simp only
      by_cases hpc : posCheck p ts Γ c = true
      · simp only [hpc, if_true]
        exact ⟨fun _ => posCheck_sound p ts Γ c hpc y hy, ⟨fun h => by simp at h, fun h => by simp at h⟩⟩
      · simp only [hpc, Bool.false_eq_true, if_false]
        cases hc' : posCert p.neg ts with
        | none => simp
        | some c' =>
          simp only
          by_cases hpc' : posCheck p.neg ts Γ c' = true
          · simp only [hpc', if_true]
            have := posCheck_sound p.neg ts Γ c' hpc' y hy
            rw [eval_neg] at this
            exact ⟨fun h => by simp at h, ⟨fun _ => by omega, fun h => by simp at h⟩⟩
          · simp [hpc']

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
