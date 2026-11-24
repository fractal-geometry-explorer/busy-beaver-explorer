/-!
# The 2-adic checker: k passes from n mod 2^(k+1), proved sound

The E-event map of every variant has the form (c, n) ↦ (c', (3n + d)/2), where c' and d depend only on c and
n mod 4 (`step`, with the table `Tab` indexed by context number and n mod 4).  So k passes from (c, n) depend only on
n mod 2^(k+1), and after them

    2^k · n_k = 3^k · n + B_k,        B_k a function of c and n mod 2^(k+1).

`solve` computes (c_k, B_k) from n mod 2^(k+1) by divide and conquer, as `c/orbit.c` does: k/2 passes from the low
k/2 + 1 bits, then the low k - k/2 + 1 bits of n_(k/2) from those, then the rest.  Its leaves (`leaf`) run up to
`L` passes one at a time on small numbers.  `seg` strings segments of L passes together on the full n, kept as a
list of L-bit digits so that no single number is longer than a few L bits (GMP, under Lean's `Nat`, caps a number
at about 1.37·10^11 bits, and n reaches several times that before the reported halts).

Everything here is about the abstract map; `Adic/Link.lean` ties it to the machines.  The theorems:

* `leaf_sound`, `solve_sound`: a `done c' B` result is what `iter` gives on every n with the given low bits, with
  2^k n_k = 3^k n + B; a `halt` result means `iter` meets a halting entry within k passes, on every such n.
* `seg_sound`: `seg ... = true` means the orbit of (c, val ds) meets a halting entry.
-/

namespace Adic

/-- What context `c` does with n mod 4 = r: the next context and d, so that n' = (3n + d)/2; or a halt; or
unknown (outside the table). -/
inductive Res where
  | go (c d : Nat)
  | halt
  | out
  deriving Inhabited, DecidableEq, Repr

/-- The table: entry 4c + r. -/
abbrev Tab := Array Res

@[inline] def get (t : Tab) (c r : Nat) : Res := t.getD (4 * c + r) .out

/-- One pass of the abstract map. -/
def step (t : Tab) (x : Nat × Nat) : Option (Nat × Nat) :=
  match get t x.1 (x.2 % 4) with
  | .go c d => if (3 * x.2 + d) % 2 = 0 then some (c, (3 * x.2 + d) / 2) else none
  | _ => none

/-- `k` passes. -/
def iter (t : Tab) : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, x => some x
  | k + 1, x =>
    match step t x with
    | none => none
    | some y => iter t k y

/-- The table has a halting entry at `x`. -/
def H (t : Tab) (x : Nat × Nat) : Prop := get t x.1 (x.2 % 4) = .halt

/-- The orbit of `x` meets a halting entry. -/
def MeetsHalt (t : Tab) (x : Nat × Nat) : Prop := ∃ j y, iter t j x = some y ∧ H t y

theorem iter_add (t : Tab) : ∀ (a b : Nat) (x : Nat × Nat), iter t (a + b) x = (iter t a x).bind (iter t b) := by
  intro a
  induction a with
  | zero => intro b x; simp [iter]
  | succ a ih =>
    intro b x
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [iter]
    cases step t x with
    | none => rfl
    | some y => exact ih b y

theorem meets_of_iter {t : Tab} {x y : Nat × Nat} {j : Nat} (h : iter t j x = some y) (m : MeetsHalt t y) :
    MeetsHalt t x := by
  obtain ⟨j', z, hz, hH⟩ := m
  exact ⟨j + j', z, by rw [iter_add, h]; exact hz, hH⟩

/-! ## Arithmetic -/

/-- `x % 2^n` without forming 2^n when x is shorter. -/
@[inline] def modP (x n : Nat) : Nat := if x >>> n = 0 then x else x - ((x >>> n) <<< n)

theorem modP_eq (x n : Nat) : modP x n = x % 2 ^ n := by
  unfold modP
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  split
  · next h =>
    have : x < 2 ^ n := by
      have := Nat.div_add_mod x (2 ^ n)
      rw [h, Nat.mul_zero, Nat.zero_add] at this
      have := Nat.mod_lt x (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ n)
      omega
    exact (Nat.mod_eq_of_lt this).symm
  · rw [Nat.mod_def, Nat.mul_comm]

theorem div_mod_of_mod {a b h m : Nat} (e : a % 2 ^ (h + m) = b % 2 ^ (h + m)) :
    a / 2 ^ h % 2 ^ m = b / 2 ^ h % 2 ^ m := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← Nat.pow_add, e]

theorem mod_of_mod_le {a b k m : Nat} (hm : m ≤ k) (e : a % 2 ^ k = b % 2 ^ k) : a % 2 ^ m = b % 2 ^ m := by
  rw [← Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 hm), ← Nat.mod_mod_of_dvd b (Nat.pow_dvd_pow 2 hm), e]

theorem lin_mod {a b k : Nat} (m d : Nat) (e : a % k = b % k) : (m * a + d) % k = (m * b + d) % k := by
  rw [Nat.add_mod, Nat.mul_mod, e, ← Nat.mul_mod, ← Nat.add_mod]

theorem mod4_of {a b k : Nat} (e : a % 2 ^ (k + 2) = b % 2 ^ (k + 2)) : a % 4 = b % 4 := by
  have := mod_of_mod_le (show 2 ≤ k + 2 by omega) e
  simpa using this

/-! ## Leaves: passes one at a time -/

/-- `leaf t k c x b p`: k passes from context c on the low bits x, accumulating B in b with p = 2^(passes so far). -/
def leaf (t : Tab) : Nat → Nat → Nat → Nat → Nat → Res
  | 0, c, _, b, _ => .go c b
  | k + 1, c, x, b, p =>
    match get t c (x % 4) with
    | .go c' d =>
      if (3 * x + d) % 2 = 0 then leaf t k c' ((3 * x + d) / 2) (3 * b + d * p) (2 * p) else .out
    | .halt => .halt
    | .out => .out

/-- The result of `leaf` and `solve`, as a `Res`: `go c B` = k passes done, ending in context c, with B = B_k. -/
def Spec (t : Tab) (k c x : Nat) (r : Res) (needB : Bool) : Prop :=
  ∀ N, N % 2 ^ (k + 1) = x % 2 ^ (k + 1) →
    (∀ c' B, r = .go c' B → ∃ N', iter t k (c, N) = some (c', N') ∧ (needB = true → 2 ^ k * N' = 3 ^ k * N + B)) ∧
    (r = .halt → ∃ j, j < k ∧ ∃ y, iter t j (c, N) = some y ∧ H t y)

theorem leaf_gen (t : Tab) : ∀ (k c x b p N M T : Nat), N % 2 ^ (k + 1) = x % 2 ^ (k + 1) → p * N = T * M + b →
    (∀ c' B, leaf t k c x b p = .go c' B →
      ∃ N', iter t k (c, N) = some (c', N') ∧ 2 ^ k * p * N' = 3 ^ k * T * M + B) ∧
    (leaf t k c x b p = .halt → ∃ j, j < k ∧ ∃ y, iter t j (c, N) = some y ∧ H t y) := by
  intro k
  induction k with
  | zero =>
    intro c x b p N M T _ inv
    refine ⟨?_, ?_⟩
    · intro c' B h
      simp only [leaf, Res.go.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨N, rfl, by simp [inv]⟩
    · intro h; simp [leaf] at h
  | succ k ih =>
    intro c x b p N M T hx inv
    have h4 : N % 4 = x % 4 := mod4_of hx
    cases hg : get t c (x % 4) with
    | halt =>
      refine ⟨?_, ?_⟩
      · intro c' B h; simp [leaf, hg] at h
      · intro _
        exact ⟨0, by omega, (c, N), rfl, by simp only [H]; rw [h4]; exact hg⟩
    | out =>
      refine ⟨?_, ?_⟩ <;> intro <;> simp_all [leaf]
    | go c1 d =>
      by_cases hp : (3 * x + d) % 2 = 0
      · have hN : (3 * N + d) % 2 = 0 := by
          have := mod_of_mod_le (show 1 ≤ k + 1 + 1 by omega) hx
          simp at this; omega
        have hs : step t (c, N) = some (c1, (3 * N + d) / 2) := by
          simp only [step]; rw [h4, hg]; simp [hN]
        have hx1 : (3 * N + d) / 2 % 2 ^ (k + 1) = (3 * x + d) / 2 % 2 ^ (k + 1) := by
          have e := lin_mod 3 d hx
          have := @div_mod_of_mod (3 * N + d) (3 * x + d) 1 (k + 1) (by rw [Nat.add_comm 1 (k + 1)]; exact e)
          simpa using this
        have inv1 : (2 * p) * ((3 * N + d) / 2) = (3 * T) * M + (3 * b + d * p) := by
          have e2 : 2 * ((3 * N + d) / 2) = 3 * N + d := by omega
          rw [Nat.mul_comm 2 p, Nat.mul_assoc, e2, Nat.mul_add, Nat.mul_left_comm, inv, Nat.mul_add,
            Nat.mul_assoc, Nat.mul_comm p d]
          omega
        obtain ⟨ih1, ih2⟩ := ih c1 ((3 * x + d) / 2) (3 * b + d * p) (2 * p) ((3 * N + d) / 2) M (3 * T) hx1 inv1
        have hl : leaf t (k + 1) c x b p = leaf t k c1 ((3 * x + d) / 2) (3 * b + d * p) (2 * p) := by
          simp [leaf, hg, hp]
        refine ⟨?_, ?_⟩
        · intro c' B h
          rw [hl] at h
          obtain ⟨N', h1, h2⟩ := ih1 c' B h
          refine ⟨N', by simp only [iter, hs]; exact h1, ?_⟩
          rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc (2 ^ k) 2 p, Nat.mul_assoc (3 ^ k) 3 T]
          exact h2
        · intro h
          rw [hl] at h
          obtain ⟨j, hj, y, h1, h2⟩ := ih2 h
          exact ⟨j + 1, by omega, y, by simp only [iter, hs]; exact h1, h2⟩
      · refine ⟨?_, ?_⟩ <;> intro <;> simp_all [leaf]

theorem leaf_sound (t : Tab) (k c x : Nat) : Spec t k c x (leaf t k c x 0 1) true := by
  intro N hN
  obtain ⟨h1, h2⟩ := leaf_gen t k c x 0 1 N N 1 hN (by simp)
  refine ⟨fun c' B h => ?_, h2⟩
  obtain ⟨N', e, r⟩ := h1 c' B h
  exact ⟨N', e, fun _ => by simpa using r⟩

theorem spec_weaken {t : Tab} {k c x : Nat} {r : Res} {nb : Bool} (h : Spec t k c x r true) : Spec t k c x r nb := by
  intro N hN
  obtain ⟨h1, h2⟩ := h N hN
  exact ⟨fun c' B e => let ⟨N', a, _⟩ := h1 c' B e; ⟨N', a, fun _ => by simp_all⟩, h2⟩

/-! ## Divide and conquer -/

/-- `solve t L f nb c x k`: k passes from context c on x ≡ n mod 2^(k+1), by halves down to `L` passes (at most f
levels deep); B is computed only when `nb` (the top call does not need it). -/
def solve (t : Tab) (L : Nat) : Nat → Bool → Nat → Nat → Nat → Res
  | 0, _, c, x, k => leaf t k c (modP x (k + 1)) 0 1
  | f + 1, nb, c, x, k =>
    if k ≤ L then leaf t k c (modP x (k + 1)) 0 1 else
    let h := k / 2
    match solve t L f true c (modP x (h + 1)) h with
    | .go c1 B1 =>
      let x1 := modP ((3 ^ h * modP x (k + 1) + B1) >>> h) (k - h + 1)
      match solve t L f nb c1 x1 (k - h) with
      | .go c2 B2 => .go c2 (if nb then 3 ^ (k - h) * B1 + (B2 <<< h) else 0)
      | r => r
    | r => r

theorem spec_leaf_modP (t : Tab) (k c x : Nat) (nb : Bool) : Spec t k c x (leaf t k c (modP x (k + 1)) 0 1) nb := by
  intro N hN
  apply spec_weaken (leaf_sound t k c (modP x (k + 1))) N
  rw [modP_eq, Nat.mod_mod]; exact hN

theorem solve_sound (t : Tab) (L : Nat) : ∀ f nb c x k, Spec t k c x (solve t L f nb c x k) nb := by
  intro f
  induction f with
  | zero => intro nb c x k; exact spec_leaf_modP t k c x nb
  | succ f ih =>
    intro nb c x k
    simp only [solve]
    split
    · exact spec_leaf_modP t k c x nb
    next hk =>
    intro N hN
    have hh : k / 2 + 1 ≤ k + 1 := by omega
    have hN1 : N % 2 ^ (k / 2 + 1) = modP x (k / 2 + 1) % 2 ^ (k / 2 + 1) := by
      rw [modP_eq, Nat.mod_mod]; exact mod_of_mod_le hh hN
    have S1 := ih true c (modP x (k / 2 + 1)) (k / 2) N hN1
    split
    next c1 B1 e1 =>
      obtain ⟨N1, i1, r1⟩ := S1.1 c1 B1 e1
      have r1 := r1 rfl
      -- the low bits of n_h
      have hX : N1 % 2 ^ (k - k / 2 + 1) =
          modP ((3 ^ (k / 2) * modP x (k + 1) + B1) >>> (k / 2)) (k - k / 2 + 1) % 2 ^ (k - k / 2 + 1) := by
        rw [modP_eq, Nat.mod_mod, Nat.shiftRight_eq_div_pow, modP_eq]
        have e : (3 ^ (k / 2) * N + B1) % 2 ^ (k / 2 + (k - k / 2 + 1)) =
            (3 ^ (k / 2) * (x % 2 ^ (k + 1)) + B1) % 2 ^ (k / 2 + (k - k / 2 + 1)) := by
          rw [show k / 2 + (k - k / 2 + 1) = k + 1 by omega]
          apply lin_mod; rw [Nat.mod_mod]; exact hN
        have := div_mod_of_mod e
        rw [← r1, Nat.mul_comm, Nat.mul_div_cancel _ (Nat.pow_pos (by decide))] at this
        exact this
      have S2 := ih nb c1 _ (k - k / 2) N1 hX
      split
      next c2 B2 e2 =>
        refine ⟨?_, fun h => by cases h⟩
        intro c' B h
        simp only [Res.go.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨N2, i2, r2⟩ := S2.1 c2 B2 e2
        refine ⟨N2, ?_, ?_⟩
        · rw [show k = k / 2 + (k - k / 2) by omega, iter_add, i1]; exact i2
        · intro hnb
          have r2 := r2 hnb
          simp only [hnb, ↓reduceIte, Nat.shiftLeft_eq]
          have hk2 : 2 ^ k = 2 ^ (k / 2) * 2 ^ (k - k / 2) := by rw [← Nat.pow_add]; congr 1; omega
          have hk3 : 3 ^ k = 3 ^ (k - k / 2) * 3 ^ (k / 2) := by rw [← Nat.pow_add]; congr 1; omega
          rw [hk2, Nat.mul_assoc, r2, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (k / 2)) (3 ^ (k - k / 2)),
            Nat.mul_assoc, r1, Nat.mul_add, hk3, Nat.mul_assoc, Nat.mul_comm B2]
          omega
      next r e2 =>
        refine ⟨fun c' B h => absurd h (e2 c' B), fun h => ?_⟩
        obtain ⟨j, hj, y, iy, hy⟩ := S2.2 h
        exact ⟨k / 2 + j, by omega, y, by rw [iter_add, i1]; exact iy, hy⟩
    next r e1 =>
      refine ⟨fun c' B h => absurd h (e1 c' B), fun h => ?_⟩
      obtain ⟨j, hj, y, iy, hy⟩ := S1.2 h
      exact ⟨j, by omega, y, iy, hy⟩

/-- `solve` finds a halt within k passes: the orbit of (c, n) meets a halting entry, for every n with these low
bits. -/
theorem meets_of_solve (t : Tab) (L f c x k N : Nat) (nb : Bool) (h : solve t L f nb c x k = .halt)
    (hN : N % 2 ^ (k + 1) = x % 2 ^ (k + 1)) : MeetsHalt t (c, N) := by
  obtain ⟨j, _, y, iy, hy⟩ := (solve_sound t L f nb c x k N hN).2 h
  exact ⟨j, y, iy, hy⟩

/-! ## Segments, with n as a list of L-bit digits -/

/-- The value of a little-endian digit list in base 2^W. -/
def val (W : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + 2 ^ W * val W ds

/-- The digits of `c` (at most `f` of them split off; the rest left as one digit). -/
def norm (W : Nat) : Nat → Nat → List Nat
  | 0, c => if c = 0 then [] else [c]
  | f + 1, c => if c = 0 then [] else modP c W :: norm W f (c >>> W)

theorem val_norm (W : Nat) : ∀ f c, val W (norm W f c) = c := by
  intro f
  induction f with
  | zero => intro c; unfold norm; split <;> simp_all [val]
  | succ f ih =>
    intro c; unfold norm; split
    · simp_all [val]
    · simp only [val, ih, modP_eq, Nat.shiftRight_eq_div_pow]
      have := Nat.div_add_mod c (2 ^ W); omega

/-- `m * val ds + c`, as digits. -/
def mulAdd (W m : Nat) : List Nat → Nat → List Nat
  | [], c => norm W 4 c
  | d :: ds, c => let s := m * d + c; modP s W :: mulAdd W m ds (s >>> W)

theorem val_mulAdd (W m : Nat) : ∀ ds c, val W (mulAdd W m ds c) = m * val W ds + c := by
  intro ds
  induction ds with
  | nil => intro c; simp [mulAdd, val_norm, val]
  | cons d ds ih =>
    intro c
    simp only [mulAdd, val, ih, modP_eq, Nat.shiftRight_eq_div_pow]
    have := Nat.div_add_mod (m * d + c) (2 ^ W)
    rw [Nat.mul_add (2 ^ W), Nat.mul_add m d, Nat.mul_left_comm m (2 ^ W)]
    omega

/-- The low W + 1 bits of the value (for W ≥ 1). -/
@[inline] def low (W : Nat) : List Nat → Nat
  | [] => 0
  | [d] => d
  | d :: e :: _ => d + (e <<< W)

theorem low_mod (W : Nat) (hW : 1 ≤ W) (ds : List Nat) : val W ds % 2 ^ (W + 1) = low W ds % 2 ^ (W + 1) := by
  match ds with
  | [] => rfl
  | [d] => simp [val, low]
  | d :: e :: es =>
    simp only [val, low, Nat.shiftLeft_eq]
    have h : 2 ^ (W + 1) ∣ 2 ^ W * (2 ^ W * val W es) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add]
      exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_right _ _)
    obtain ⟨q, hq⟩ := h
    rw [Nat.mul_add, hq, Nat.mul_comm e, ← Nat.add_assoc, Nat.add_mul_mod_self_left]

/-- Drop the low digit when it is below 2^W (so the value is divided by 2^W exactly up to the digit). -/
def shr (W : Nat) : List Nat → Option (List Nat)
  | [] => some []
  | d :: ds => if d >>> W = 0 then some ds else none

theorem val_shr (W : Nat) {ds es : List Nat} (h : shr W ds = some es) : val W ds / 2 ^ W = val W es := by
  match ds, h with
  | [], h => simp only [shr, Option.some.injEq] at h; subst h; simp [val]
  | d :: ds, h =>
    simp only [shr] at h
    split at h
    · next hd =>
      simp only [Option.some.injEq] at h; subst h
      rw [Nat.shiftRight_eq_div_pow] at hd
      have hlt : d < 2 ^ W := by
        have := Nat.div_add_mod d (2 ^ W); have := Nat.mod_lt d (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ W)
        rw [hd] at *; omega
      simp only [val]
      rw [Nat.add_comm, Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2)), Nat.div_eq_of_lt hlt, Nat.add_zero]
    · cases h

/-- `s` segments of `L` passes each, from context c on n = val L ds (m = 3^L); true when a halting entry is met. -/
def seg (t : Tab) (L Lf f m : Nat) : Nat → Nat → List Nat → Bool
  | 0, _, _ => false
  | s + 1, c, ds =>
    match solve t Lf f true c (low L ds) L with
    | .halt => true
    | .go c' B =>
      match shr L (mulAdd L m ds B) with
      | some es => seg t L Lf f m s c' es
      | none => false
    | .out => false

theorem seg_sound (t : Tab) (L Lf f : Nat) (hL : 1 ≤ L) :
    ∀ s c ds, seg t L Lf f (3 ^ L) s c ds = true → MeetsHalt t (c, val L ds) := by
  intro s
  induction s with
  | zero => intro c ds h; simp [seg] at h
  | succ s ih =>
    intro c ds h
    simp only [seg] at h
    have hN := low_mod L hL ds
    have S := solve_sound t Lf f true c (low L ds) L (val L ds) hN
    split at h
    next e => exact meets_of_solve t Lf f c _ L _ true e hN
    next c' B e =>
      split at h
      next es hs =>
        obtain ⟨N', i1, r1⟩ := S.1 c' B e
        have r1 := r1 rfl
        have hv := val_shr L hs
        rw [val_mulAdd, ← r1, Nat.mul_comm, Nat.mul_div_cancel _ (Nat.pow_pos (by decide))] at hv
        have m := ih c' es h
        rw [← hv] at m
        exact meets_of_iter i1 m
      next => cases h
    next => cases h

end Adic
