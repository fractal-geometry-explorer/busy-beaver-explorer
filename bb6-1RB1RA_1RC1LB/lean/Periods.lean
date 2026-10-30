import Cycles

/-!
# The period factors are 1, 2, 4 or 5

Over a period of a cycling bottom `C` (`bs m C = C`), the next level's block goes from `q` to `topv m C q`, the
**pass map** `F` (`bs_iter`).  The bottom with one more level then has period `m * L`, where `L` is the least period
of the level's block under `F`; in the run, `L` is always 1, 2, 4 or 5.  This file proves that it must be, and says
which.

* **Mod 5 a wave is affine.**  A wave `h` takes the block `p` to `(d + 5) / 2` or `d / 2` with `d = p + h`; both are
  `3 d` mod 5, since `2 · 3 = 6 ≡ 1`.  An add `a` takes `p` to `p + a`.  So mod 5 the pass map is
  `r ↦ a r + b` with `a = 3^W` mod 5, `W` the waves in a period, and `b = F 0` mod 5 (`topv_mod`, `topm_aff`).
* **A cycle has distinct residues** (`cycle_residues`): if the bottom passes on at least one wave per period and `x`
  lies on a cycle of `F`, no other point of that cycle is `x` mod 5.  Two blocks `y = x + 5 c` stay `5 c'` apart with
  `c' ≤ c`, and `c' < c` after a wave if `c ≥ 2` (`lev_shift`).  Around a cycle `c` cannot shrink, so `c = 1` for
  ever, and then `F^j` shifts the cycle by 5 each time, which is absurd.
* **So `L` is the period of an affine map of `ℤ/5`** (`period_factor`): `L ∈ {1, 2, 4, 5}`; `L ∈ {1, 4}` if `W` is
  odd, `L ∈ {1, 2}` if `W ≡ 2` mod 4, and if `W ≡ 0` mod 4, `L = 5` exactly when `b ≠ 0` (else `L = 1`).  `L = 1`
  exactly when the block's residue is the fixed point of `r ↦ a r + b`.

Nothing here says which residue the block has; that is set by its past.  Kernel only.
-/

namespace BB6b

open TM

/-! ## Iteration -/

theorem iter_succ' (F : Nat → Nat) (k q : Nat) : iter F (k + 1) q = F (iter F k q) := by
  rw [Nat.add_comm, iter_add]; rfl

theorem iter_mul (F : Nat → Nat) (n a : Nat) (ha : iter F n a = a) : ∀ q, iter F (q * n) a = a := by
  intro q
  induction q with
  | zero => simp [iter]
  | succ q ih => rw [Nat.succ_mul, iter_add, ha, ih]

/-! ## Mod 5 -/

/-- What an event does to a block's residue mod 5. -/
def am : Ev → Nat → Nat
  | .none, r => r % 5
  | .add a, r => (r + a) % 5
  | .wave h, r => 3 * (r + h) % 5

theorem lev_mod (x : Nat) : ∀ e, (lev x e).1 % 5 = am e (x % 5)
  | .none => by simp [lev, am]
  | .add a => by simp only [lev, am]; omega
  | .wave h => by simp only [lev, am]; split <;> (try simp only) <;> omega

/-- The residue of one more level after `i` super steps of the bottom `C` (`topv` mod 5). -/
def topm : Nat → List Nat → Nat → Nat
  | 0, _, r => r
  | i + 1, C, r => topm i (bstep C).1 (am (bstep C).2.1 r)

theorem topv_mod : ∀ (i : Nat) (C : List Nat) (x : Nat), topv i C x % 5 = topm i C (x % 5) := by
  intro i
  induction i with
  | zero => intro C x; rfl
  | succ i ih => intro C x; simp only [topv, topm]; rw [ih, lev_mod]

theorem am_lt (e : Ev) (r : Nat) : am e r < 5 := by cases e <;> simp only [am] <;> omega

theorem topm_lt : ∀ (i : Nat) (C : List Nat) (r : Nat), r < 5 → topm i C r < 5 := by
  intro i
  induction i with
  | zero => intro C r h; exact h
  | succ i ih => intro C r _; exact ih _ _ (am_lt _ _)

/-- The waves the bottom passes on in `i` super steps. -/
def wc : Nat → List Nat → Nat
  | 0, _ => 0
  | i + 1, C => wc i (bstep C).1 + (if isWave (bstep C).2.1 then 1 else 0)

/-- `3^n` mod 5. -/
def mul3 : Nat → Nat
  | 0 => 1
  | n + 1 => 3 * mul3 n % 5

theorem mul3_eq : ∀ n, (n % 4 = 0 → mul3 n = 1) ∧ (n % 4 = 1 → mul3 n = 3) ∧ (n % 4 = 2 → mul3 n = 4) ∧
    (n % 4 = 3 → mul3 n = 2) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ => rfl, by omega, by omega, by omega⟩
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [mul3]
    · rw [h3 (by omega)]
    · rw [h0 (by omega)]
    · rw [h1 (by omega)]
    · rw [h2 (by omega)]

theorem mul3_lt (n : Nat) : mul3 n < 5 ∧ 0 < mul3 n := by
  obtain ⟨h0, h1, h2, h3⟩ := mul3_eq n
  have : n % 4 < 4 := Nat.mod_lt _ (by omega)
  by_cases a : n % 4 = 0
  · rw [h0 a]; omega
  by_cases b : n % 4 = 1
  · rw [h1 b]; omega
  by_cases c : n % 4 = 2
  · rw [h2 c]; omega
  · rw [h3 (by omega)]; omega

/-- The affine map `r ↦ a r + b` of `ℤ/5`. -/
def af (a b r : Nat) : Nat := (a * r + b) % 5

theorem af_none : ∀ a, a < 5 → ∀ b, b < 5 → ∀ r, r < 5 → af a b r = af a (af a b 0) r := by decide

theorem af_add : ∀ a, a < 5 → ∀ b, b < 5 → ∀ s, s < 5 → ∀ r, r < 5 →
    af a b ((r + s) % 5) = af a (af a b ((0 + s) % 5)) r := by decide

theorem af_wave : ∀ a, a < 5 → ∀ b, b < 5 → ∀ s, s < 5 → ∀ r, r < 5 →
    af a b (3 * (r + s) % 5) = af (3 * a % 5) (af a b (3 * (0 + s) % 5)) r := by decide

/-- **Mod 5 the pass map is affine**, `r ↦ 3^W r + b` with `W` the waves passed on and `b` the image of 0. -/
theorem topm_aff : ∀ (i : Nat) (C : List Nat) (r : Nat), r < 5 → topm i C r = af (mul3 (wc i C)) (topm i C 0) r := by
  intro i
  induction i with
  | zero => intro C r h; simp only [topm, wc, mul3, af]; omega
  | succ i ih =>
    intro C r hr
    simp only [topm, wc]
    have ha := mul3_lt (wc i (bstep C).1)
    have hb := topm_lt i (bstep C).1 0 (by omega)
    rw [ih _ _ (am_lt _ _), ih _ (am _ 0) (am_lt _ _)]
    generalize (bstep C).2.1 = e
    cases e with
    | none =>
      simp only [am, isWave, Bool.false_eq_true, ite_false, Nat.add_zero, Nat.zero_mod, Nat.mod_eq_of_lt hr]
      exact af_none _ ha.1 _ hb _ hr
    | add v =>
      simp only [am, isWave, Bool.false_eq_true, ite_false, Nat.add_zero]
      rw [show (r + v) % 5 = (r + v % 5) % 5 by omega, show (0 + v) % 5 = (0 + v % 5) % 5 by omega]
      exact af_add _ ha.1 _ hb _ (Nat.mod_lt _ (by omega)) _ hr
    | wave h =>
      simp only [am, isWave, ite_true]
      rw [show 3 * (r + h) % 5 = 3 * (r + h % 5) % 5 by omega, show 3 * (0 + h) % 5 = 3 * (0 + h % 5) % 5 by omega]
      exact af_wave _ ha.1 _ hb _ (Nat.mod_lt _ (by omega)) _ hr

/-- The pass map's iterates mod 5 are the affine map's iterates. -/
theorem iter_mod (m : Nat) (C : List Nat) (x : Nat) :
    ∀ k, iter (topv m C) k x % 5 = iter (af (mul3 (wc m C)) (topm m C 0)) k (x % 5) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iter_succ', iter_succ', topv_mod, ih]
    exact topm_aff _ _ _ (by rw [← ih]; exact Nat.mod_lt _ (by omega))

/-! ## Blocks 5 apart -/

/-- Two blocks `5 c` apart are `5 c'` apart after an event, `c' ≤ c`, and `c' < c` after a wave if `c ≥ 2`. -/
theorem lev_shift (x c : Nat) : ∀ e, ∃ c', (lev (x + 5 * c) e).1 = (lev x e).1 + 5 * c' ∧ c' ≤ c ∧
    (isWave e = true → 2 ≤ c → c' < c)
  | .none => ⟨c, by simp [lev], Nat.le_refl _, by simp [isWave]⟩
  | .add a => ⟨c, by simp only [lev]; omega, Nat.le_refl _, by simp [isWave]⟩
  | .wave h => by
    simp only [lev]
    by_cases hy : (x + 5 * c + h) % 2 = 1 <;> by_cases hx : (x + h) % 2 = 1
    · simp only [hy, hx, ↓reduceIte]; exact ⟨c / 2, by omega, by omega, fun _ _ => by omega⟩
    · simp only [hy, hx, ↓reduceIte]; exact ⟨(c + 1) / 2, by omega, by omega, fun _ _ => by omega⟩
    · simp only [hy, hx, ↓reduceIte]; exact ⟨(c - 1) / 2, by omega, by omega, fun _ _ => by omega⟩
    · simp only [hy, hx, ↓reduceIte]; exact ⟨c / 2, by omega, by omega, fun _ _ => by omega⟩

theorem topv_shift : ∀ (i : Nat) (C : List Nat) (x c : Nat), ∃ c', topv i C (x + 5 * c) = topv i C x + 5 * c' ∧
    c' ≤ c ∧ (hasW i C = true → 2 ≤ c → c' < c) := by
  intro i
  induction i with
  | zero => intro C x c; exact ⟨c, rfl, Nat.le_refl _, by simp [hasW]⟩
  | succ i ih =>
    intro C x c
    obtain ⟨c₁, h₁, l₁, s₁⟩ := lev_shift x c (bstep C).2.1
    obtain ⟨c₂, h₂, l₂, s₂⟩ := ih (bstep C).1 (lev x (bstep C).2.1).1 c₁
    refine ⟨c₂, by simp only [topv]; rw [h₁, h₂], by omega, fun hw hc => ?_⟩
    simp only [hasW, Bool.or_eq_true] at hw
    rcases hw with hw | hw
    · have := s₁ hw hc; omega
    · by_cases h : 2 ≤ c₁
      · have := s₂ hw h; omega
      · omega

/-- A map that keeps blocks `5 c` apart `5 c'` apart, `c' ≤ c`, with `c' < c` if `c ≥ 2`, has no cycle through two
blocks 5·e apart with the upper one an image of the lower. -/
theorem no_shift_cycle (F : Nat → Nat)
    (hF : ∀ x c, ∃ c', F (x + 5 * c) = F x + 5 * c' ∧ c' ≤ c ∧ (2 ≤ c → c' < c))
    (a n j e : Nat) (hn : 0 < n) (ha : iter F n a = a) (hj : iter F j a = a + 5 * e) (he : 0 < e) : False := by
  have hy : ∀ q, iter F (q * n) (a + 5 * e) = a + 5 * e := by
    apply iter_mul
    rw [← hj, ← iter_add, Nat.add_comm, iter_add, ha]
  -- once 5 c apart, always at most 5 c apart
  have reach : ∀ t k c, iter F k (a + 5 * e) = iter F k a + 5 * c →
      ∃ c', c' ≤ c ∧ iter F (k + t) (a + 5 * e) = iter F (k + t) a + 5 * c' := by
    intro t
    induction t with
    | zero => intro k c h; exact ⟨c, Nat.le_refl _, h⟩
    | succ t ih =>
      intro k c h
      obtain ⟨c₁, l₁, h₁⟩ := ih k c h
      obtain ⟨c₂, h₂, l₂, _⟩ := hF (iter F (k + t) a) c₁
      refine ⟨c₂, by omega, ?_⟩
      rw [← Nat.add_assoc, iter_succ', iter_succ', h₁, h₂]
  -- after one step and n - 1 more, back at distance 5 e: so e did not shrink, and e = 1
  obtain ⟨e₁, h₁, l₁, s₁⟩ := hF a e
  have he1 : e = 1 := by
    obtain ⟨c', l', h'⟩ := reach (n - 1) 1 e₁ (by rw [iter_succ', iter_succ']; exact h₁)
    rw [show 1 + (n - 1) = 1 * n by omega, hy, iter_mul F n a ha] at h'
    by_cases h2 : 2 ≤ e
    · have := s₁ h2; omega
    · omega
  subst he1
  -- so the two stay exactly 5 apart for ever
  have stay : ∀ k, iter F k (a + 5 * 1) = iter F k a + 5 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      obtain ⟨c, hc, lc, _⟩ := hF (iter F k a) 1
      rw [iter_succ', iter_succ', ih, hc]
      by_cases h0 : c = 0
      · exfalso
        obtain ⟨c', l', h'⟩ := reach ((k + 1) * n - (k + 1)) (k + 1) 0
          (by rw [iter_succ', iter_succ', ih, hc, h0])
        have hk : k + 1 ≤ (k + 1) * n := Nat.le_mul_of_pos_right _ hn
        rw [show k + 1 + ((k + 1) * n - (k + 1)) = (k + 1) * n by omega, hy, iter_mul F n a ha] at h'
        omega
      · rw [show c = 1 by omega]
  -- then F^j moves a by 5 each time, but F^(n j) = a
  have walk : ∀ q, iter F (q * j) a = a + 5 * q := by
    intro q
    induction q with
    | zero => simp [iter]
    | succ q ih => rw [Nat.succ_mul, iter_add, hj, stay, ih]; omega
  have := walk n
  rw [Nat.mul_comm, iter_mul F n a ha] at this
  omega

/-- **The blocks of a cycle of the pass map have distinct residues mod 5**, if the bottom passes a wave on. -/
theorem cycle_residues (m : Nat) (C : List Nat) (hw : hasW m C = true) (x n : Nat) (hn : 0 < n)
    (hx : iter (topv m C) n x = x) (j : Nat) (hj : iter (topv m C) j x % 5 = x % 5) : iter (topv m C) j x = x := by
  have hF : ∀ y c, ∃ c', topv m C (y + 5 * c) = topv m C y + 5 * c' ∧ c' ≤ c ∧ (2 ≤ c → c' < c) := by
    intro y c
    obtain ⟨c', h, l, s⟩ := topv_shift m C y c
    exact ⟨c', h, l, s hw⟩
  generalize hy : iter (topv m C) j x = y at hj
  by_cases hxy : x ≤ y
  · obtain ⟨e, he⟩ : ∃ e, y = x + 5 * e := ⟨(y - x) / 5, by omega⟩
    by_cases h0 : e = 0
    · omega
    · exact (no_shift_cycle _ hF x n j e hn hx (by rw [hy, he]) (by omega)).elim
  · obtain ⟨e, he⟩ : ∃ e, x = y + 5 * e := ⟨(x - y) / 5, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hyc : iter (topv m C) (n' + 1) y = y := by
      rw [← hy, ← iter_add, Nat.add_comm, iter_add, hx]
    have hback : iter (topv m C) (n' * j) y = y + 5 * e := by
      rw [← he, ← hy, ← iter_add, ← Nat.succ_mul, Nat.mul_comm, iter_mul _ _ _ hx]
    exact (no_shift_cycle _ hF y (n' + 1) (n' * j) e hn hyc hback (by omega)).elim

/-! ## The period factor -/

/-- The least period of `r` under `r ↦ a r + b`, found by trying 1, 2, 4. -/
def lp (a b r : Nat) : Nat :=
  if af a b r = r then 1 else if iter (af a b) 2 r = r then 2 else if iter (af a b) 4 r = r then 4 else 5

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
theorem lp_spec : ∀ a, a < 5 → ∀ b, b < 5 → ∀ r, r < 5 → 0 < a →
    0 < lp a b r ∧ iter (af a b) (lp a b r) r = r ∧ ∀ k, k < lp a b r → 0 < k → iter (af a b) k r ≠ r := by decide

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
theorem lp_class : ∀ a, a < 5 → ∀ b, b < 5 → ∀ r, r < 5 →
    (lp a b r = 1 ↔ af a b r = r) ∧
    ((a = 3 ∨ a = 2) → lp a b r = 1 ∨ lp a b r = 4) ∧
    (a = 4 → lp a b r = 1 ∨ lp a b r = 2) ∧
    (a = 1 → (lp a b r = 5 ↔ b ≠ 0) ∧ (lp a b r = 1 ↔ b = 0)) := by decide

/-- **The period factor.**  If the bottom `C` passes a wave on in its `m` super steps and the next level's block `x`
has least period `L` under the pass map `topv m C`, then `L` is the least period of `x mod 5` under
`r ↦ 3^W r + b` (`W = wc m C` the waves passed on, `b = topm m C 0`): it is 1, 2, 4 or 5, which ones as stated, and 1
exactly when `x mod 5` is that map's fixed point. -/
theorem period_factor (m : Nat) (C : List Nat) (hw : hasW m C = true) (x L : Nat) (hL : 0 < L)
    (hx : iter (topv m C) L x = x) (hmin : ∀ k, 0 < k → k < L → iter (topv m C) k x ≠ x) :
    L = lp (mul3 (wc m C)) (topm m C 0) (x % 5) ∧
    (L = 1 ∨ L = 2 ∨ L = 4 ∨ L = 5) ∧
    (L = 1 ↔ topm m C (x % 5) = x % 5) ∧
    (wc m C % 2 = 1 → L = 1 ∨ L = 4) ∧
    (wc m C % 4 = 2 → L = 1 ∨ L = 2) ∧
    (wc m C % 4 = 0 → (L = 5 ↔ topm m C 0 ≠ 0) ∧ (L = 1 ↔ topm m C 0 = 0)) := by
  have ha := mul3_lt (wc m C)
  have hb := topm_lt m C 0 (by omega)
  have hr : x % 5 < 5 := Nat.mod_lt _ (by omega)
  obtain ⟨p0, p1, p2⟩ := lp_spec _ ha.1 _ hb _ hr ha.2
  have hcl := lp_class _ ha.1 _ hb _ hr
  generalize hl : lp (mul3 (wc m C)) (topm m C 0) (x % 5) = l at p0 p1 p2 hcl
  have im := iter_mod m C x
  -- F^l x ≡ x, so F^l x = x, so L ≤ l
  have hle : L ≤ l := by
    have h := cycle_residues m C hw x L hL hx l (by rw [im]; exact p1)
    by_cases h' : l < L
    · exact absurd h (hmin l p0 h')
    · omega
  -- F^L x = x gives the affine map back at x mod 5 after L, so l ≤ L
  have hge : l ≤ L := by
    by_cases h' : L < l
    · exact absurd (by rw [← im, hx]) (p2 L h' hL)
    · omega
  have hL' : L = l := by omega
  subst hL'
  have hfix : topm m C (x % 5) = af (mul3 (wc m C)) (topm m C 0) (x % 5) := topm_aff _ _ _ hr
  have h3 := mul3_eq (wc m C)
  refine ⟨rfl, ?_, by rw [hfix]; exact hcl.1, fun h => hcl.2.1 ?_, fun h => hcl.2.2.1 ?_,
    fun h => hcl.2.2.2 ?_⟩
  · rw [← hl]; unfold lp; split <;> (try split) <;> (try split) <;> simp
  · by_cases h' : wc m C % 4 = 1
    · exact Or.inl (h3.2.1 h')
    · exact Or.inr (h3.2.2.2 (by omega))
  · exact h3.2.2.1 h
  · exact h3.1 h

/-- **One more level multiplies the period by 1, 2, 4 or 5.**  If the bottom `C` comes back after `m` super steps and
passes a wave on meanwhile, and the next level's block `q` has least period `L` under the pass map, then the bottom
with that level comes back after `L * m` super steps, with `L` as in `period_factor`. -/
theorem level_period (m : Nat) (C : List Nat) (hC : bs m C = C) (hw : hasW m C = true) (q L : Nat) (hL : 0 < L)
    (hq : iter (topv m C) L q = q) (hmin : ∀ k, 0 < k → k < L → iter (topv m C) k q ≠ q) :
    bs (L * m) (C ++ [q]) = C ++ [q] ∧ (L = 1 ∨ L = 2 ∨ L = 4 ∨ L = 5) := by
  refine ⟨by rw [bs_iter C m hC, hq], (period_factor m C hw q L hL hq hmin).2.1⟩

/-! ## On the orbit

The bottom levels of the orbit from blank tape (`cycle₁`–`cycle₃` of `Cycles.lean`, which also check the periods
directly).  Level 0 receives one wave a super step (`W = 1`, so `L ∈ {1, 4}`), and its block 12 is not at the fixed
residue: `L = 4`.  Level 1 (block 26 below [12]) receives two waves per period: `L = 2`.  Level 2 (block 39 below
[12, 27]) receives three: `L = 4`.  The rule for the further levels is checked by `c/superrun.c -r`. -/

theorem rule₁ : wc 1 [] = 1 ∧ topm 1 [] 0 = 0 ∧ lp (mul3 1) (topm 1 [] 0) (12 % 5) = 4 := by decide

theorem rule₂ : wc 4 [12] = 2 ∧ topm 4 [12] 0 = 3 ∧ lp (mul3 2) (topm 4 [12] 0) (26 % 5) = 2 := by decide

theorem rule₃ : bs 8 [12, 27] = [12, 27] ∧ wc 8 [12, 27] = 3 ∧ lp (mul3 3) (topm 8 [12, 27] 0) (39 % 5) = 4 := by
  decide

end BB6b
