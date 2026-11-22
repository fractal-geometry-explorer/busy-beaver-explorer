import Hop
import XorLucas

/-!
# Which gaps the sweeps and the jumps can turn into the danger pattern

Read the gap after a `10` defect as a power series over GF(2), with the defect as the constant term:
`W = 1 + g0 z + g1 z^2 + ...` (`ser`, `y = 1`, `x = 0`).  `Hop.lean` proves what one deep sweep does to the words:

* `ser_shielded`: a shielded sweep (`x` before the defect) multiplies `W` by `1 + z` (`mz`), on every word the old gap
  determines;
* `ser_jump`: a jump (`y` before the defect) over `y^j x^(a+1)` leaves `(1 + z) C`, where `C` is the rest of the gap;
  with the `j + a + 1` shielded sweeps that `clock` then forces, jump to jump is `F(W) = (1 + z)^L C`, `L = j + a + 2`
  (`Fj`).

The new results are about the inverse of `(1 + z)^t`:

* `mzi_mask`: `(1 + z)^t` turns the series `mask t` (coefficient `k` is `disj k t`: `k` and `t` share no binary 1, i.e.
  `C(t + k, k)` is odd) into `1 + z + z^2 + ...`.  This is `(1 + z)^(-(t+1))`, and Pascal's rule is the whole proof.
* `mzi_agree`: multiplying by `(1 + z)^t` keeps and reflects agreement on the first `r` coefficients.
* `reach_ones`: so **after `t` shielded sweeps the first `r` words of the gap (defect included) are all `y` iff they
  were `mask t`**.  With `mask_period` (`mask (t + 2^b) = mask t` below `2^b`) a gap of fewer than `2^b` words ever
  becomes all `y` iff it is one of the `2^b` series `mask s`, `s < 2^b` (`pascal_reach`): the rows of Pascal's
  triangle mod 2 of the README, now proved.
* `next_jump_run`: at a jump over `y^j x^(a+1)` with rest `C`, **the run of `y`s at the next jump covers the first `r`
  coefficients iff `C` agrees with `mask (j + a + 2)` there**.  So the danger pattern at the next jump (the run reaches
  the wall) needs the rest of the gap to be exactly `mask L` on all its known words: for each `(j, a)` one gap, about
  `n^2 / 2` of the `2^n` gaps of length `n`, and the first `0` of `mask L` sits at `2^(v_2 L)`.
-/

namespace H696

/-! ## Series -/

/-- Multiply by `1 + z` over GF(2). -/
def mz (w : Nat → Bool) : Nat → Bool
  | 0 => w 0
  | k + 1 => bne (w (k + 1)) (w k)

/-- Multiply by `(1 + z)^t`. -/
def mzi : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, w => w
  | t + 1, w => mzi t (mz w)

/-- `(1 + z)^(-(t+1))`: coefficient `k` is `C(t + k, k) mod 2`, i.e. `k` and `t` share no binary 1. -/
def mask (t : Nat) : Nat → Bool := fun k => disj k t

/-- `1 + z + z^2 + ...`: the all-`y` gap. -/
def ones : Nat → Bool := fun _ => true

/-- Agreement on the first `r` coefficients. -/
def agree (r : Nat) (u v : Nat → Bool) : Prop := ∀ k, k < r → u k = v k

theorem bne_bne_cancel (a b : Bool) : bne (bne a b) b = a := by cases a <;> cases b <;> rfl

theorem bne_inj (a b c : Bool) (h : bne a c = bne b c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-! ## `(1 + z)^t` and its inverse -/

theorem mask_zero : mask 0 = ones := by
  funext k; exact disj_zero_right k

/-- Pascal's rule, as a series identity: `(1 + z) (1 + z)^(-(t+2)) = (1 + z)^(-(t+1))`. -/
theorem mz_mask (t : Nat) : mz (mask (t + 1)) = mask t := by
  funext k
  cases k with
  | zero => show disj 0 (t + 1) = disj 0 t; rw [disj_zero_left, disj_zero_left]
  | succ k =>
    show bne (disj (k + 1) (t + 1)) (disj k (t + 1)) = disj (k + 1) t
    have h := pascal_rule (k + 1) (t + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at h
    rw [h, bne_bne_cancel]

/-- **`(1 + z)^t mask t = 1 + z + z^2 + ...`.** -/
theorem mzi_mask (t : Nat) : mzi t (mask t) = ones := by
  induction t with
  | zero => exact mask_zero
  | succ t ih => show mzi t (mz (mask (t + 1))) = ones; rw [mz_mask, ih]

/-- `1 + z` keeps and reflects agreement on the first `r` coefficients (it is lower triangular with 1s on the diagonal). -/
theorem mz_agree (r : Nat) (u v : Nat → Bool) : agree r (mz u) (mz v) ↔ agree r u v := by
  constructor
  · intro h k
    induction k with
    | zero => intro hk; exact h 0 hk
    | succ k ih =>
      intro hk
      have e := h (k + 1) hk
      have e2 := ih (by omega)
      simp only [mz] at e
      rw [e2] at e
      exact bne_inj _ _ _ e
  · intro h k hk
    cases k with
    | zero => exact h 0 hk
    | succ k => show bne (u (k + 1)) (u k) = bne (v (k + 1)) (v k); rw [h (k + 1) hk, h k (by omega)]

theorem mzi_agree (t r : Nat) : ∀ u v : Nat → Bool, agree r (mzi t u) (mzi t v) ↔ agree r u v := by
  induction t with
  | zero => intro u v; exact Iff.rfl
  | succ t ih => intro u v; show agree r (mzi t (mz u)) (mzi t (mz v)) ↔ _; rw [ih, mz_agree]

/-- **After `t` shielded sweeps the first `r` coefficients are all `y` iff they were `mask t`.** -/
theorem reach_ones (t r : Nat) (w : Nat → Bool) : agree r (mzi t w) ones ↔ agree r w (mask t) := by
  rw [← mzi_mask t]; exact mzi_agree t r w (mask t)

/-! ## Periodicity -/

/-- Below `2^b`, `mask` has period `2^b` in `t`. -/
theorem mask_period (b : Nat) : ∀ t k, k < 2 ^ b → disj k (t + 2 ^ b) = disj k t := by
  induction b with
  | zero => intro t k hk; have : k = 0 := by omega
            subst this; rw [disj_zero_left, disj_zero_left]
  | succ b ih =>
    intro t k hk
    have p : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ]; omega
    rw [disj_eq k (t + 2 ^ (b + 1)), disj_eq k t]
    have e1 : (t + 2 ^ (b + 1)) % 2 = t % 2 := by omega
    have e2 : (t + 2 ^ (b + 1)) / 2 = t / 2 + 2 ^ b := by omega
    have e3 : k / 2 < 2 ^ b := by omega
    rw [e1, e2, ih (t / 2) (k / 2) e3]

theorem mask_mod (b t : Nat) (k : Nat) (hk : k < 2 ^ b) : disj k t = disj k (t % 2 ^ b) := by
  have h : ∀ q s, disj k (s + 2 ^ b * q) = disj k s := by
    intro q
    induction q with
    | zero => intro s; rfl
    | succ q ih =>
      intro s
      have e : s + 2 ^ b * (q + 1) = (s + 2 ^ b * q) + 2 ^ b := by rw [Nat.mul_succ]; omega
      rw [e, mask_period b _ k hk, ih]
  have e := Nat.mod_add_div t (2 ^ b)
  conv => lhs; rw [← e]
  exact h _ _

/-- **Pascal rows.**  A gap whose first `r ≤ 2^b` coefficients are known ever becomes all `y` on them under shielded
sweeps iff it agrees there with one of the `2^b` series `mask t`, `t < 2^b`, and then it does so after `t` sweeps. -/
theorem pascal_reach (b r : Nat) (hr : r ≤ 2 ^ b) (w : Nat → Bool) :
    (∃ t, agree r (mzi t w) ones) ↔ ∃ t, t < 2 ^ b ∧ agree r (mzi t w) ones := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t % 2 ^ b, Nat.mod_lt _ (Nat.two_pow_pos b), ?_⟩
    rw [reach_ones] at ht ⊢
    intro k hk
    rw [ht k hk]
    exact mask_mod b t k (by omega)
  · rintro ⟨t, _, ht⟩; exact ⟨t, ht⟩

/-! ## The jump map -/

/-- Jump to jump: strip the first `L = j + a + 2` coefficients (the defect, `j` `y`s, `a + 1` `x`s) and multiply the rest
`C` by `(1 + z)^L`. -/
def Fj (L : Nat) (w : Nat → Bool) : Nat → Bool := mzi L (fun k => w (L + k))

/-- One jump and the `L - 1` shielded sweeps after it: `(1 + z)^(L-1) ((1 + z) C) = (1 + z)^L C`. -/
theorem Fj_split (L : Nat) (w : Nat → Bool) : Fj (L + 1) w = mzi L (mz (fun k => w (L + 1 + k))) := rfl

/-- **The run at the next jump.**  Its first `r` coefficients are all `y` iff `C` is `mask L` there. -/
theorem Fj_ones (L r : Nat) (w : Nat → Bool) : agree r (Fj L w) ones ↔ agree r (fun k => w (L + k)) (mask L) :=
  reach_ones L r _

/-! ## The link to the words of `Hop.lean` -/

/-- The gap words `G` as a series: the defect, then `G`, then `y`s. -/
def ser (G : List Bool) : Nat → Bool := fun k => (true :: G).getD k true

theorem getD_snoc_true (l : List Bool) : ∀ i, (l ++ [true]).getD i true = l.getD i true := by
  induction l with
  | nil => intro i; cases i <;> rfl
  | cons a l ih => intro i; cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getD_dflt (l : List Bool) (d d' : Bool) : ∀ i, i < l.length → l.getD i d = l.getD i d' := by
  induction l with
  | nil => intro i h; simp at h
  | cons a l ih => intro i h; cases i with
    | zero => rfl
    | succ i => exact ih i (by simp at h; omega)

theorem getD_append_len (l m : List Bool) (d : Bool) : ∀ k, (l ++ m).getD (l.length + k) d = m.getD k d := by
  induction l with
  | nil => intro k; simp
  | cons a l ih => intro k; rw [List.cons_append, List.length_cons, Nat.add_right_comm]; exact ih k

/-- **The shielded sweep on the series.**  `shielded` turns the gap `G` into `x102 (y G y) y`; on the `|G| + 2`
coefficients the old gap determines, that is `(1 + z) W`. -/
theorem ser_shielded (G : List Bool) : agree (G.length + 2) (ser (x102 (true :: G ++ [true]) true)) (mz (ser G)) := by
  intro k hk
  cases k with
  | zero => rfl
  | succ k =>
    show (x102 (true :: G ++ [true]) true).getD k true = bne ((true :: G).getD (k + 1) true) ((true :: G).getD k true)
    have hl : k < (true :: G ++ [true]).length := by simp; omega
    rw [getD_dflt _ true false k (by rw [length_x102]; exact hl), x102_getD _ true k hl]
    have e : true :: G ++ [true] = (true :: G) ++ [true] := rfl
    rw [e, getD_snoc_true, getD_dflt _ false true k (by simpa using hl), getD_snoc_true]
    cases (true :: G).getD (k + 1) true <;> cases (true :: G).getD k true <;> rfl

/-- **The jump on the series.**  `jump` leaves the gap `x102 (C y) y`; on the `|C| + 1` coefficients the old gap
determines, that is `(1 + z) C` (`C` read from its first word, which is `y`). -/
theorem ser_jump (C : List Bool) (hC : hd C true = true) :
    agree (C.length + 1) (ser (x102 (C ++ [true]) true)) (mz (fun k => C.getD k true)) := by
  intro k hk
  cases k with
  | zero => show true = C.getD 0 true; cases C with
    | nil => rfl
    | cons c _ => exact hC.symm
  | succ k =>
    show (x102 (C ++ [true]) true).getD k true = bne (C.getD (k + 1) true) (C.getD k true)
    have hl : k < (C ++ [true]).length := by simp; omega
    rw [getD_dflt _ true false k (by rw [length_x102]; exact hl), x102_getD _ true k hl, getD_snoc_true,
      getD_dflt _ false true k hl, getD_snoc_true]
    cases C.getD (k + 1) true <;> cases C.getD k true <;> rfl

/-- The rest of the gap `y^j x^(a+1) C` after the first `L = j + a + 2` coefficients is `C`. -/
theorem ser_rest (j a : Nat) (C : List Bool) (k : Nat) :
    ser (List.replicate j true ++ List.replicate (a + 1) false ++ C) (j + a + 2 + k) = C.getD k true := by
  show (true :: (List.replicate j true ++ List.replicate (a + 1) false ++ C)).getD (j + a + 2 + k) true = _
  have e : true :: (List.replicate j true ++ List.replicate (a + 1) false ++ C) =
      (true :: (List.replicate j true ++ List.replicate (a + 1) false)) ++ C := by simp
  have hl : (true :: (List.replicate j true ++ List.replicate (a + 1) false)).length = j + a + 2 := by simp; omega
  rw [e, ← hl, getD_append_len]

/-- **Which gaps a jump can turn into the danger pattern.**  At a jump over `y^j x^(a+1)` with rest `C`
(`G = y^j x^(a+1) C`, `L = j + a + 2`), the series at the next jump is `Fj L (ser G)`, and its first `r` coefficients are
all `y` (the run of `y`s at the next jump covers them; with `r` the whole gap, the danger pattern) iff `C`, extended by
`y`s, is `mask L` there: word `k` of `C` is `y` exactly when `k` and `L` share no binary 1. -/
theorem next_jump_run (j a r : Nat) (C : List Bool) :
    agree r (Fj (j + a + 2) (ser (List.replicate j true ++ List.replicate (a + 1) false ++ C))) ones ↔
      agree r (fun k => C.getD k true) (mask (j + a + 2)) := by
  rw [Fj_ones]
  constructor
  · intro h k hk; have := h k hk; simp only [ser_rest] at this; exact this
  · intro h k hk; show ser _ (j + a + 2 + k) = _; rw [ser_rest]; exact h k hk

end H696
