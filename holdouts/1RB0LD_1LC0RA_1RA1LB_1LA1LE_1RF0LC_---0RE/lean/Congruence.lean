import Closed

/-!
# 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE: no congruence rules out a halt

The run is the orbit of `n ↦ F k n = 3n + 3k + 14 - 10·2^k` (`h k < n < h (k+1)`, `pstep_closed`), and it halts
exactly when it lands on some `h k` (`pstep_halt`).  A non-halting proof of the simplest kind would be a set of
residue classes that contains the orbit, is kept by the map, and misses every `h k`.  This file shows there is
none, for every modulus dividing `M = 2^16·3^9` (so every `2^j·3^i` with `j ≤ 16`, `i ≤ 9`), and for the three
starts of the three machines that iterate this map (`n = 4`, `10` and `1`).

What a congruence can see of `n` at level `k` is `cls M k n`: `v = n + k + 6 - 5·2^k` mod `M` (`n = h k` iff
`v = 0`), `k` mod `M` and `2^k` mod `M`.  `CongInv M K P`: the property `P` of these residues excludes `h k` and
is kept by the step at every level `k ≥ K`, whatever the level of the image.

* `cls_step`: the residues of `F k n` are `astep` of those of `n` when the level goes up by `d`;
* `realize`: once `2^k ≥ 3M + k + 10`, every residue of `v` occurs at level `k` both for `d = 0` and `d = 1`,
  so a congruence invariant has to be kept by `astep` with either choice;
* `no_inv`: a list of choices (a certificate, checked by `cert`) that leads from the residues of the start to
  `v = 0` rules out every such invariant (the start is moved up to level `K` by a period of `2^k` mod `M`);
* `no_inv_dvd`, `inv_dvd`: an invariant mod a divisor of `M` is one mod `M`;
* `no_cong_4`, `no_cong_10`, `no_cong_1`: the certificates (paths of 34 choices found by a meet-in-the-middle
  search, `py/congruence.py`), each checked by the kernel.

So a proof that the orbit never hits an `h k` has to use more than residues mod `2^j·3^i`: for instance the size
of `n` within its level, which decides `d`.
-/

namespace H50372

/-! ## Congruence invariants -/

/-- The closed-form macro step at level `k` (`pstep_closed`). -/
def F (k n : Nat) : Nat := 3 * n + 3 * k + 14 - 10 * 2 ^ k

/-- What a congruence modulo `M` can see of `P n` at level `k`: `v = n + k + 6 - 5·2^k` (so `n = h k` iff `v = 0`)
mod `M`, `k` mod `M`, and `2^k` mod `M`. -/
def cls (M k n : Nat) : Nat × Nat × Nat := ((n + k + 6 - 5 * 2 ^ k) % M, k % M, 2 ^ k % M)

/-- `P` (a property of the residues) is a congruence invariant from level `K` on: it excludes the halting value
`h k` and is kept by the macro step, whatever level the next value has. -/
def CongInv (M K : Nat) (P : Nat × Nat × Nat → Prop) : Prop :=
  ∀ k n, K ≤ k → h k ≤ n → n < h (k + 1) → P (cls M k n) →
    n ≠ h k ∧ ∀ d, h (k + d) ≤ F k n → F k n < h (k + d + 1) → P (cls M (k + d) (F k n))

/-- The step on residues, when the level goes up by `d`. -/
def astep (M : Nat) (s : Nat × Nat × Nat) (d : Nat) : Nat × Nat × Nat :=
  ((3 * s.1 + 2 + 5 * s.2.2 + s.2.1 + d + 5 * (M - (2 ^ d * s.2.2) % M)) % M, (s.2.1 + d) % M,
    (2 ^ d * s.2.2) % M)

/-- A certificate: a path of level increments `d ∈ {0, 1}` from `s` to residue `v = 0`. -/
def cert (M : Nat) : Nat × Nat × Nat → List Nat → Bool
  | s, [] => s.1 == 0
  | s, d :: ds => decide (d ≤ 1) && cert M (astep M s d) ds

theorem mod_cancel {a b c M : Nat} (hM : 0 < M) (h : (a + c) % M = (b + c) % M) : a % M = b % M := by
  have key : ∀ x, (x + c + (M - c % M)) % M = x % M := by
    intro x
    have h1 := Nat.mod_add_div c M
    have h2 := Nat.mod_lt c hM
    have : x + c + (M - c % M) = x + (c / M + 1) * M := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
    rw [this, Nat.add_mul_mod_self_right]
  rw [← key a, ← key b, Nat.add_mod, h, ← Nat.add_mod]

theorem lin (M v x x' k d : Nat) (hM : 0 < M) :
    (3 * v + 2 + 5 * x + k + d) % M =
      (3 * (v % M) + 2 + 5 * (x % M) + k % M + d + 5 * (M - x' % M) + 5 * x') % M := by
  have hv := Nat.mod_add_div v M
  have hx := Nat.mod_add_div x M
  have hk := Nat.mod_add_div k M
  have hx' := Nat.mod_add_div x' M
  have hlt := Nat.mod_lt x' hM
  generalize v / M = a at hv
  generalize x / M = b at hx
  generalize k / M = c at hk
  generalize x' / M = e at hx'
  have e1 : 3 * v + 2 + 5 * x + k + d
      = (3 * (v % M) + 2 + 5 * (x % M) + k % M + d) + M * (3 * a + 5 * b + c) := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm M 3, Nat.mul_left_comm M 5]; omega
  have e2 : 3 * (v % M) + 2 + 5 * (x % M) + k % M + d + 5 * (M - x' % M) + 5 * x'
      = (3 * (v % M) + 2 + 5 * (x % M) + k % M + d) + M * (5 + 5 * e) := by
    rw [Nat.mul_add, Nat.mul_left_comm M 5]; omega
  rw [e1, e2, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]

/-- The residues of the next value are `astep` of the residues. -/
theorem cls_step (M k n d : Nat) (hM : 0 < M) (hk : 1 ≤ k) (hn : h k ≤ n) (hd : h (k + d) ≤ F k n) :
    cls M (k + d) (F k n) = astep M (cls M k n) d := by
  obtain ⟨p1, p2⟩ := pow_facts k
  have hx : 2 ^ (k + d) = 2 ^ d * 2 ^ k := by rw [Nat.pow_add, Nat.mul_comm]
  have hdk : k + d < 2 ^ (k + d) := Nat.lt_two_pow_self
  have hm : 2 ^ d * (2 ^ k % M) % M = 2 ^ (k + d) % M := by
    rw [hx, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  unfold cls astep
  simp only [hm]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    unfold h F at *
    have e : (3 * n + 3 * k + 14 - 10 * 2 ^ k + (k + d) + 6 - 5 * 2 ^ (k + d)) + 5 * 2 ^ (k + d)
        = 3 * (n + k + 6 - 5 * 2 ^ k) + 2 + 5 * 2 ^ k + k + d := by omega
    apply mod_cancel hM (c := 5 * 2 ^ (k + d))
    rw [e]
    exact lin M _ _ _ k d hM
  · simp only [Nat.add_mod k d M, Nat.mod_mod, Nat.add_mod (k % M) d M]
  · rfl

theorem res_hit (B c M : Nat) (hM : 0 < M) (hc : c < M) : (B + (c + M - B % M) % M) % M = c := by
  have hb := Nat.mod_lt B hM
  rw [Nat.add_mod_mod, Nat.add_mod, Nat.add_mod_mod, show B % M + (c + M - B % M) = c + M by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hc]

theorem two_mul_le_pow : ∀ k, 2 ≤ k → 2 * k ≤ 2 ^ k
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by decide
  | k + 3, _ => by
    have ih := two_mul_le_pow (k + 2) (by omega)
    rw [Nat.pow_succ]; omega

/-- Every residue of `v`, with the level staying (`d = 0`) or going up by one (`d = 1`), is taken by some `n`
of level `k`, once `2^k` is large compared with `M`. -/
theorem realize (M k c d : Nat) (hM : 0 < M) (hk : 1 ≤ k) (hc : c < M) (hd : d ≤ 1)
    (hbig : 3 * M + k + 10 ≤ 2 ^ k) :
    ∃ n, h k < n ∧ n < h (k + 1) ∧ (n + k + 6 - 5 * 2 ^ k) % M = c ∧
      h (k + d) ≤ F k n ∧ F k n < h (k + d + 1) := by
  obtain ⟨p1, p2⟩ := pow_facts k
  have p3 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by rw [Nat.pow_succ, p2]; omega
  rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
  · have ht := Nat.mod_lt (c + M - 1 % M) hM
    have hr := res_hit 1 c M hM hc
    generalize (c + M - 1 % M) % M = t at ht hr
    refine ⟨h k + (1 + t), ?_, ?_, ?_, ?_, ?_⟩ <;> unfold h <;> try unfold F
    all_goals try simp only [p2, Nat.add_zero]
    all_goals try omega
    rw [show 5 * 2 ^ k - k - 6 + (1 + t) + k + 6 - 5 * 2 ^ k = 1 + t by omega]; exact hr
  · have ht := Nat.mod_lt (c + M - (2 * 2 ^ k + 1) % M) hM
    have hr := res_hit (2 * 2 ^ k + 1) c M hM hc
    generalize (c + M - (2 * 2 ^ k + 1) % M) % M = t at ht hr
    refine ⟨h k + (2 * 2 ^ k + 1 + t), ?_, ?_, ?_, ?_, ?_⟩ <;> unfold h <;> try unfold F
    all_goals try simp only [p2, p3]
    all_goals try omega
    rw [show 5 * 2 ^ k - k - 6 + (2 * 2 ^ k + 1 + t) + k + 6 - 5 * 2 ^ k = 2 * 2 ^ k + 1 + t by omega]; exact hr

theorem pow_period (M j L : Nat) (hper : 2 ^ (j + L) % M = 2 ^ j % M) :
    ∀ t k, j ≤ k → 2 ^ (k + t * L) % M = 2 ^ k % M := by
  intro t
  induction t with
  | zero => intro k _; simp
  | succ t ih =>
    intro k hk
    have e : k + (t + 1) * L = (k + t * L - j) + (j + L) := by rw [Nat.add_mul, Nat.one_mul]; omega
    rw [e, Nat.pow_add, Nat.mul_mod, hper, ← Nat.mul_mod, ← Nat.pow_add,
      show k + t * L - j + j = k + t * L by omega, ih k hk]

/-- **No congruence invariant.**  If the residue path `path` leads from the residues of `n0` (at level `k0`) to
residue `v = 0`, then no property of the residues mod `M` that holds at `n0` is kept by the macro step from any
level `K` on while avoiding the halting values `h k`.  (`L` is a period of `2^k` mod `M` from `j` on, and a
multiple of `M`.) -/
theorem no_inv (M j L k0 n0 : Nat) (path : List Nat) (hM : 0 < M) (hL : 0 < L) (hLM : L % M = 0)
    (hper : 2 ^ (j + L) % M = 2 ^ j % M) (hj : j ≤ k0) (hk0 : 1 ≤ k0)
    (hc : cert M (cls M k0 n0) path = true) :
    ∀ K P, CongInv M K P → ¬ P (cls M k0 n0) := by
  intro K P hI hP
  have aux : ∀ path s k, K ≤ k → 3 * M + 12 ≤ k → s.1 < M → s.2.1 = k % M → s.2.2 = 2 ^ k % M → P s →
      cert M s path = true → False := by
    intro path
    induction path with
    | nil =>
      intro s k hK hk h1 h2 h3 hPs hcs
      simp only [cert, beq_iff_eq] at hcs
      have hb := two_mul_le_pow k (by omega)
      obtain ⟨p1, p2⟩ := pow_facts k
      have hs : cls M k (h k) = s := by
        unfold cls h
        rw [show 5 * 2 ^ k - k - 6 + k + 6 - 5 * 2 ^ k = 0 by omega, Nat.zero_mod, ← hcs, ← h2, ← h3]
      have hlt : h k < h (k + 1) := by unfold h; rw [p2]; omega
      exact (hI k (h k) hK (Nat.le_refl _) hlt (hs ▸ hPs)).1 rfl
    | cons d ds ih =>
      intro s k hK hk h1 h2 h3 hPs hcs
      simp only [cert, Bool.and_eq_true, decide_eq_true_eq] at hcs
      have hb := two_mul_le_pow k (by omega)
      obtain ⟨n, n1, n2, n3, n4, n5⟩ := realize M k s.1 d hM (by omega) h1 hcs.1 (by omega)
      have hs : cls M k n = s := by
        unfold cls; rw [n3, ← h2, ← h3]
      have hn := (hI k n hK (Nat.le_of_lt n1) n2 (hs ▸ hPs)).2 d n4 n5
      have hst := cls_step M k n d hM (by omega) (Nat.le_of_lt n1) n4
      rw [hs] at hst
      apply ih (astep M s d) (k + d) (by omega) (by omega)
        (by rw [← hst]; exact Nat.mod_lt _ hM) (by rw [← hst]; rfl) (by rw [← hst]; rfl)
        (hst ▸ hn) hcs.2
  -- move the start up to a level ≥ K with the same residues
  have hK1 : K + 3 * M + 12 ≤ k0 + (K + 3 * M + 12) * L := by
    have := Nat.le_mul_of_pos_right (K + 3 * M + 12) hL; omega
  apply aux path (cls M k0 n0) (k0 + (K + 3 * M + 12) * L) (by omega) (by omega)
    (Nat.mod_lt _ hM) ?_ ?_ hP hc
  · show k0 % M = _
    rw [Nat.add_mod, Nat.mul_mod, hLM, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  · show 2 ^ k0 % M = _
    rw [pow_period M j L hper _ k0 hj]

/-! ## Divisors, a checked modular power, and the starts -/

/-- Reduce residues mod `M` to residues mod a divisor `M'`. -/
def red (M' : Nat) (s : Nat × Nat × Nat) : Nat × Nat × Nat := (s.1 % M', s.2.1 % M', s.2.2 % M')

theorem cls_dvd {M' M : Nat} (hd : M' ∣ M) (k n : Nat) : cls M' k n = red M' (cls M k n) := by
  simp only [cls, red, Nat.mod_mod_of_dvd _ hd]

/-- A congruence invariant mod a divisor `M'` of `M` is one mod `M`. -/
theorem inv_dvd {M' M K : Nat} {P : Nat × Nat × Nat → Prop} (hd : M' ∣ M) (hI : CongInv M' K P) :
    CongInv M K (fun s => P (red M' s)) := by
  intro k n hK h1 h2 hP
  rw [← cls_dvd hd] at hP
  obtain ⟨a, b⟩ := hI k n hK h1 h2 hP
  exact ⟨a, fun d e1 e2 => by show P (red M' _); rw [← cls_dvd hd]; exact b d e1 e2⟩

theorem no_inv_dvd (M j L k0 n0 : Nat) (path : List Nat) (hM : 0 < M) (hL : 0 < L) (hLM : L % M = 0)
    (hper : 2 ^ (j + L) % M = 2 ^ j % M) (hj : j ≤ k0) (hk0 : 1 ≤ k0)
    (hc : cert M (cls M k0 n0) path = true) :
    ∀ M', M' ∣ M → ∀ K P, CongInv M' K P → ¬ P (cls M' k0 n0) := by
  intro M' hd K P hI hP
  apply no_inv M j L k0 n0 path hM hL hLM hper hj hk0 hc K _ (inv_dvd hd hI)
  rw [← cls_dvd hd]; exact hP

/-- `b^e mod M` by repeated squaring, with fuel `f` (enough when `e < 2^f`). -/
def powModF : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, M => 1 % M
  | f + 1, b, e, M =>
    if e = 0 then 1 % M else
      if e % 2 = 0 then powModF f b (e / 2) M * powModF f b (e / 2) M % M
      else powModF f b (e / 2) M * powModF f b (e / 2) M % M * b % M

theorem powModF_eq : ∀ f b e M, e < 2 ^ f → powModF f b e M = b ^ e % M := by
  intro f
  induction f with
  | zero => intro b e M he; simp at he; subst he; simp [powModF]
  | succ f ih =>
    intro b e M he
    have h2 : e / 2 < 2 ^ f := by rw [Nat.pow_succ] at he; omega
    have hsq : powModF f b (e / 2) M * powModF f b (e / 2) M % M = b ^ (2 * (e / 2)) % M := by
      rw [ih b (e / 2) M h2, ← Nat.mul_mod, Nat.two_mul, Nat.pow_add]
    unfold powModF
    by_cases e0 : e = 0
    · subst e0; simp
    · rw [if_neg e0]
      by_cases ev : e % 2 = 0
      · rw [if_pos ev, hsq, show 2 * (e / 2) = e by omega]
      · rw [if_neg ev, hsq, Nat.mod_mul_mod, ← Nat.pow_succ, show (2 * (e / 2)).succ = e by omega]

/-- The level of `n`: the `k` with `h k ≤ n < h (k+1)`. -/
def levF : Nat → Nat → Nat → Nat
  | 0, _, k => k
  | f + 1, n, k => if h (k + 1) ≤ n then levF f n (k + 1) else k

/-- The map on `P n`: `none` at a halt. -/
def fmap (n : Nat) : Option Nat :=
  let k := levF 64 n 0
  if n = h k then none else some (F k n)

def fiter : Nat → Nat → Option Nat
  | 0, n => some n
  | t + 1, n => match fmap n with | some m => fiter t m | none => none

/-- `no_inv_dvd` with the period checked by `powModF` (for `j + L < 2^64`). -/
theorem no_inv_cert (M j L k0 n0 : Nat) (path : List Nat) (hM : 0 < M) (hL : 0 < L) (hLM : L % M = 0)
    (hjL : j + L < 2 ^ 64) (hper : powModF 64 2 (j + L) M = powModF 64 2 j M) (hj : j ≤ k0) (hk0 : 1 ≤ k0)
    (hc : cert M (cls M k0 n0) path = true) :
    ∀ M', M' ∣ M → ∀ K P, CongInv M' K P → ¬ P (cls M' k0 n0) := by
  rw [powModF_eq 64 2 _ M hjL, powModF_eq 64 2 _ M (by omega)] at hper
  exact no_inv_dvd M j L k0 n0 path hM hL hLM hper hj hk0 hc
/-! ## The certificates (generated by `py/congruence.py lean 16 9 17 17`) -/

/-- Start 4: the value after 40 steps of the map is 432545740, at level 26. -/
theorem start_4 : fiter 40 4 = some 432545740 := by decide +kernel

theorem level_4 : h 26 ≤ 432545740 ∧ 432545740 < h 27 := by decide +kernel

/-- **No congruence invariant mod any divisor of 2^16·3^9 = 1289945088** for start 4. -/
theorem no_cong_4 : ∀ M', M' ∣ 1289945088 → ∀ K P, CongInv M' K P → ¬ P (cls M' 26 432545740) :=
  no_inv_cert 1289945088 16 1289945088 26 432545740
    [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1]
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
    (by decide +kernel)

/-- Start 10: the value after 40 steps of the map is 131603755, at level 24. -/
theorem start_10 : fiter 40 10 = some 131603755 := by decide +kernel

theorem level_10 : h 24 ≤ 131603755 ∧ 131603755 < h 25 := by decide +kernel

/-- **No congruence invariant mod any divisor of 2^16·3^9 = 1289945088** for start 10. -/
theorem no_cong_10 : ∀ M', M' ∣ 1289945088 → ∀ K P, CongInv M' K P → ¬ P (cls M' 24 131603755) :=
  no_inv_cert 1289945088 16 1289945088 24 131603755
    [0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1]
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
    (by decide +kernel)

/-- Start 1: the value after 40 steps of the map is 6382008234, at level 30. -/
theorem start_1 : fiter 40 1 = some 6382008234 := by decide +kernel

theorem level_1 : h 30 ≤ 6382008234 ∧ 6382008234 < h 31 := by decide +kernel

/-- **No congruence invariant mod any divisor of 2^16·3^9 = 1289945088** for start 1. -/
theorem no_cong_1 : ∀ M', M' ∣ 1289945088 → ∀ K P, CongInv M' K P → ¬ P (cls M' 30 6382008234) :=
  no_inv_cert 1289945088 16 1289945088 30 6382008234
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1]
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
    (by decide +kernel)

/-- For this machine the start is a value of its own run: the macro-step orbit of `P 4` (`Orbit.lean`) is at
`P 432545740` after 40 macro steps. -/
theorem orbit_40 : (orbit 40 4).map Prod.fst = some 432545740 := by decide +kernel

end H50372
