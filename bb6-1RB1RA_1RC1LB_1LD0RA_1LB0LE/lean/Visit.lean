import Thin

/-!
# The blank orbit cannot step around a failing excursion

The return map is a counter: from `[a, 2a+1]` the orbit goes to `[a + 12k, 2(a + 12k) + 1]`, `k ≥ 1`, and the values
`a + 12j`, `0 < j < k`, inside a jump are skipped.  The orbit starts at `a = 5`, so it only meets `a = 5 mod 12`.  A
structure that holds along the orbit and not elsewhere would have to be in which values it skips.  This file shows
that the skipped values are never the ones that matter:

* `skip_off_open34` (for every `a`, no upper bound, kernel): unless `a mod 2^34` is one of the 67 open residues of
  `Thin.lean`, the excursion from `[a, 2a+1]` returns and the jump skips no value `= 1 mod 32` (`SkipRet`).
* `open34_mod256`: every open residue is `1 mod 256`.  So a failing excursion has `a = 1 mod 256`, and the jumps
  before it never skip such a value.
* `visit`: if every `a = 5 mod 12` below `b` makes such a jump, the orbit reaches `[b, 2b+1]` for every `b = 5 mod 12`,
  `b = 1 mod 32`.
* `orbit_meets_first_failure`: if some `a = 5 mod 12` fails `SkipRet` (its excursion halts, meets a stop block of 1,
  never comes back, or jumps over a value `= 1 mod 32`), the least such `a` is one of the open residues and the blank
  orbit reaches `[a, 2a+1]`.

So along the return map the only thing the blank orbit knows that a general start does not is `a mod 3`, and the
question for the orbit is the question for every `a = 5 mod 12`: does each excursion return?
-/

namespace BB6d

/-- `a` returns, and the jump `a → a + 12k` passes over no value `= 1 mod 32`. -/
def SkipRet (a : Nat) : Prop :=
  ∃ k, 1 ≤ k ∧ iterN (9 * k) (.ok [2 * a + 1, a]) = .ok [2 * (a + 12 * k) + 1, a + 12 * k] ∧
    ∀ j, 0 < j → j < k → (a + 12 * j) % 32 ≠ 1

theorem SkipRet.returns {a : Nat} (h : SkipRet a) : Returns a :=
  let ⟨k, h1, h2, _⟩ := h; ⟨k, h1, h2⟩

/-- No value `p + q*u + 12j`, `0 < j < k`, is `1 mod 32` (for every `u` when `32 ∣ q`). -/
def noSkip (p q k : Nat) : Bool :=
  k == 1 || (q % 32 == 0 && (List.range k).all fun j => j == 0 || (p + 12 * j) % 32 != 1)

theorem noSkip_ok {p q k : Nat} (h : noSkip p q k = true) (u : Nat) :
    ∀ j, 0 < j → j < k → (p + q * u + 12 * j) % 32 ≠ 1 := by
  intro j hj hk
  simp only [noSkip, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  rcases h with h | ⟨hq, h⟩
  · omega
  · have := h j hk
    simp only [bne_iff_ne, ne_eq] at this
    obtain ⟨c, rfl⟩ : ∃ c, q = 32 * c := ⟨q / 32, by omega⟩
    rw [Nat.mul_assoc]
    generalize c * u = w
    omega

/-- `sgood` with the jump checked as well. -/
def sgoodS (p q : Nat) : SR :=
  match srun 200 [⟨2 * p + 1, 2 * q⟩, ⟨p, q⟩] with
  | (.ok [b, a'], n) =>
    if n % 9 == 0 && 9 ≤ n && a'.q == q && a'.p == p + 12 * (n / 9) && b.q == 2 * q && b.p == 2 * a'.p + 1
      && noSkip p q (n / 9)
    then .ok [] else .bad
  | (.ok _, _) => .bad
  | (r, _) => r

theorem sgoodS_ok (p q : Nat) (h : sgoodS p q = .ok []) (u : Nat) : SkipRet (p + q * u) := by
  unfold sgoodS at h
  split at h
  · rename_i b a' n hs
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨h9, hn⟩, hq⟩, hp⟩, hbq⟩, hbp⟩, hns⟩ := hc
      have hr := srun_ok u _ _ _ _ hs
      refine ⟨n / 9, by omega, ?_, noSkip_ok hns u⟩
      rw [show 9 * (n / 9) = n by omega]
      simp only [List.map, Aff.ev] at hr
      have e1 : 2 * p + 1 + 2 * q * u = 2 * (p + q * u) + 1 := by rw [Nat.mul_assoc]; omega
      have e2 : b.p + b.q * u = 2 * (p + q * u + 12 * (n / 9)) + 1 := by
        rw [hbq, hbp, hp, Nat.mul_assoc]; omega
      have e3 : a'.p + a'.q * u = p + q * u + 12 * (n / 9) := by rw [hq, hp]; omega
      rw [e1, e2, e3] at hr; exact hr
    · cases h
  · cases h
  · rename_i r n _ _; cases r <;> simp_all

/-- `cgood` with the jump checked as well. -/
def cgoodS (a : Nat) : Bool :=
  match crun 1000 [2 * a + 1, a] with
  | some ([b, a'], n) => n % 9 == 0 && 9 ≤ n && a' == a + 12 * (n / 9) && b == 2 * a' + 1 && noSkip a 0 (n / 9)
  | _ => false

theorem cgoodS_ok (a : Nat) (h : cgoodS a = true) : SkipRet a := by
  unfold cgoodS at h
  split at h
  · rename_i b a' n hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h9, hn⟩, ha⟩, hb⟩, hns⟩ := h
    have := crun_ok _ _ _ _ hc
    refine ⟨n / 9, by omega, ?_, fun j hj hk => by simpa using noSkip_ok hns 0 j hj hk⟩
    rw [show 9 * (n / 9) = n by omega, this, hb, ha]
  · cases h

/-- `thin` with `sgoodS` and `cgoodS`. -/
def thinS (M : Nat) : Nat → Nat → Nat → Nat → Option (List Nat)
  | 0, _, _, _ => none
  | f + 1, d, p, q =>
    match sgoodS p q with
    | .ok _ => some []
    | .split => match d with
      | 0 => if q % M = 0 then some [p % M] else none
      | d + 1 => match thinS M f d p (2 * q), thinS M f d (p + q) (2 * q) with
        | some l, some r => some (l ++ r)
        | _, _ => none
    | .small => if cgoodS p then thinS M f d (p + q) q else none
    | .bad => none

theorem thinS_ok (M : Nat) (f : Nat) : ∀ (d p q : Nat) (L : List Nat), thinS M f d p q = some L →
    ∀ u, ¬ SkipRet (p + q * u) → (p + q * u) % M ∈ L := by
  induction f with
  | zero => intro d p q L h; simp [thinS] at h
  | succ f ih =>
    intro d p q L h u hu
    simp only [thinS] at h
    split at h
    · rename_i l hs
      cases l with
      | nil => exact absurd (sgoodS_ok p q hs u) hu
      | cons _ _ =>
        unfold sgoodS at hs
        split at hs <;> (try split at hs) <;> simp_all
    · split at h
      · split at h
        · rename_i hq
          cases h
          simp only [List.mem_singleton]
          obtain ⟨c, hc⟩ : ∃ c, q = M * c := ⟨q / M, by have := Nat.div_add_mod q M; omega⟩
          rw [hc, Nat.mul_assoc, Nat.add_mul_mod_self_left]
        · cases h
      · rename_i d
        split at h
        · rename_i l r h0 h1
          cases h
          obtain ⟨v, rfl | rfl⟩ : ∃ v, u = 2 * v ∨ u = 2 * v + 1 := ⟨u / 2, by omega⟩
          · have e : 2 * q * v = q * (2 * v) := by rw [Nat.mul_comm 2 q, Nat.mul_assoc]
            have := ih d p (2 * q) l h0 v (by rw [e]; exact hu)
            rw [e] at this; exact List.mem_append_left _ this
          · have e : p + q + 2 * q * v = p + q * (2 * v + 1) := by
              rw [Nat.mul_add, Nat.mul_one, show 2 * q * v = q * (2 * v) by rw [Nat.mul_comm 2 q, Nat.mul_assoc]]
              omega
            have := ih d (p + q) (2 * q) r h1 v (by rw [e]; exact hu)
            rw [e] at this; exact List.mem_append_right _ this
        · cases h
    · split at h
      · rename_i hc
        cases u with
        | zero => exact absurd (by simpa using cgoodS_ok p hc) hu
        | succ v =>
          have e : p + q + q * v = p + q * (v + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
          have := ih d (p + q) q L h v (by rw [e]; exact hu)
          rwa [e] at this
      · cases h
    · cases h

/-- **For every `a`, unbounded**: unless `a mod 2^34` is one of the 67 open residues, the excursion from `[a, 2a+1]`
returns and its jump skips no value `= 1 mod 32`.  Kernel only. -/
theorem skip_off_open34 : ∀ a, a % 4 = 1 → 5 ≤ a → a % 2 ^ 34 ∉ open34 → SkipRet a := by
  have h : thinS (2 ^ 34) 200 32 5 4 = some open34 := by decide +kernel
  intro a h1 h5 ho
  refine Classical.byContradiction fun hr => ho ?_
  have := thinS_ok _ _ _ _ _ _ h ((a - 5) / 4)
  rw [show 5 + 4 * ((a - 5) / 4) = a by omega] at this
  exact this hr

/-- Every open residue is `1 mod 256`. -/
theorem open34_mod256 : ∀ r ∈ open34, r % 256 = 1 := by decide

/-- The counter cannot jump over `b = 5 mod 12`, `b = 1 mod 32`, while every value before it makes a jump that skips
no value `= 1 mod 32`: the blank orbit reaches `[b, 2b+1]` (nearest first `[2b+1, b]`). -/
theorem visit (b : Nat) (hb : b % 12 = 5) (h32 : b % 32 = 1)
    (H : ∀ a, a % 12 = 5 → a < b → SkipRet a) : ∃ n, orbit n = .ok [2 * b + 1, b] := by
  have P : ∀ m a, b - a ≤ m → a ≤ b → a % 12 = 5 → (∃ n, orbit n = .ok [2 * a + 1, a]) →
      ∃ n, orbit n = .ok [2 * b + 1, b] := by
    intro m
    induction m with
    | zero =>
      intro a hm hab _ ⟨n, hn⟩
      rw [show a = b by omega] at hn; exact ⟨n, hn⟩
    | succ m ih =>
      intro a hm hab ha ⟨n, hn⟩
      by_cases he : a = b
      · subst he; exact ⟨n, hn⟩
      obtain ⟨k, hk, hr, hs⟩ := H a ha (by omega)
      by_cases hle : a + 12 * k ≤ b
      · exact ih (a + 12 * k) (by omega) hle (by omega) ⟨n + 9 * k, by rw [orbit_add, hn]; exact hr⟩
      · exact absurd h32 (by
          have := hs ((b - a) / 12) (by omega) (by omega)
          rwa [show a + 12 * ((b - a) / 12) = b by omega] at this)
  exact P (b - 5) 5 (Nat.le_refl _) (by omega) rfl ⟨4, orbit_4⟩

/-- **The orbit meets the first failure.**  If some `a = 5 mod 12` fails `SkipRet`, the least one has its residue
among the 67 open ones and the blank orbit reaches `[a, 2a+1]`. -/
theorem orbit_meets_first_failure (b : Nat) (hb : b % 12 = 5) (hfail : ¬ SkipRet b)
    (H : ∀ a, a % 12 = 5 → a < b → SkipRet a) :
    b % 2 ^ 34 ∈ open34 ∧ ∃ n, orbit n = .ok [2 * b + 1, b] := by
  have ho : b % 2 ^ 34 ∈ open34 :=
    Classical.byContradiction fun h => hfail (skip_off_open34 b (by omega) (by omega) h)
  have h256 := open34_mod256 _ ho
  have h32 : b % 32 = 1 := by
    have : b % 2 ^ 34 % 32 = b % 32 := Nat.mod_mod_of_dvd b (by decide)
    omega
  exact ⟨ho, visit b hb h32 H⟩

/-- Conversely, if every `a = 5 mod 12` makes such a jump, no pass of the blank orbit stops at a block of 1. -/
theorem no_one_of_all (H : ∀ a, a % 12 = 5 → SkipRet a) (n : Nat) : ∃ zs, orbit n = .ok zs := by
  have Q : ∀ j, ∃ m, j ≤ m ∧ ∃ a, a % 12 = 5 ∧ orbit m = .ok [2 * a + 1, a] := by
    intro j
    induction j with
    | zero => exact ⟨4, by omega, 5, rfl, orbit_4⟩
    | succ j ih =>
      obtain ⟨m, hm, a, ha, hr⟩ := ih
      by_cases hlt : j + 1 ≤ m
      · exact ⟨m, hlt, a, ha, hr⟩
      obtain ⟨k, hk, he, _⟩ := H a ha
      exact ⟨m + 9 * k, by omega, a + 12 * k, by omega, by rw [orbit_add, hr]; exact he⟩
  obtain ⟨m, hm, a, _, hr⟩ := Q n
  exact orbit_ok_of_le hm hr

end BB6d
