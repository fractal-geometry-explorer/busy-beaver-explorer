import Bits

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: the rebuild map, checked

A *rebuild state* `rcfg k m r` is the moment a single block arrives: a single block of `3 (k + 1)` cells and a
regular counter in round `m` with `r` sub-rounds left (`cz`, `Bits.lean`).  From there the next sub-round is the
rebuild (`rebuild`, `rebuild_one`), then comes the *transient*, where the small gaps move cells of the counter into
the list, and then the collapse to the next single block.

`rstep` computes the next rebuild state from a hint (where to cut the counter, how many digits of the list to keep,
and the stretches of the transient: `adv M` for `M` sub-rounds of `W` with the counter, `pass N` for `N` sub-rounds of
the pass machine).  It only ever looks at the lowest bits of `r` and the first digits of the list:

* the counter is cut at a 0 bit `p` (`cz_split`): the gaps of the bits below `p` are the prefix `Z`, the gaps of the
  bits above are a tail `R` that the transient never reads;
* the list `3 2^k` after the rebuild is `0^c ++ 0^(k - c)`, and only `0^c` is given to the transient;
* each stretch is computed on the prefixes (`gfastF`, `subsF`, `Frame.lean`), which is a theorem for every tail;
* at the end the low gaps must be the counter of some bits `L'` (`czb L'`), so the counter is again a number
  (`cz_join`), and the collapse is arithmetic (`giter_cz`, `T_append`).

`rstep_sound`: whatever `rstep` computes is a run of the machine.  So `rrun` (rebuild after rebuild) needs from the
kernel only the transients on short prefixes and arithmetic on the numbers; the size of the single block and of the
counter do not matter.
-/

namespace H4320

open TM

/-! ## The transient on prefixes -/

/-- A stretch of the transient: `M` sub-rounds of `W` with the counter, or `N` sub-rounds of the pass machine. -/
inductive Seg where
  | adv (M : Nat)
  | pass (N : Nat)
  deriving Repr

/-- Trailing zeros of `n` (at most `f`). -/
def tzc : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n % 2 = 1 then 0 else tzc f (n / 2) + 1

/-- The digits with time left `n` (the binary expansion of `n`, `f` digits at most). -/
def tinv : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else tzc n n :: tinv f (n / 2 ^ (tzc n n + 1))

def fd (d : Nat) : Nat := 3 * d + 2

/-- One stretch on the prefixes.  With `top` there is nothing further out on the right of the zone, so the counter
is evaluated exactly (`gfast`) and the pass machine may read the zone to its end. -/
def segStep (fuel : Nat) (top : Bool) : Seg → List Nat × (Nat × List Nat) → Option (List Nat × (Nat × List Nat))
  | .adv M, (F, x) =>
    match (if top then gfast fuel M x else gfastF fuel M x) with
    | some y =>
      let F' := tinv (F.length + sig F) (T F - M)
      if M ≤ T F ∧ T F' + M = T F ∧ sig F' = sig F then some (F', y) else none
    | none => none
  | .pass N, (F, (l, Z)) =>
    match subsF top fuel N (F.map fd) l Z with
    | some (.moment bs l' Z' _) =>
      let F' := bs.map (fun b => (b - 2) / 3)
      if bs = F'.map fd then some (F', (l', Z')) else none
    | _ => none

def runSegs (fuel : Nat) (top : Bool) : List Seg → List Nat × (Nat × List Nat) → Option (List Nat × (Nat × List Nat))
  | [], s => some s
  | g :: gs, s =>
    match segStep fuel top g s with
    | some s' => runSegs fuel top gs s'
    | none => none

theorem segStep_sound (fuel : Nat) (top : Bool) (g : Seg) (F F' : List Nat) (x y : Nat × List Nat)
    (h : segStep fuel top g (F, x) = some (F', y)) (q : Nat) (X R : List Nat) (ht : top = true → R = []) :
    ∃ n, steps n (enc q (F ++ X) x.1 (x.2 ++ R)) = some (enc q (F' ++ X) y.1 (y.2 ++ R)) := by
  cases g with
  | adv M =>
    cases top with
    | false =>
      simp only [segStep, Bool.false_eq_true, ite_false] at h
      cases e : gfastF fuel M x with
      | none => rw [e] at h; simp at h
      | some y' =>
        rw [e] at h
        simp only at h
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact advance_frame fuel M q F _ X x y' R (by omega) hc.2.2 e
        · simp at h
    | true =>
      obtain rfl := ht rfl
      simp only [segStep, ite_true] at h
      cases e : gfast fuel M x with
      | none => rw [e] at h; simp at h
      | some y' =>
        rw [e] at h
        simp only at h
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [List.append_nil]
          exact advance_to M q q (F ++ X) (_ ++ X) x y' (by rw [T_append, T_append, hc.2.2]; omega)
            (by rw [mass_append, mass_append, hc.2.2]) (gfast_sound fuel M x y' e)
        · simp at h
  | pass N =>
    obtain ⟨l, Z⟩ := x
    simp only [segStep] at h
    cases e : subsF top fuel N (F.map fd) l Z with
    | none => rw [e] at h; simp at h
    | some o =>
      rw [e] at h
      cases o with
      | moment bs l' Z' n =>
        simp only at h
        split at h
        · rename_i hb
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨n, pass_frame top fuel N q F _ X l l' Z Z' R n ht ?_⟩
          show subsF top fuel N (F.map fd) l Z = some (.moment (List.map fd _) l' Z' n)
          rw [e, ← hb]
        · simp at h
      | halt => simp at h
      | stuck => simp at h

theorem runSegs_sound (fuel : Nat) (top : Bool) : ∀ (gs : List Seg) (F F' : List Nat) (x y : Nat × List Nat),
    runSegs fuel top gs (F, x) = some (F', y) → ∀ (q : Nat) (X R : List Nat), (top = true → R = []) →
    ∃ n, steps n (enc q (F ++ X) x.1 (x.2 ++ R)) = some (enc q (F' ++ X) y.1 (y.2 ++ R))
  | [], F, F', x, y, h, q, X, R, _ => by
    simp only [runSegs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, rfl⟩
  | g :: gs, F, F', x, y, h, q, X, R, ht => by
    simp only [runSegs] at h
    cases e : segStep fuel top g (F, x) with
    | none => rw [e] at h; simp at h
    | some s =>
      rw [e] at h
      obtain ⟨F₁, x₁⟩ := s
      obtain ⟨n₁, h₁⟩ := segStep_sound fuel top g F F₁ x x₁ e q X R ht
      obtain ⟨n₂, h₂⟩ := runSegs_sound fuel top gs F₁ F' x₁ y h q X R ht
      exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

/-! ## The rebuild sub-round on a prefix -/

def startT : Nat × List Nat → Option (Nat × List Nat)
  | (b + 5, Z) => some (5, b :: Z)
  | (1, (u + 2) :: Z) => some (4, u :: Z)
  | _ => none

theorem startT_sound (x y : Nat × List Nat) (h : startT x = some y) (k : Nat) (R : List Nat) :
    ∃ n, steps n (enc (k + 1) [] x.1 (x.2 ++ R)) = some (enc 1 (List.replicate k 0) y.1 (y.2 ++ R)) := by
  obtain ⟨l, Z⟩ := x
  match l, Z, h with
  | b + 5, Z, h =>
    simp only [startT, Option.some.injEq] at h; subst h
    exact rebuild k b (Z ++ R)
  | 1, (u + 2) :: Z, h =>
    simp only [startT, Option.some.injEq] at h; subst h
    exact rebuild_one k u (Z ++ R)
  | 0, _, h => simp [startT] at h
  | 1, [], h => simp [startT] at h
  | 1, 0 :: _, h => simp [startT] at h
  | 1, 1 :: _, h => simp [startT] at h
  | 2, _, h => simp [startT] at h
  | 3, _, h => simp [startT] at h
  | 4, _, h => simp [startT] at h

/-! ## Back to a number -/

/-- The bits of a low counter (`czb` backwards; `rstep` checks the result). -/
def unz : List Nat → List Bool
  | [] => []
  | [g] => List.replicate ((g + 1) / 4 - 1) true
  | g :: gs => List.replicate ((g + 1) / 4 - 1) true ++ false :: unz gs

def decode (x : Nat × List Nat) : List Bool := List.replicate ((x.1 - 1) / 4) false ++ true :: unz x.2

theorem valB_pos : ∀ L : List Bool, allF L = false → 1 ≤ valB L
  | [], h => by simp [allF] at h
  | true :: _, _ => by simp [valB]
  | false :: L, h => by
    simp only [allF, List.all_cons, beq_self_eq_true, Bool.true_and] at h
    have := valB_pos L h
    simp only [valB]; omega

/-! ## The rebuild map -/

/-- A rebuild state: a single block of `3 (k + 1)` cells, the counter in round `m` with `r` sub-rounds left. -/
def rcfg (k m r : Nat) : Config := enc (k + 1) [] (cz m r).1 (cz m r).2

/-- What `rstep` needs to be told: the 0 bit `p` where the counter is cut, how many digits `c` the transient may
touch, its stretches, and the round `m'` of the next rebuild state. -/
structure Hint where
  p : Nat
  c : Nat
  segs : List Seg
  m' : Nat
  deriving Repr

/-- The counter after the transient as a number: round and sub-rounds left (`p = m`: no cut). -/
def joinC (p m r : Nat) (L' : List Bool) : Nat × Nat :=
  if p = m then (L'.length, valB L')
  else (L'.length + 1 + (m - p - 1), valB L' + 2 ^ (L'.length + 1) * (r / 2 ^ (p + 1)))

theorem runT_sound (fuel : Nat) (top : Bool) (gs : List Seg) (k c : Nat) (F' R : List Nat) (x y : Nat × List Nat)
    (hc : c ≤ k) (ht : top = true → R = []) (h : runSegs fuel top gs (List.replicate c 0, x) = some (F', y)) :
    ∃ n, steps n (enc 1 (List.replicate k 0) x.1 (x.2 ++ R)) =
      some (enc 1 (F' ++ List.replicate (k - c) 0) y.1 (y.2 ++ R)) := by
  have hk : List.replicate k 0 = List.replicate c 0 ++ List.replicate (k - c) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [hk]
  exact runSegs_sound fuel top gs _ _ x y h 1 _ R ht

/-- The next rebuild state, or `none` if the hint does not fit.  The counter is cut at a 0 bit `p < m`, or not at
all (`p = m`). -/
def rstep (fuel : Nat) (hh : Hint) (k m r : Nat) : Option (Nat × Nat × Nat) :=
  if hh.c ≤ k ∧ 1 ≤ r ∧ r ≤ 2 ^ m ∧ r % 2 ^ hh.p ≠ 0 ∧ hh.p ≤ m ∧ (hh.p = m ∨ r / 2 ^ hh.p % 2 = 0) then
    match startT (czb (bits hh.p r)) with
    | none => none
    | some x₁ =>
      match runSegs fuel (decide (hh.p = m)) hh.segs (List.replicate hh.c 0, x₁) with
      | none => none
      | some (F', y) =>
        let L' := decode y
        if czb L' = y ∧ allF L' = false then
          let m₁ := (joinC hh.p m r L').1
          let r₁ := (joinC hh.p m r L').2
          let K := k - hh.c
          let N := T F' + 2 ^ sig F' * (2 ^ K - 1)
          let V := 2 ^ (m₁ + 1) - r₁ + N
          if 2 ^ hh.m' ≤ V ∧ V < 2 ^ (hh.m' + 1) then
            some (sig F' + K, hh.m', 2 ^ (hh.m' + 1) - V)
          else none
        else none
  else none

theorem T_replicate' (K : Nat) : T (List.replicate K 0) = 2 ^ K - 1 := by
  have := T_replicate K; omega

theorem sig_replicate (K : Nat) : (List.map (· + 1) (List.replicate K 0)).sum = K := by
  induction K with
  | zero => rfl
  | succ K ih => rw [List.replicate_succ, List.map_cons, List.sum_cons, ih]; omega

/-- The rebuild, the transient on prefixes and the collapse, once the counter is cut (`x₀` and a tail `R`) and the
counter after the transient is a number again (`hj`). -/
theorem finish (fuel : Nat) (top : Bool) (segs : List Seg) (k c m₁ r₁ m' : Nat) (x₀ x₁ y : Nat × List Nat)
    (F' R : List Nat) (L' : List Bool) (hc : c ≤ k) (ht : top = true → R = []) (e1 : startT x₀ = some x₁)
    (e2 : runSegs fuel top segs (List.replicate c 0, x₁) = some (F', y)) (hy : czb L' = y)
    (hj : ((czb L').1, (czb L').2 ++ R) = cz m₁ r₁) (hr1 : 1 ≤ r₁) (hr2 : r₁ ≤ 2 ^ m₁)
    (hV1 : 2 ^ m' ≤ 2 ^ (m₁ + 1) - r₁ + (T F' + 2 ^ sig F' * (2 ^ (k - c) - 1)))
    (hV2 : 2 ^ (m₁ + 1) - r₁ + (T F' + 2 ^ sig F' * (2 ^ (k - c) - 1)) < 2 ^ (m' + 1)) :
    ∃ n, steps n (enc (k + 1) [] x₀.1 (x₀.2 ++ R)) =
      some (rcfg (sig F' + (k - c)) m' (2 ^ (m' + 1) - (2 ^ (m₁ + 1) - r₁ + (T F' + 2 ^ sig F' * (2 ^ (k - c) - 1))))) := by
  obtain ⟨n₁, h₁⟩ := startT_sound _ _ e1 k R
  obtain ⟨n₂, h₂⟩ := runT_sound fuel top segs k c F' R x₁ y hc ht e2
  subst hy
  rw [show (czb L').2 ++ R = ((czb L').1, (czb L').2 ++ R).2 from rfl,
    show (czb L').1 = ((czb L').1, (czb L').2 ++ R).1 from rfl, hj] at h₂
  have hT : T (F' ++ List.replicate (k - c) 0) = T F' + 2 ^ sig F' * (2 ^ (k - c) - 1) := by
    rw [T_append, T_replicate']
  have hg := giter_cz (T F' + 2 ^ sig F' * (2 ^ (k - c) - 1)) m₁ r₁ m' hr1 hr2 hV1 hV2
  obtain ⟨n₃, h₃⟩ := collapse _ 1 (F' ++ List.replicate (k - c) 0) _ _ hT hg
  rw [mass_append, sig_replicate] at h₃
  refine ⟨n₁ + n₂ + n₃, ?_⟩
  unfold rcfg
  refine steps_seq trans (steps_seq trans h₁ h₂) ?_
  rw [show sig F' + (k - c) + 1 = 1 + sig F' + (k - c) by omega]
  exact h₃

/-- **The rebuild map is sound**: from a rebuild state, the run reaches the rebuild state `rstep` computes. -/
theorem rstep_sound (fuel : Nat) (hh : Hint) (k m r k' m' r' : Nat) (h : rstep fuel hh k m r = some (k', m', r')) :
    ∃ n, steps n (rcfg k m r) = some (rcfg k' m' r') := by
  unfold rstep at h
  split at h
  case isFalse => simp at h
  rename_i hc
  obtain ⟨hck, hr1, hr2, hl, hpm, h0⟩ := hc
  cases e1 : startT (czb (bits hh.p r)) with
  | none => rw [e1] at h; simp at h
  | some x₁ =>
  rw [e1] at h
  simp only at h
  cases e2 : runSegs fuel (decide (hh.p = m)) hh.segs (List.replicate hh.c 0, x₁) with
  | none => rw [e2] at h; simp at h
  | some s =>
  obtain ⟨F', y⟩ := s
  rw [e2] at h
  simp only at h
  split at h
  case isFalse => simp at h
  rename_i hy
  obtain ⟨hy1, hy2⟩ := hy
  split at h
  case isFalse => simp at h
  rename_i hV
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hrm : r < 2 ^ m := by
    rcases Nat.lt_or_ge r (2 ^ m) with h' | h'
    · exact h'
    · exfalso
      have : r = 2 ^ m := by omega
      apply hl
      rw [this, show m = hh.p + (m - hh.p) by omega, Nat.pow_add, Nat.mul_mod_right]
  have hv := valB_lt (decode y)
  have hv1 := valB_pos _ hy2
  by_cases htop : hh.p = m
  · -- no cut: the whole counter is the prefix
    simp only [joinC, htop, ite_true] at hV ⊢
    subst htop
    have hcut : cz hh.p r = ((czb (bits hh.p r)).1, (czb (bits hh.p r)).2 ++ []) := by simp [cz]
    have hj : ((czb (decode y)).1, (czb (decode y)).2 ++ []) = cz (decode y).length (valB (decode y)) := by
      simp [cz, bits_valB]
    obtain ⟨n, hn⟩ := finish fuel _ hh.segs k hh.c _ _ hh.m' _ x₁ y F' [] (decode y) hck
      (fun _ => rfl) e1 e2 hy1 hj hv1
      (by omega) hV.1 hV.2
    refine ⟨n, ?_⟩
    unfold rcfg
    rw [hcut]
    exact hn
  · simp only [joinC, htop, ite_false] at hV ⊢
    have hp : hh.p < m := by omega
    have h0' : r / 2 ^ hh.p % 2 = 0 := by rcases h0 with h0 | h0; exact absurd h0 htop; exact h0
    have hcut := cz_split m hh.p r hp h0' hl
    have hH : r / 2 ^ (hh.p + 1) < 2 ^ (m - hh.p - 1) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show m - hh.p - 1 + (hh.p + 1) = m by omega]
      exact hrm
    have hjoin := cz_join (decode y) (m - hh.p - 1) (r / 2 ^ (hh.p + 1)) hy2
    rw [← bits_mod (m - hh.p - 1), Nat.mod_eq_of_lt hH] at hjoin
    have hr₂ : valB (decode y) + 2 ^ ((decode y).length + 1) * (r / 2 ^ (hh.p + 1)) ≤
        2 ^ ((decode y).length + 1 + (m - hh.p - 1)) := by
      have hH' : r / 2 ^ (hh.p + 1) + 1 ≤ 2 ^ (m - hh.p - 1) := hH
      have e : 2 ^ ((decode y).length + 1 + (m - hh.p - 1)) = 2 ^ (decode y).length * 2 * 2 ^ (m - hh.p - 1) := by
        rw [Nat.pow_add, Nat.pow_succ]
      rw [e, Nat.pow_succ]
      have := Nat.mul_le_mul_left (2 ^ (decode y).length * 2) hH'
      rw [Nat.mul_add, Nat.mul_one] at this
      generalize 2 ^ (decode y).length = a at hv this ⊢
      generalize r / 2 ^ (hh.p + 1) = H at this ⊢
      generalize 2 ^ (m - hh.p - 1) = b at this ⊢
      generalize a * 2 * H = P at this ⊢
      generalize a * 2 * b = Q at this ⊢
      omega
    obtain ⟨n, hn⟩ := finish fuel _ hh.segs k hh.c _ _ hh.m' _ x₁ y F' _ (decode y) hck
      (fun ht => absurd (of_decide_eq_true ht) htop) e1 e2 hy1 hjoin
      (by omega) hr₂ hV.1 hV.2
    refine ⟨n, ?_⟩
    unfold rcfg
    rw [hcut]
    exact hn

/-- Rebuild after rebuild. -/
def rrun (fuel : Nat) : List Hint → Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | [], s => some s
  | hh :: hs, (k, m, r) =>
    match rstep fuel hh k m r with
    | some s' => rrun fuel hs s'
    | none => none

theorem rrun_sound (fuel : Nat) : ∀ (hs : List Hint) (k m r k' m' r' : Nat),
    rrun fuel hs (k, m, r) = some (k', m', r') → ∃ n, steps n (rcfg k m r) = some (rcfg k' m' r')
  | [], k, m, r, k', m', r', h => by
    simp only [rrun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨0, rfl⟩
  | hh :: hs, k, m, r, k', m', r', h => by
    simp only [rrun] at h
    cases e : rstep fuel hh k m r with
    | none => rw [e] at h; simp at h
    | some s =>
      rw [e] at h
      obtain ⟨k₁, m₁, r₁⟩ := s
      obtain ⟨n₁, h₁⟩ := rstep_sound fuel hh k m r k₁ m₁ r₁ e
      obtain ⟨n₂, h₂⟩ := rrun_sound fuel hs k₁ m₁ r₁ k' m' r' h
      exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

/-- One more rebuild state on a run, for states given as triples. -/
theorem reach_step {c₀ : Config} {fuel : Nat} {hh : Hint} {s s' : Nat × Nat × Nat}
    (h₁ : ∃ n, steps n c₀ = some (rcfg s.1 s.2.1 s.2.2)) (h₂ : rstep fuel hh s.1 s.2.1 s.2.2 = some s') :
    ∃ n, steps n c₀ = some (rcfg s'.1 s'.2.1 s'.2.2) := by
  obtain ⟨n₁, e₁⟩ := h₁
  obtain ⟨n₂, e₂⟩ := rstep_sound fuel hh _ _ _ s'.1 s'.2.1 s'.2.2 (by rw [h₂])
  exact ⟨n₁ + n₂, steps_seq trans e₁ e₂⟩

end H4320
