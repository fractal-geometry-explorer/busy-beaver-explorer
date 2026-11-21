import TailPhase
import TM.MapOrbit

/-!
# The phase map on (M, tail), as far as it is proved

A tail is a list of blocks, `enc [u₀, u₁, …] = 0 1^u₀ 0 1^u₁ … 0^inf`, and `PS M (enc T)` is a phase start.  `phi`
is the phase map: from `PS M (enc T)` the machine reaches `PS M' (enc T')` whenever `phi (M, T) = some (M', T')`
(`phi_sound`).  It is defined for every tail except one shape: two ones left over (M = 1 mod 3, possibly after
blocks were taken in by `d_merge`) and the tail starting with blocks of one 1, then a block of two ones that is not
the last block.  There `phi` is `none`, meaning *not covered*, not *halts*: every halt of the machine lies in that
shape (no other case halts), so

* `not_halts_of_covered`: if the orbit of `phi` from `PS(9, [])` (step 36 from blank tape) never leaves the covered
  tails, the machine does not halt.

That condition is not proved: it is a statement about the residues mod 3 along the orbit (Python: no uncovered tail
in the first 30,000 phases).
-/

namespace H103424

open TM

/-- A tail of blocks of ones, each after a 0. -/
def enc : List Nat → Tape
  | [] => blank
  | u :: R => cons false (rep u [true] (enc R))

theorem enc_ones (n : Nat) (L : List Nat) : enc (List.replicate n 1 ++ L) = rep n [false, true] (enc L) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show cons false (rep 1 [true] (enc (List.replicate n 1 ++ L))) = cons false (cons true (rep n [false, true] (enc L)))
    rw [ih]
    rfl

/-- The number of leading blocks `1`, and the rest. -/
def lead1 : List Nat → Nat × List Nat
  | [] => (0, [])
  | u :: R => if u = 1 then ((lead1 R).1 + 1, (lead1 R).2) else (0, u :: R)

theorem lead1_spec : ∀ T : List Nat, T = List.replicate (lead1 T).1 1 ++ (lead1 T).2
  | [] => rfl
  | u :: R => by
    by_cases hu : u = 1
    · subst hu
      simp only [lead1, ite_true, List.replicate_succ, List.cons_append]
      exact congrArg _ (lead1_spec R)
    · simp [lead1, hu]

/-- Two ones left over and a tail of j blocks `1` (then the end or an empty block). -/
def endOnes (k : Nat) : Nat → Option (Nat × List Nat)
  | 0 => if 2 ≤ k then some (2 * k + 3, [6]) else none
  | j + 1 => some (2 * k + 3, [2 * j + 8])

/-- Two ones left over and a tail of j blocks `1` and a last block `1 1`. -/
def endTwo (k : Nat) : Nat → Option (Nat × List Nat)
  | 0 => if 1 ≤ k then some (2 * k + 1, [4, 1, 1, 1]) else none
  | j + 1 => some (2 * k + 3, [2 * j + 4, 6])

/-- Two ones left over, j blocks `1`, then the blocks r (not starting with a block `1`). -/
def end2r (k j : Nat) : List Nat → Option (Nat × List Nat)
  | [] => endOnes k j
  | [0] => endOnes k j
  | 0 :: y :: R => some (2 * k + 3, (2 * j + 6 + y) :: R)
  | [2] => endTwo k j
  | x :: R => if 3 ≤ x then some (2 * k + 7, List.replicate (j + 2) 1 ++ (x - 3) :: R) else none

/-- The end of a phase with two ones left over, on the wall of k pairs. -/
def end2 (k : Nat) (T : List Nat) : Option (Nat × List Nat) := end2r k (lead1 T).1 (lead1 T).2

/-- The end of a phase from the wall `DW k (1^m enc T)`, m < 3; one ones left over takes in the next block. -/
def dEnd : Nat → Nat → List Nat → Option (Nat × List Nat)
  | k, 0, [] => some (2 * k + 7, [])
  | k, 0, u :: R => some (2 * k + 7 + u, R)
  | k, 1, [] => some (2 * k + 9, [])
  | k, 1, u :: R => dEnd (k + 1 + 4 * (u / 3)) (u % 3) R
  | k, 2, T => end2 k T
  | _, _, _ => none

/-- The phase map; `none` where it is not covered. -/
def phi (s : Nat × List Nat) : Option (Nat × List Nat) :=
  if s.1 < 5 then none else dEnd (5 + 4 * ((s.1 - 5) / 3)) ((s.1 - 5) % 3) s.2

theorem reach_trans {a b c : Config} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  exact ⟨s + t, steps_seq trans hs ht⟩

theorem reach_of {n : Nat} {c d d' : Config} (h : steps n c = some d) (e : d = d') : Reach c d' := ⟨n, e ▸ h⟩

theorem endOnes_sound (k j M' : Nat) (T' : List Nat) (h : endOnes k j = some (M', T')) :
    Reach (DW k (cons true (cons true (rep j [false, true] blank)))) (PS M' (enc T')) := by
  cases j with
  | zero =>
    by_cases hk : 2 ≤ k
    · simp only [endOnes, hk, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
      have h := end_e2 i
      simp only [ones_cons, pairs_ones] at h
      exact reach_ps (by omega) ⟨_, h⟩
    · simp [endOnes, hk] at h
  | succ i =>
    simp only [endOnes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact d_ones2 k i

theorem endTwo_sound (k j M' : Nat) (T' : List Nat) (h : endTwo k j = some (M', T')) :
    Reach (DW k (cons true (cons true (rep j [false, true] (enc [2]))))) (PS M' (enc T')) := by
  cases j with
  | zero =>
    by_cases hk : 1 ≤ k
    · simp only [endTwo, hk, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      have h := two0 i
      simp only [ones_cons, pairs_ones, cons_false_blank] at h
      have h' : Reach _ _ := ⟨_, h⟩
      exact reach_ps (by omega) h'
    · simp [endTwo, hk] at h
  | succ i =>
    simp only [endTwo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h := two2 i k
    simp only [ones_cons, pairs_ones] at h
    exact reach_ps (by omega) ⟨_, h⟩

theorem end2r_sound (k j : Nat) (r : List Nat) (M' : Nat) (T' : List Nat) (h : end2r k j r = some (M', T')) :
    Reach (DW k (cons true (cons true (rep j [false, true] (enc r))))) (PS M' (enc T')) := by
  rcases r with _ | ⟨x, R⟩
  · exact endOnes_sound k j M' T' h
  · rcases x with _ | _ | _ | x
    · rcases R with _ | ⟨y, R⟩
      · have e : enc [0] = blank := cons_false_blank
        rw [e]
        exact endOnes_sound k j M' T' h
      · simp only [end2r, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := d_zero2 k j (rep y [true] (enc R))
        show Reach _ (PS _ (cons false (rep _ [true] (enc R))))
        rw [← ones_rep]
        exact this
    · simp [end2r] at h
    · rcases R with _ | ⟨y, R⟩
      · exact endTwo_sound k j M' T' h
      · simp [end2r] at h
    · simp only [end2r, show 3 ≤ x + 1 + 1 + 1 from by omega, ite_true, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [enc_ones]
      exact d_push2 k j x (enc R)

theorem end2_sound (k : Nat) (T : List Nat) (M' : Nat) (T' : List Nat) (h : end2 k T = some (M', T')) :
    Reach (DW k (cons true (cons true (enc T)))) (PS M' (enc T')) := by
  unfold end2 at h
  have hT := lead1_spec T
  generalize (lead1 T).1 = j at h hT
  generalize (lead1 T).2 = r at h hT
  subst hT
  rw [enc_ones]
  exact end2r_sound k j r M' T' h

theorem dEnd_sound : ∀ (T : List Nat) (k m M' : Nat) (T' : List Nat), dEnd k m T = some (M', T') →
    Reach (DW k (rep m [true] (enc T))) (PS M' (enc T'))
  | [], k, 0, M', T', h => by
    simp only [dEnd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h := end_e0 k
    simp only [ones_cons, pairs_ones] at h
    have h' : Reach _ _ := ⟨_, h⟩
    exact reach_ps (by omega) h'
  | u :: R, k, 0, M', T', h => by
    simp only [dEnd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact d_pop k u (enc R)
  | [], k, 1, M', T', h => by
    simp only [dEnd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h := end_e1 k
    simp only [ones_cons, pairs_ones, ones_snoc] at h
    have h' : Reach _ _ := ⟨_, h⟩
    exact reach_ps (by omega) h'
  | u :: R, k, 1, M', T', h => by
    simp only [dEnd] at h
    have ih := dEnd_sound R _ _ M' T' h
    show Reach (DW k (cons true (cons false (rep u [true] (enc R))))) _
    rw [d_merge]
    obtain ⟨s, hs⟩ := rounds (u / 3) (k + 1) (u % 3) (enc R)
    rw [show 3 * (u / 3) + u % 3 = u by omega] at hs
    exact reach_trans ⟨s, hs⟩ ih
  | T, k, 2, M', T', h => by
    simp only [dEnd] at h
    exact end2_sound k T M' T' h
  | T, k, m + 3, M', T', h => by
    cases T <;> simp [dEnd] at h

theorem ps_plus (q m : Nat) (T : Tape) :
    Plus trans (PS (3 * q + 5 + m) T) (DW (5 + 4 * q) (rep m [true] T)) := by
  have h1 := start (3 * q + m) T
  obtain ⟨s2, h2⟩ := rounds q 5 m T
  rw [show 3 * q + 5 + m = 3 * q + m + 5 by omega]
  exact ⟨51 + s2, by rw [show 51 + s2 + 1 = 52 + s2 by omega]; exact steps_seq trans h1 h2⟩

theorem phi_sound (M : Nat) (T : List Nat) (M' : Nat) (T' : List Nat) (h : phi (M, T) = some (M', T')) :
    Plus trans (PS M (enc T)) (PS M' (enc T')) := by
  unfold phi at h
  simp only at h
  split at h
  · cases h
  · have hp := ps_plus ((M - 5) / 3) ((M - 5) % 3) (enc T)
    rw [show 3 * ((M - 5) / 3) + 5 + (M - 5) % 3 = M by omega] at hp
    obtain ⟨s, hs⟩ := dEnd_sound T _ _ M' T' h
    exact hp.trans_star ⟨s, hs⟩

/-- From blank tape the first phase start is PS(9, []), at step 36. -/
theorem blank9 : steps 36 init = some (PS 9 (enc [])) := rfl

/-- **The conditional reduction**, from any configuration that reaches a phase start: if the orbit of the phase map
from there stays among the covered tails for ever, the machine does not halt. -/
theorem not_halts_from {c₀ : Config} {t M₀ : Nat} {T₀ : List Nat} (h₀ : steps t c₀ = some (PS M₀ (enc T₀)))
    (h : ∀ n, ∃ s, orbit phi (M₀, T₀) n = some s) : ¬ TM.Halts trans c₀ := by
  have reach : ∀ n s, orbit phi (M₀, T₀) n = some s → ∃ t', n ≤ t' ∧ steps t' c₀ = some (PS s.1 (enc s.2)) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      cases hs
      exact ⟨t, Nat.zero_le _, h₀⟩
    | succ n ih =>
      intro s hs
      simp only [orbit] at hs
      cases e : orbit phi (M₀, T₀) n with
      | none => rw [e] at hs; cases hs
      | some s₁ =>
        rw [e] at hs
        simp only [Option.bind] at hs
        obtain ⟨t', ht, hc⟩ := ih s₁ e
        obtain ⟨u, hu⟩ := phi_sound s₁.1 s₁.2 s.1 s.2 hs
        exact ⟨t' + (u + 1), by omega, steps_seq trans hc hu⟩
  apply not_halts_of_forall trans
  apply forall_of_unbounded trans (fun t => ∃ c, steps t c₀ = some c)
  · intro N
    obtain ⟨s, hs⟩ := h N
    obtain ⟨t', ht, hc⟩ := reach N s hs
    exact ⟨t', ht, _, hc⟩
  · intro t ht
    exact ht

/-- **The conditional reduction** from blank tape: if the orbit of the phase map from PS(9, []) stays among the
covered tails for ever, the machine does not halt. -/
theorem not_halts_of_covered (h : ∀ n, ∃ s, orbit phi (9, []) n = some s) : ¬ HaltsFromBlank :=
  not_halts_from blank9 h

end H103424
