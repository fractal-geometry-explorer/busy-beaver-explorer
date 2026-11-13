import Phase
import Family

/-!
# The rebuild for every up-counter ending in `1^(2k+1) 0 b`, for every k ≥ 1

At V = 0 the tape is `L N 00 D> 0110101 (11)^n 1 0^inf`.  When the lowest 2k + 3 digits of N are, from the bottom,
2k + 1 ones, a 0 and a digit b (N ≡ 2^(2k+1) − 1 + b·2^(2k+2) mod 2^(2k+3)), the rebuild reads exactly those digits
(the walk of `py/rebuild_rule.py` goes O, O, ..., O and stops on the pair 01) and returns to a clean tick
configuration: the up-counter is the rest L (that is N >> (2k + 3)), the header is 0110101 for b = 0 and 0110111 for
b = 1, and the down-counter has n + 5k + 8 digits and the value

    2^(n + 5k + 8) − δ + b,    δ = 1 + 32^(k+1) · (3 · 2^(2k+3) − 1)

(`rebuild_family`, with k = m + 1 and n = 2m + p + 5, so n ≥ 2k + 3).  The rebuild is made of four local passes
(`Family.lean`, proved along symbolic runs) and four runs of 2^(2k) − 1 or 2^(2k+1) − 1 ticks (`Phase.lean`, by
induction on the number of ticks), each with the carry into a top word between them.  One theorem for the whole
family, in place of one theorem per residue class.
-/

namespace H49767

open TM

/-! ## Words and tapes -/

theorem rep_two_mul (w : List Bool) (s : Tape) : ∀ m, rep (2 * m) w s = rep m (w ++ w) s
  | 0 => rfl
  | m + 1 => by
    rw [show 2 * (m + 1) = (2 * m) + 1 + 1 by omega, rep_succ, rep_succ, rep_two_mul w s m, rep_succ, ← app_app]

theorem rep_five_mul (w : List Bool) (s : Tape) : ∀ m, rep (5 * m) w s = rep m (w ++ w ++ w ++ w ++ w) s
  | 0 => rfl
  | m + 1 => by
    rw [show 5 * (m + 1) = (5 * m) + 1 + 1 + 1 + 1 + 1 by omega]
    simp only [rep_succ, rep_five_mul w s m, app_app, List.append_assoc]

/-- Zeros commute with a repeat of zeros. -/
theorem rep_zero_cons (n : Nat) (s : Tape) :
    rep n [false, false, false, false, false] (cons false s) = cons false (rep n [false, false, false, false, false] s) :=
  (rep_rotate n [false] [false, false, false, false, false] [false, false, false, false, false] rfl s).symm

theorem encV_append (a b : List Bool) (R : Tape) : encV (a ++ b) R = encV a (encV b R) := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [encV, ih]

theorem encV_replicate (w : Nat) (b : Bool) (R : Tape) : encV (List.replicate w b) R = rep w (dV b) R := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, encV, ih]

theorem encU_replicate (w : Nat) (b : Bool) (L : Tape) : encU (List.replicate w b) L = rep w (dU b) L := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, encU, ih]

/-! ## Values -/

theorem val_append (a b : List Bool) : val (a ++ b) = val a + 2 ^ a.length * val b := by
  induction a with
  | nil => simp [val]
  | cons x a ih =>
    have e : 2 ^ (a.length + 1) * val b = 2 * (2 ^ a.length * val b) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ a.length) 2, Nat.mul_assoc]
    cases x <;> simp [val, ih, e] <;> omega

theorem val_replicate_false (w : Nat) : val (List.replicate w false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, val, ih]

theorem val_replicate_true (w : Nat) : val (List.replicate w true) + 1 = 2 ^ w := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, val, Nat.pow_succ]; omega

/-- Bit lists of the same length and value are equal. -/
theorem val_inj : ∀ u v : List Bool, u.length = v.length → val u = val v → u = v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: u, b :: v, h, hv => by
    have hl : u.length = v.length := by simpa using h
    cases a <;> cases b <;> simp [val] at hv
    · rw [val_inj u v hl (by omega)]
    · omega
    · omega
    · rw [val_inj u v hl (by omega)]


/-! ## Reaching -/

/-- `c` reaches `c'`. -/
def Reach (c c' : Config) : Prop := ∃ s, steps s c = some c'

theorem Reach.trans {a b c : Config} : Reach a b → Reach b c → Reach a c
  | ⟨s₁, h₁⟩, ⟨s₂, h₂⟩ => ⟨s₁ + s₂, steps_seq H49767.trans h₁ h₂⟩

theorem reach_of {a b : Config} {s : Nat} (h : steps s a = some b) : Reach a b := ⟨s, h⟩

theorem reach_congr {a a' b b' : Config} {s : Nat} (h : steps s a = some b) (ha : a = a') (hb : b = b') :
    Reach a' b' := ⟨s, ha ▸ hb ▸ h⟩

/-- A run of ticks with its end given exactly. -/
theorem phase_exact (H : List Bool) (hH : H = hdr0 ∨ H = hdr1) (u v u' v' : List Bool) (L R : Tape) (k : Nat)
    (hk : k ≤ val v) (hu : val u + k < 2 ^ u.length) (h1 : u'.length = u.length) (h2 : v'.length = v.length)
    (h3 : val u' = val u + k) (h4 : val v' + k = val v) :
    Reach (tcfg H u v L R) (tcfg H u' v' L R) := by
  obtain ⟨x, y, s, hs, a1, a2, a3, a4⟩ := phase H hH u v L R k hk hu
  have ex : x = u' := val_inj _ _ (by rw [a1, h1]) (by rw [a3, h3])
  have ey : y = v' := val_inj _ _ (by rw [a2, h2]) (by omega)
  subst ex; subst ey
  exact ⟨s, hs⟩

/-- The carry of a full counter into a top word whose nearest cell is 0 (header 0110111, V even). -/
theorem carry_top (w i : Nat) (v : List Bool) (L R : Tape) :
    Reach (tcfg hdr1 (List.replicate w true) (List.replicate (i + 1) false ++ true :: v) (cons false L) R)
          (tcfg hdr1 (List.replicate w false) (List.replicate (i + 1) true ++ false :: v) (cons true L) R) := by
  refine ⟨8 * i + 10 * w + 42, ?_⟩
  have h := carry1_even i w L (encV v R)
  simp only [tcfg, encU_replicate, encV_append, encV_replicate, encV, dU, dV, hdr1, app] at h ⊢
  rw [← rep_app_comm i [false, true]]
  simpa [app] using h

/-! ## The values of the down-counter along the way -/

theorem val_ones (b : Nat) : val (List.replicate b true) + 1 = 2 ^ b := val_replicate_true b

/-- `0^a 1^b` has the value 2^(a+b) − 2^a. -/
theorem val_zeros_ones (a b : Nat) : val (List.replicate a false ++ List.replicate b true) + 2 ^ a = 2 ^ (a + b) := by
  rw [val_append, val_replicate_false, List.length_replicate, Nat.pow_add]
  have h := val_ones b
  generalize val (List.replicate b true) = T at h ⊢
  rw [← h]
  rw [Nat.mul_add, Nat.mul_one]; omega

/-- `1^a 0 1^b` has the value 2^(a+1+b) − 2^a − 1. -/
theorem val_ones_zero_ones (a b : Nat) :
    val (List.replicate a true ++ false :: List.replicate b true) + 2 ^ a + 1 = 2 ^ (a + 1 + b) := by
  rw [val_append, List.length_replicate]
  have h1 := val_ones a
  have h2 := val_ones b
  have e : val (false :: List.replicate b true) = 2 * val (List.replicate b true) := by simp [val]
  rw [e, Nat.pow_add, Nat.pow_succ]
  generalize val (List.replicate b true) = T at h2 ⊢
  rw [← h2]
  generalize 2 ^ a = X at h1 ⊢
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]; omega

/-- `0^a 1 0 1^b` has the value 2^(a+2+b) − 3 · 2^a. -/
theorem val_zeros_one_zero_ones (a b : Nat) :
    val (List.replicate a false ++ true :: false :: List.replicate b true) + 2 ^ a + 2 ^ a + 2 ^ a = 2 ^ (a + 2 + b) := by
  rw [val_append, val_replicate_false, List.length_replicate]
  have h2 := val_ones b
  have e : val (true :: false :: List.replicate b true) = 1 + 4 * val (List.replicate b true) := by
    simp [val]; omega
  rw [e, Nat.pow_add, Nat.pow_add]
  generalize val (List.replicate b true) = T at h2 ⊢
  rw [← h2]
  generalize 2 ^ a = X
  rw [show (2 : Nat) ^ 2 = 4 from rfl]
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]; omega


/-! ## The rebuild -/

theorem rep_Z_succ (n : Nat) (X : Tape) :
    rep (n + 1) [false, false, false, false, false] X =
      cons false (rep n [false, false, false, false, false] (app [false, false, false, false] X)) := by
  rw [← rep_app_comm]; exact rep_zero_cons n (app [false, false, false, false] X)

/-- The new down-counter, least significant digit first. -/
def Vfam (m p : Nat) : Bool → List Bool
  | false => List.replicate (5 * m + 10) true ++ List.replicate (2 * m + 5) false ++ true :: false :: List.replicate (p + 1) true
  | true => List.replicate (5 * m + 10) false ++ true :: List.replicate (2 * m + 4) false ++ true :: false ::
      List.replicate (p + 1) true

/-- The new header: 0110101 after a digit 0, 0110111 after a digit 1. -/
def hdrOf : Bool → List Bool
  | false => hdr0
  | true => hdr1

section
variable (m p : Nat)

local notation "rf" => List.replicate
local notation "R0" => cons true blank

theorem stageA (L : Tape) :
    Reach ⟨cons false (cons false (rep (2 * m + 3) [true, false, false, false, false] (app [false, false, false, false, false] L))),
           app hdr0 (rep (2 * m + p + 5) [true, true] R0), .D⟩
      (tcfg hdr1 (rf (2 * m + 2) false) (rf (2 * m + p + 6) true)
        (app [false, false, false, false, true] (app [false, false, false, false] L)) R0) := by
  have h := segA m p L
  have e : rep (2 * m + 3) [false, false, false, false, false] (cons true (cons false (cons false (cons false (cons false L))))) =
      cons false (rep (2 * m + 2) [false, false, false, false, false] (app [false, false, false, false, true] (app [false, false, false, false] L))) :=
    rep_Z_succ (2 * m + 2) _
  rw [e] at h
  refine reach_congr h (by simp [hdr0, app]) ?_
  simp only [tcfg, encU_replicate, encV_replicate, dU, dV, hdr1]
  rw [show 2 * m + p + 6 = (2 * m + p + 5) + 1 by omega, ← rep_app_comm (2 * m + p + 5) [false, true]]
  simp only [app]

theorem stageP1 (L : Tape) :
    Reach (tcfg hdr1 (rf (2 * m + 2) false) (rf (2 * m + p + 6) true) L R0)
      (tcfg hdr1 (rf (2 * m + 2) true) (rf (2 * m + 1 + 1) false ++ true :: rf (p + 3) true) L R0) := by
  have e1 := val_ones (2 * m + 2)
  have e2 := val_ones (2 * m + p + 6)
  have e3 := val_zeros_ones (2 * m + 2) (p + 4)
  rw [show 2 * m + 2 + (p + 4) = 2 * m + p + 6 by omega] at e3
  have e4 : rf (2 * m + 1 + 1) false ++ true :: rf (p + 3) true = rf (2 * m + 2) false ++ rf (p + 4) true := by
    simp [List.replicate_succ]
  have hp := Nat.two_pow_pos (2 * m + 2)
  rw [e4]
  apply phase_exact hdr1 (Or.inr rfl) _ _ _ _ L R0 (2 ^ (2 * m + 2) - 1)
  · omega
  · simp [val_replicate_false]; omega
  · simp
  · simp; omega
  · simp [val_replicate_false]; omega
  · omega

theorem stageC1 (L : Tape) :
    Reach (tcfg hdr1 (rf (2 * m + 2) true) (rf (2 * m + 1 + 1) false ++ true :: rf (p + 3) true)
            (app [false, false, false, false, true] (app [false, false, false, false] L)) R0)
      (tcfg hdr1 (rf (2 * m + 2) false) (rf (2 * m + 1 + 1) true ++ false :: rf (p + 3) true)
            (cons true (app [false, false, false, true] (app [false, false, false, false] L))) R0) :=
  carry_top (2 * m + 2) (2 * m + 1) (rf (p + 3) true) (app [false, false, false, true] (app [false, false, false, false] L)) R0

theorem stageP2 (L : Tape) :
    Reach (tcfg hdr1 (rf (2 * m + 2) false) (rf (2 * m + 1 + 1) true ++ false :: rf (p + 3) true) L R0)
      (tcfg hdr1 (rf (2 * m + 2) true) (rf (2 * m + 3) false ++ rf (p + 3) true) L R0) := by
  have e1 := val_ones (2 * m + 2)
  have e2 := val_ones_zero_ones (2 * m + 2) (p + 3)
  have e3 := val_zeros_ones (2 * m + 3) (p + 3)
  rw [show 2 * m + 2 + 1 + (p + 3) = 2 * m + p + 6 by omega] at e2
  rw [show 2 * m + 3 + (p + 3) = 2 * m + p + 6 by omega] at e3
  rw [show 2 * m + 1 + 1 = 2 * m + 2 by omega]
  have e4 : 2 ^ (2 * m + 3) = 2 ^ (2 * m + 2) * 2 := by
    rw [show 2 * m + 3 = (2 * m + 2) + 1 by omega, Nat.pow_succ]
  have hp := Nat.two_pow_pos (2 * m + 2)
  apply phase_exact hdr1 (Or.inr rfl) _ _ _ _ L R0 (2 ^ (2 * m + 2) - 1)
  · omega
  · simp [val_replicate_false]; omega
  · simp
  · simp; omega
  · simp [val_replicate_false]; omega
  · omega

theorem stageB (L : Tape) :
    Reach (tcfg hdr1 (rf (2 * m + 2) true) (rf (2 * m + 3) false ++ rf (p + 3) true)
            (cons true (app [false, false, false, true] (app [false, false, false, false] L))) R0)
      (tcfg hdr1 (rf (2 * m + 3) false) (rf (2 * m + 3) true ++ false :: rf (p + 2) true)
            (app [false, false, false, true] L) R0) := by
  have h := segB m p L
  refine reach_congr h ?_ ?_
  · simp only [tcfg, encU_replicate, encV_append, encV_replicate, dU, dV, hdr1, app]
  · simp only [tcfg, encU_replicate, encV_append, encV_replicate, encV, dU, dV, hdr1]
    rw [show 2 * m + 3 = (2 * m + 2) + 1 by omega, ← rep_app_comm (2 * m + 2) [false, false, false, false, false],
      ← rep_app_comm (2 * m + 2) [false, true]]
    simp only [app]

theorem stageP3 (L : Tape) :
    Reach (tcfg hdr1 (rf (2 * m + 3) false) (rf (2 * m + 3) true ++ false :: rf (p + 2) true) L R0)
      (tcfg hdr1 (rf (2 * m + 3) true) (rf (2 * m + 3 + 1) false ++ true :: rf (p + 1) true) L R0) := by
  have e1 := val_ones (2 * m + 3)
  have e2 := val_ones_zero_ones (2 * m + 3) (p + 2)
  have e3 := val_zeros_ones (2 * m + 3 + 1) (p + 2)
  have e4 : rf (2 * m + 3 + 1) false ++ true :: rf (p + 1) true = rf (2 * m + 3 + 1) false ++ rf (p + 2) true := by
    simp [List.replicate_succ]
  rw [show 2 * m + 3 + 1 + (p + 2) = 2 * m + p + 6 by omega] at e2 e3
  rw [Nat.pow_succ] at e3
  have hp := Nat.two_pow_pos (2 * m + 3)
  rw [e4]
  apply phase_exact hdr1 (Or.inr rfl) _ _ _ _ L R0 (2 ^ (2 * m + 3) - 1)
  · omega
  · simp [val_replicate_false]; omega
  · simp
  · simp; omega
  · simp [val_replicate_false]; omega
  · omega

theorem stageC2 (L : Tape) :
    Reach (tcfg hdr1 (rf (2 * m + 3) true) (rf (2 * m + 3 + 1) false ++ true :: rf (p + 1) true)
            (app [false, false, false, true] L) R0)
      (tcfg hdr1 (rf (2 * m + 3) false) (rf (2 * m + 3 + 1) true ++ false :: rf (p + 1) true)
            (cons true (app [false, false, true] L)) R0) :=
  carry_top (2 * m + 3) (2 * m + 3) (rf (p + 1) true) (app [false, false, true] L) R0

theorem stageP4 (L : Tape) :
    Reach (tcfg hdr1 (rf (2 * m + 3) false) (rf (2 * m + 3 + 1) true ++ false :: rf (p + 1) true) L R0)
      (tcfg hdr1 (rf (2 * m + 3) true) (rf (2 * m + 3) false ++ true :: false :: rf (p + 1) true) L R0) := by
  have e1 := val_ones (2 * m + 3)
  have e2 := val_ones_zero_ones (2 * m + 3 + 1) (p + 1)
  have e3 := val_zeros_one_zero_ones (2 * m + 3) (p + 1)
  rw [show 2 * m + 3 + 1 + 1 + (p + 1) = 2 * m + p + 6 by omega, Nat.pow_succ] at e2
  rw [show 2 * m + 3 + 2 + (p + 1) = 2 * m + p + 6 by omega] at e3
  have hp := Nat.two_pow_pos (2 * m + 3)
  apply phase_exact hdr1 (Or.inr rfl) _ _ _ _ L R0 (2 ^ (2 * m + 3) - 1)
  · omega
  · simp [val_replicate_false]; omega
  · simp
  · simp; omega
  · simp [val_replicate_false]; omega
  · omega

/-- Three digits nearest the gap, then `m` pairs of digits. -/
theorem rep_3_2m (w : List Bool) (X : Tape) :
    rep (2 * m + 3) w X = app w (app w (app w (rep m (w ++ w) X))) := by
  rw [show 2 * m + 3 = 3 + 2 * m by omega, rep_add, rep_two_mul]; rfl

/-- `m` pairs of digits, then three more. -/
theorem rep_2m_3 (w : List Bool) (X : Tape) :
    rep (2 * m + 3) w X = rep m (w ++ w) (app w (app w (app w X))) := by
  rw [rep_add, rep_two_mul]; rfl

theorem stageC (b : Bool) (L0 : Tape) :
    Reach (tcfg hdr1 (rf (2 * m + 3) true) (rf (2 * m + 3) false ++ true :: false :: rf (p + 1) true)
            (cons true (app [false, false, true] (app (dU b) L0))) R0)
      ⟨cons false (cons false L0), app (hdrOf b) (encV (Vfam m p b) R0), .D⟩ := by
  cases b
  · have h := segC0 m p L0
    refine reach_congr h ?_ ?_
    · simp only [tcfg, encU_replicate, encV_append, encV_replicate, encV, dU, dV, hdr1]
      rw [rep_3_2m m [true, false, false, false, false], rep_2m_3 m [true, true]]
      simp only [app, List.cons_append, List.nil_append]
    · simp only [Vfam, hdrOf, hdr0, encV_append, encV_replicate, encV, dV]
      rw [show 5 * m + 10 = 2 + (5 * m + 8) by omega, rep_add 2 (5 * m + 8), rep_add (5 * m) 8, rep_five_mul,
        show 2 * m + 5 = 2 + (2 * m + 3) by omega, rep_add 2 (2 * m + 3), rep_2m_3 m [true, true]]
      simp only [app, rep_succ, rep_zero, List.cons_append, List.nil_append]
  · have h := segC1 m p L0
    refine reach_congr h ?_ ?_
    · simp only [tcfg, encU_replicate, encV_append, encV_replicate, encV, dU, dV, hdr1]
      rw [rep_3_2m m [true, false, false, false, false], rep_2m_3 m [true, true]]
      simp only [app, List.cons_append, List.nil_append]
    · simp only [Vfam, hdrOf, hdr1, encV_append, encV_replicate, encV, dV]
      rw [show 5 * m + 10 = 2 + (5 * m + 8) by omega, rep_add 2 (5 * m + 8), rep_add (5 * m) 8, rep_five_mul,
        show 2 * m + 4 = 1 + (2 * m + 3) by omega, rep_add 1 (2 * m + 3), rep_2m_3 m [true, true]]
      simp only [app, rep_succ, rep_zero, List.cons_append, List.nil_append]

/-- The whole rebuild: from `L b 0 1^(2m+3) 00 D> 0110101 (11)^(2m+p+5) 1 0^inf` to a clean tick configuration. -/
theorem rebuild_family (b : Bool) (L0 : Tape) :
    Reach ⟨cons false (cons false (rep (2 * m + 3) [true, false, false, false, false]
              (app [false, false, false, false, false] (app (dU b) L0)))),
           app hdr0 (rep (2 * m + p + 5) [true, true] R0), .D⟩
      ⟨cons false (cons false L0), app (hdrOf b) (encV (Vfam m p b) R0), .D⟩ :=
  (stageA m p _).trans ((stageP1 m p _).trans ((stageC1 m p _).trans ((stageP2 m p _).trans ((stageB m p _).trans
    ((stageP3 m p _).trans ((stageC2 m p _).trans ((stageP4 m p _).trans (stageC m p b L0))))))))

end

/-- The length of the new down-counter: n + 5k + 8 with n = 2m + p + 5, k = m + 1. -/
theorem length_Vfam (m p : Nat) (b : Bool) : (Vfam m p b).length = 7 * m + p + 18 := by
  cases b <;> simp [Vfam] <;> omega

/-- Its value: 2^(n + 5k + 8) − δ + b with δ = 3 · 2^(7m+15) − 2^(5m+10) + 1 = 1 + 32^(k+1) (3 · 2^(2k+3) − 1). -/
theorem val_Vfam (m p : Nat) (b : Bool) :
    val (Vfam m p b) + 3 * 2 ^ (7 * m + 15) + 1 = 2 ^ (7 * m + p + 18) + 2 ^ (5 * m + 10) + (if b then 1 else 0) := by
  have hA : 2 ^ (7 * m + 15) = 2 ^ (5 * m + 10) * 2 ^ (2 * m + 5) := by rw [← Nat.pow_add]; congr 1; omega
  have hE : 2 ^ (7 * m + p + 18) = 2 ^ (5 * m + 10) * 2 ^ (2 * m + 5 + 2 + (p + 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hA, hE]
  cases b
  · simp only [Vfam, List.append_assoc]
    rw [val_append, List.length_replicate]
    have h1 := val_ones (5 * m + 10)
    have h2 := val_zeros_one_zero_ones (2 * m + 5) (p + 1)
    rw [← h2]
    simp only [Nat.mul_add, Bool.false_eq_true, ↓reduceIte]
    omega
  · simp only [Vfam, List.append_assoc, List.cons_append]
    rw [val_append, val_replicate_false, List.length_replicate]
    have h2 := val_zeros_one_zero_ones (2 * m + 4) (p + 1)
    have e : val (true :: (List.replicate (2 * m + 4) false ++ true :: false :: List.replicate (p + 1) true)) =
        1 + 2 * val (List.replicate (2 * m + 4) false ++ true :: false :: List.replicate (p + 1) true) := by simp [val]
    rw [e]
    have e2 : 2 ^ (2 * m + 5) = 2 * 2 ^ (2 * m + 4) := by
      rw [show 2 * m + 5 = (2 * m + 4) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have e3 : 2 ^ (2 * m + 5 + 2 + (p + 1)) = 2 * 2 ^ (2 * m + 4 + 2 + (p + 1)) := by
      rw [show 2 * m + 5 + 2 + (p + 1) = (2 * m + 4 + 2 + (p + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    rw [e2, e3, ← h2]
    simp only [Nat.mul_add, ↓reduceIte]
    omega

end H49767
