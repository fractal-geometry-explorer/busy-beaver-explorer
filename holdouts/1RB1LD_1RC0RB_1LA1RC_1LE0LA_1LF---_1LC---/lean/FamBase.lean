import Phase

/-!
# Tools for rebuild families: reaching, the counters' encodings, and a phase that fills the up-counter

Written by `holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC/py/famprove.py`.  `fill` is the run of ticks that
takes the up-counter `u` (width `w`) to all ones: `2^w − 1 − val u` ticks, stated without arithmetic on the
down-counter: its lowest `w` digits are incremented `val u + 1` times (without overflow) and the rest decremented once.
-/

namespace H163594

open TM

set_option linter.unusedSimpArgs false

/-- `c` reaches `c'`. -/
def Reach (c c' : Config) : Prop := ∃ s, steps s c = some c'

theorem Reach.trans {a b c : Config} : Reach a b → Reach b c → Reach a c
  | ⟨s₁, h₁⟩, ⟨s₂, h₂⟩ => ⟨s₁ + s₂, steps_seq H163594.trans h₁ h₂⟩

theorem reach_of {a b : Config} {s : Nat} (h : steps s a = some b) : Reach a b := ⟨s, h⟩

theorem reach_congr {a a' b b' : Config} (h : Reach a b) (ha : a = a') (hb : b = b') : Reach a' b' := ha ▸ hb ▸ h

theorem encU_append (a b : List Bool) (L : Tape) : encU (a ++ b) L = encU a (encU b L) := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [encU, ih]

theorem encV_append (a b : List Bool) (R : Tape) : encV (a ++ b) R = encV a (encV b R) := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [encV, ih]

theorem encU_replicate (w : Nat) (b : Bool) (L : Tape) : encU (List.replicate w b) L = rep w (dU b) L := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, encU, ih]

theorem encV_replicate (w : Nat) (b : Bool) (R : Tape) : encV (List.replicate w b) R = rep w (dV b) R := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, encV, ih]

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

/-- Increment through a run of ones. -/
theorem inc_rt (a : Nat) (x : List Bool) : inc (List.replicate a true ++ x) = List.replicate a false ++ inc x := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, inc, ih]

/-- Decrement through a run of zeros. -/
theorem dec_rf (a : Nat) (x : List Bool) : dec (List.replicate a false ++ x) = List.replicate a true ++ dec x := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, dec, ih]

theorem rot_0 (n : Nat) (s : Tape) : cons false (rep n [false] s) = rep n [false] (cons false s) :=
  rep_rotate n [false] [false] [false] rfl s

theorem rot_1 (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep n [true] (cons true s) :=
  rep_rotate n [true] [true] [true] rfl s

/-- `c` copies of a word, as one word. -/
def wpow : Nat → List Bool → List Bool
  | 0, _ => []
  | c + 1, w => w ++ wpow c w

theorem rep_wpow (c : Nat) (w : List Bool) (X : Tape) : rep c w X = app (wpow c w) X := by
  induction c with
  | zero => rfl
  | succ c ih => rw [rep_succ, wpow, ← app_app, ih]

theorem rep_mul (c m : Nat) (w : List Bool) (s : Tape) : rep (c * m) w s = rep m (wpow c w) s := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, Nat.add_comm, rep_add, rep_succ, ← ih, rep_wpow]

theorem inc_false (x : List Bool) : inc (false :: x) = true :: x := rfl
theorem inc_true (x : List Bool) : inc (true :: x) = false :: inc x := rfl
theorem dec_true (x : List Bool) : dec (true :: x) = false :: x := rfl
theorem dec_false (x : List Bool) : dec (false :: x) = true :: dec x := rfl

theorem length_itr_inc (u : List Bool) : ∀ t, (itr inc t u).length = u.length
  | 0 => rfl
  | t + 1 => by rw [itr_succ', length_inc, length_itr_inc u t]

/-- **Fill the up-counter.** From `u` (width `w`) the ticks run until the up-counter is all ones, `2^w − 1 − val u`
of them: the lowest `w` digits of the down-counter go up by `t = val u + 1` (no overflow: each of the first `t`
increments finds a 0) and the digits above go down by one (they hold a 1). -/
theorem fill (H : List Bool) (hH : IsHdr H) (u vlo vhi : List Bool) (L R : Tape) (w t : Nat)
    (hw : u.length = w) (hlo : vlo.length = w) (ht : val u + 1 = t)
    (hno : ∀ i < t, false ∈ itr inc i vlo) (hhi : true ∈ vhi) :
    Reach (tcfg H u (vlo ++ vhi) L R) (tcfg H (List.replicate w true) (itr inc t vlo ++ dec vhi) L R) := by
  have hv0 : val vlo + t < 2 ^ w := by
    cases t with
    | zero => omega
    | succ t =>
      have h1 := iter_inc vlo
      have key : ∀ i, i ≤ t → val (itr inc i vlo) = val vlo + i ∧ (itr inc i vlo).length = vlo.length := by
        intro i hi
        induction i with
        | zero => simp [itr]
        | succ i ih =>
          obtain ⟨a1, a2⟩ := ih (by omega)
          rw [itr_succ']
          have hf := hno i (by omega)
          exact ⟨by rw [val_inc _ hf, a1]; omega, by rw [length_inc, a2]⟩
      obtain ⟨a1, a2⟩ := key t (Nat.le_refl _)
      have hf := hno t (by omega)
      have := val_lt (inc (itr inc t vlo))
      rw [length_inc, a2, hlo, val_inc _ hf, a1] at this
      omega
  have hX := val_dec vhi hhi
  have hP := val_lt vlo
  rw [hlo] at hP
  have hvU := val_lt u
  rw [hw] at hvU
  have hpos : 0 < val vhi := by
    have := mem_true_of_pos; clear this
    cases vhi with
    | nil => simp at hhi
    | cons b w' => cases b <;> simp [val] at hX ⊢ <;> omega
  have hV : val (vlo ++ vhi) = val vlo + 2 ^ w * val vhi := by rw [val_append, hlo]
  have hk : 2 ^ w - 1 - val u ≤ val (vlo ++ vhi) := by
    rw [hV]
    have : 2 ^ w ≤ 2 ^ w * val vhi := Nat.le_mul_of_pos_right _ hpos
    omega
  obtain ⟨u', v', s, hs, a1, a2, a3, a4⟩ := phase H hH u (vlo ++ vhi) L R (2 ^ w - 1 - val u) hk (by rw [hw]; omega)
  have eu : u' = List.replicate w true := val_inj _ _ (by rw [a1, hw, List.length_replicate])
    (by have := val_replicate_true w; generalize 2 ^ w = P at *; omega)
  have ev : v' = itr inc t vlo ++ dec vhi := by
    apply val_inj
    · rw [a2]; simp [length_itr_inc, length_dec]
    · obtain ⟨b1, b2⟩ := iter_inc vlo t (by rw [hlo]; exact hv0)
      rw [val_append, b2, hlo, b1]
      rw [hV] at a4
      have e2 : 2 ^ w * val (dec vhi) + 2 ^ w = 2 ^ w * val vhi := by
        rw [← hX, Nat.mul_add, Nat.mul_one]
      generalize 2 ^ w * val (dec vhi) = A at e2 ⊢
      generalize 2 ^ w * val vhi = B at e2 a4 hk ⊢
      generalize 2 ^ w = P at *
      omega
  subst eu; subst ev
  exact ⟨s, hs⟩

end H163594
