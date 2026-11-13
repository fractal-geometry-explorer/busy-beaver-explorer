import Rules

/-!
# A whole phase of ticks, for every pair of counters

`Rules.lean` proves one tick (U + 1, V − 1) for every number of carries and borrows. Here the counters are
written as bit lists (least significant first) of a fixed width, the tick is restated on them, and an induction on
the number of ticks gives a whole run of ticks: from `U = x`, `V = y` the machine reaches `U = x + k`, `V = y − k`
for every `k ≤ y` with `x + k < 2^a` (`a` the width of U), whatever the tape beyond the two counters.

The rebuild after V = 0 is made of such runs (its sub-phases) and short local passes between them; this lemma is
the part of a general rebuild proof that does not depend on the digits of N.
-/

namespace H49767

open TM

/-- One digit of the up-counter, as the left stream lists it (nearest the head first): `00001` is 1, `00000` 0. -/
def dU : Bool → List Bool
  | true => [true, false, false, false, false]
  | false => [false, false, false, false, false]

/-- One digit of the down-counter, read rightwards: `01` is 1, `11` is 0. -/
def dV : Bool → List Bool
  | true => [false, true]
  | false => [true, true]

/-- The up-counter, least significant digit next to the gap, in front of the left tape `L`. -/
def encU : List Bool → Tape → Tape
  | [], L => L
  | b :: u, L => app (dU b) (encU u L)

/-- The down-counter, least significant digit first, in front of the right tape `R`. -/
def encV : List Bool → Tape → Tape
  | [], R => R
  | b :: v, R => app (dV b) (encV v R)

/-- Binary increment of a fixed-width bit list (least significant first; an overflow is dropped). -/
def inc : List Bool → List Bool
  | [] => []
  | true :: u => false :: inc u
  | false :: u => true :: u

/-- Binary decrement of a fixed-width bit list (least significant first). -/
def dec : List Bool → List Bool
  | [] => []
  | false :: v => true :: dec v
  | true :: v => false :: v

/-- The value of a bit list, least significant first. -/
def val : List Bool → Nat
  | [] => 0
  | b :: u => (if b then 1 else 0) + 2 * val u

/-- The two headers of the run: `0110101` and `0110111`. -/
def hdr0 : List Bool := [false, true, true, false, true, false, true]
def hdr1 : List Bool := [false, true, true, false, true, true, true]

/-- `f` applied `n` times. -/
def itr (f : List Bool → List Bool) : Nat → List Bool → List Bool
  | 0, x => x
  | n + 1, x => itr f n (f x)

theorem itr_succ' (f : List Bool → List Bool) : ∀ n x, itr f (n + 1) x = f (itr f n x)
  | 0, _ => rfl
  | n + 1, x => by rw [itr, itr_succ' f n (f x)]; rfl

/-- The tick configuration `L U 00 D> H V R`. -/
def tcfg (H u v : List Bool) (L R : Tape) : Config :=
  ⟨cons false (cons false (encU u L)), app H (encV v R), .D⟩

theorem encU_rep_true (j : Nat) (u : List Bool) (L : Tape) :
    encU (List.replicate j true ++ u) L = rep j [true, false, false, false, false] (encU u L) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, encU, dU, ih]

theorem encU_rep_false (j : Nat) (u : List Bool) (L : Tape) :
    encU (List.replicate j false ++ u) L = rep j [false, false, false, false, false] (encU u L) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, encU, dU, ih]

theorem encV_rep_false (i : Nat) (v : List Bool) (R : Tape) :
    encV (List.replicate i false ++ v) R = rep i [true, true] (encV v R) := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, encV, dV, ih]

theorem encV_rep_true (i : Nat) (v : List Bool) (R : Tape) :
    encV (List.replicate i true ++ v) R = rep i [false, true] (encV v R) := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, encV, dV, ih]

/-- A list with a `false` is `1^j 0 u'`, and its increment is `0^j 1 u'`. -/
theorem split_inc : ∀ u : List Bool, false ∈ u →
    ∃ j u', u = List.replicate j true ++ false :: u' ∧ inc u = List.replicate j false ++ true :: u'
  | [], h => by simp at h
  | false :: u, _ => ⟨0, u, rfl, rfl⟩
  | true :: u, h => by
    have h' : false ∈ u := by simpa using h
    obtain ⟨j, u', e1, e2⟩ := split_inc u h'
    exact ⟨j + 1, u', by simp [e1, List.replicate_succ], by simp [inc, e2, List.replicate_succ]⟩

/-- A list with a `true` is `0^i 1 v'`, and its decrement is `1^i 0 v'`. -/
theorem split_dec : ∀ v : List Bool, true ∈ v →
    ∃ i v', v = List.replicate i false ++ true :: v' ∧ dec v = List.replicate i true ++ false :: v'
  | [], h => by simp at h
  | true :: v, _ => ⟨0, v, rfl, rfl⟩
  | false :: v, h => by
    have h' : true ∈ v := by simpa using h
    obtain ⟨i, v', e1, e2⟩ := split_dec v h'
    exact ⟨i + 1, v', by simp [e1, List.replicate_succ], by simp [dec, e2, List.replicate_succ]⟩

/-- One tick on the bit lists, for either header. -/
theorem tick (H : List Bool) (hH : H = hdr0 ∨ H = hdr1) (u v : List Bool) (hu : false ∈ u) (hv : true ∈ v)
    (L R : Tape) : ∃ s, steps s (tcfg H u v L R) = some (tcfg H (inc u) (dec v) L R) := by
  obtain ⟨j, u', rfl, hi⟩ := split_inc u hu
  obtain ⟨i, v', rfl, hd⟩ := split_dec v hv
  rw [hi, hd]
  simp only [tcfg, encU_rep_true, encU_rep_false, encV_rep_false, encV_rep_true]
  cases i with
  | zero =>
    rcases hH with rfl | rfl
    · refine ⟨10 * j + 34, ?_⟩
      simpa [encU, encV, dU, dV, rep, hdr0, app] using tick0_odd j (encU u' L) (encV v' R)
    · refine ⟨10 * j + 34, ?_⟩
      simpa [encU, encV, dU, dV, rep, hdr1, app] using tick1_odd j (encU u' L) (encV v' R)
  | succ i =>
    rcases hH with rfl | rfl
    · refine ⟨8 * i + 10 * j + 42, ?_⟩
      have h := tick0_even i j (encU u' L) (encV v' R)
      rw [← rep_app_comm i [false, true]]
      simpa [encU, encV, dU, dV, rep, hdr0, app] using h
    · refine ⟨8 * i + 10 * j + 42, ?_⟩
      have h := tick1_even i j (encU u' L) (encV v' R)
      rw [← rep_app_comm i [false, true]]
      simpa [encU, encV, dU, dV, rep, hdr1, app] using h

/-- A run of `k` ticks, as long as U does not overflow and V does not reach 0 before the last of them. -/
theorem ticks (H : List Bool) (hH : H = hdr0 ∨ H = hdr1) (L R : Tape) :
    ∀ (k : Nat) (u v : List Bool), (∀ m < k, false ∈ itr inc m u ∧ true ∈ itr dec m v) →
      ∃ s, steps s (tcfg H u v L R) = some (tcfg H (itr inc k u) (itr dec k v) L R)
  | 0, u, v, _ => ⟨0, rfl⟩
  | k + 1, u, v, h => by
    obtain ⟨s₁, h₁⟩ := tick H hH u v (h 0 (by omega)).1 (h 0 (by omega)).2 L R
    obtain ⟨s₂, h₂⟩ := ticks H hH L R k (inc u) (dec v) (fun m hm => by
      have := h (m + 1) (by omega)
      simpa [itr] using this)
    exact ⟨s₁ + s₂, steps_seq trans h₁ (by simpa [itr] using h₂)⟩

/-! ## The same in numbers -/

theorem length_inc : ∀ u : List Bool, (inc u).length = u.length
  | [] => rfl
  | true :: u => by simp [inc, length_inc u]
  | false :: u => rfl

theorem length_dec : ∀ v : List Bool, (dec v).length = v.length
  | [] => rfl
  | false :: v => by simp [dec, length_dec v]
  | true :: v => rfl

theorem val_lt : ∀ u : List Bool, val u < 2 ^ u.length
  | [] => by simp [val]
  | b :: u => by
    have := val_lt u
    cases b <;> simp [val, Nat.pow_succ] <;> omega

theorem mem_false_of_lt : ∀ u : List Bool, val u + 1 < 2 ^ u.length → false ∈ u
  | [], h => by simp [val] at h
  | false :: _, _ => by simp
  | true :: u, h => by
    have : val u + 1 < 2 ^ u.length := by simp [val, Nat.pow_succ] at h; omega
    simp [mem_false_of_lt u this]

theorem mem_true_of_pos : ∀ v : List Bool, 0 < val v → true ∈ v
  | [], h => by simp [val] at h
  | true :: _, _ => by simp
  | false :: v, h => by
    have : 0 < val v := by simp [val] at h; omega
    simp [mem_true_of_pos v this]

theorem val_inc : ∀ u : List Bool, false ∈ u → val (inc u) = val u + 1
  | [], h => by simp at h
  | false :: _, _ => by simp [inc, val]; omega
  | true :: u, h => by
    have h' : false ∈ u := by simpa using h
    simp [inc, val, val_inc u h']; omega

theorem val_dec : ∀ v : List Bool, true ∈ v → val (dec v) + 1 = val v
  | [], h => by simp at h
  | true :: _, _ => by simp [dec, val]; omega
  | false :: v, h => by
    have h' : true ∈ v := by simpa using h
    have := val_dec v h'
    simp [dec, val]; omega

theorem iter_inc (u : List Bool) : ∀ m, val u + m < 2 ^ u.length →
    val (itr inc m u) = val u + m ∧ (itr inc m u).length = u.length
  | 0, _ => by simp [itr]
  | m + 1, h => by
    obtain ⟨h1, h2⟩ := iter_inc u m (by omega)
    rw [itr_succ']
    have hf : false ∈ itr inc m u := mem_false_of_lt _ (by rw [h1, h2]; omega)
    exact ⟨by rw [val_inc _ hf, h1]; omega, by rw [length_inc, h2]⟩

theorem iter_dec (v : List Bool) : ∀ m, m ≤ val v → val (itr dec m v) + m = val v ∧ (itr dec m v).length = v.length
  | 0, _ => by simp [itr]
  | m + 1, h => by
    obtain ⟨h1, h2⟩ := iter_dec v m (by omega)
    rw [itr_succ']
    have ht : true ∈ itr dec m v := mem_true_of_pos _ (by omega)
    have := val_dec _ ht
    exact ⟨by omega, by rw [length_dec, h2]⟩

/-- **A phase of ticks.** From the tick configuration with up-counter `u` (width `u.length`) and down-counter `v`,
for every `k ≤ val v` with `val u + k < 2 ^ u.length`, the machine reaches the tick configuration whose counters
have the same widths and the values `val u + k` and `val v - k`; nothing beyond the counters is read. -/
theorem phase (H : List Bool) (hH : H = hdr0 ∨ H = hdr1) (u v : List Bool) (L R : Tape) (k : Nat)
    (hk : k ≤ val v) (hu : val u + k < 2 ^ u.length) :
    ∃ u' v' s, steps s (tcfg H u v L R) = some (tcfg H u' v' L R) ∧
      u'.length = u.length ∧ v'.length = v.length ∧ val u' = val u + k ∧ val v' + k = val v := by
  obtain ⟨s, hs⟩ := ticks H hH L R k u v (fun m hm => by
    obtain ⟨a1, a2⟩ := iter_inc u m (by omega)
    obtain ⟨b1, b2⟩ := iter_dec v m (by omega)
    exact ⟨mem_false_of_lt _ (by rw [a1, a2]; omega), mem_true_of_pos _ (by omega)⟩)
  obtain ⟨a1, a2⟩ := iter_inc u k hu
  obtain ⟨b1, b2⟩ := iter_dec v k hk
  exact ⟨_, _, s, hs, a2, b2, a1, b1⟩

/-- In particular a whole phase: V runs down to 0 (all digits `11`) when U has room for it. -/
theorem phase_to_zero (H : List Bool) (hH : H = hdr0 ∨ H = hdr1) (u v : List Bool) (L R : Tape)
    (hu : val u + val v < 2 ^ u.length) :
    ∃ u' s, steps s (tcfg H u v L R) = some (tcfg H u' (List.replicate v.length false) L R) ∧
      u'.length = u.length ∧ val u' = val u + val v := by
  obtain ⟨u', v', s, hs, h1, h2, h3, h4⟩ := phase H hH u v L R (val v) (Nat.le_refl _) hu
  have hz : v' = List.replicate v.length false := by
    have hv0 : val v' = 0 := by omega
    rw [← h2]
    clear hs h2 h4
    induction v' with
    | nil => rfl
    | cons b w ih =>
      cases b
      · simp [val] at hv0
        rw [List.length_cons, List.replicate_succ, ← ih (by omega)]
      · simp [val] at hv0
  exact ⟨u', s, hz ▸ hs, h1, h3⟩

end H49767
