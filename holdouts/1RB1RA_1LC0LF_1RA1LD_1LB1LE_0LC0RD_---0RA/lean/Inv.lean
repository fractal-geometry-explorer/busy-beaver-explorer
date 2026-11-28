import Sim

namespace H129887

open TM

/-- Every frame of the list has at least one 1 and at least one 0. -/
def FOk (fs : List (Nat × Nat)) : Prop := ∀ f ∈ fs, 1 ≤ f.1 ∧ 1 ≤ f.2

/-- The states the run passes through: frames with ones and zeros (in `Z` the top frame may have run out of
zeros), and a call with at least one 1. -/
def Inv : MS → Prop
  | ⟨fs, .ret _ _ _⟩ => FOk fs
  | ⟨fs, .call m _⟩ => FOk fs ∧ 1 ≤ m
  | ⟨[], .z _ _⟩ => True
  | ⟨f :: fs, .z _ _⟩ => 1 ≤ f.1 ∧ FOk fs

theorem fok_nil : FOk [] := by intro f h; cases h

theorem fok_cons {n z : Nat} {r : List (Nat × Nat)} (h1 : 1 ≤ n) (h2 : 1 ≤ z) (hr : FOk r) : FOk ((n, z) :: r) := by
  intro f hf
  cases hf with
  | head => exact ⟨h1, h2⟩
  | tail _ h => exact hr f h

theorem fok_head {n z : Nat} {r : List (Nat × Nat)} (h : FOk ((n, z) :: r)) : 1 ≤ n ∧ 1 ≤ z :=
  h (n, z) (List.Mem.head _)

theorem fok_tail {f} {r : List (Nat × Nat)} (h : FOk (f :: r)) : FOk r :=
  fun g hg => h g (List.Mem.tail _ hg)

theorem fok_push (n z : Nat) (fs : List (Nat × Nat)) (hz : 1 ≤ z) (h : FOk fs) : FOk (push n z fs) := by
  cases n with
  | zero =>
    cases fs with
    | nil => exact fok_nil
    | cons f r =>
      obtain ⟨n', z'⟩ := f
      have := fok_head h
      exact fok_cons this.1 (by omega) (fok_tail h)
  | succ n => exact fok_cons (by omega) hz h

theorem lead_shape (w : List Bool) : (lead w).2 = [] ∨ ∃ X, (lead w).2 = false :: X := by
  induction w with
  | nil => exact Or.inl rfl
  | cons x w ih =>
    cases x with
    | false => exact Or.inr ⟨w, rfl⟩
    | true => exact ih

theorem lead_cons_true (w : List Bool) : lead (true :: w) = ((lead w).1 + 1, (lead w).2) := rfl

theorem inv_zcall (fs : List (Nat × Nat)) (m : Nat) (X : List Bool) (hm : 1 ≤ m)
    (h : Inv ⟨fs, .z true []⟩) : Inv (zcall fs m X) := by
  match fs, h with
  | [], _ => exact ⟨fok_nil, hm⟩
  | (n, 0) :: r, h => exact ⟨h.2, by omega⟩
  | (n, z + 1) :: r, h => exact ⟨fok_cons h.1 (by omega) h.2, hm⟩

/-- One transition from a state of the run: the model halts, or it moves on to a state of the run, by at least one
step of the machine.  In particular it never gets stuck. -/
theorem inv_step (s : MS) (hs : Inv s) :
    mstep s = .halt ∨ ∃ s' k, mstep s = .next s' k ∧ Inv s' ∧ 1 ≤ k := by
  obtain ⟨fs, mode⟩ := s
  cases mode with
  | ret p x w =>
    have hf : FOk fs := hs
    match p, fs, hf with
    | p + 3, fs, hf => exact Or.inr ⟨⟨fs, .ret p false (x :: w)⟩, 5, by cases fs <;> rfl, hf, by omega⟩
    | 2, [], _ => exact Or.inr ⟨_, _, rfl, trivial, by omega⟩
    | 2, (n, 0) :: r, hf => exact absurd (fok_head hf).2 (by omega)
    | 2, (n, z + 1) :: r, hf => exact Or.inr ⟨_, _, rfl, ⟨(fok_head hf).1, fok_tail hf⟩, by omega⟩
    | 1, [], _ => exact Or.inr ⟨_, _, rfl, trivial, by omega⟩
    | 1, (n, 0) :: r, hf => exact absurd (fok_head hf).2 (by omega)
    | 1, (0, 1) :: r, hf => exact absurd (fok_head hf).1 (by omega)
    | 1, (n + 1, 1) :: r, hf => exact Or.inr ⟨_, _, rfl, fok_tail hf, by omega⟩
    | 1, (n, z + 2) :: r, hf => exact Or.inr ⟨_, _, rfl, ⟨(fok_head hf).1, fok_tail hf⟩, by omega⟩
    | 0, [], _ => exact Or.inr ⟨_, _, rfl, trivial, by omega⟩
    | 0, (n, 0) :: r, hf => exact absurd (fok_head hf).2 (by omega)
    | 0, (0, z + 1) :: r, hf => exact absurd (fok_head hf).1 (by omega)
    | 0, (n + 1, z + 3) :: r, hf => exact Or.inr ⟨_, _, rfl, ⟨(fok_head hf).1, fok_tail hf⟩, by omega⟩
    | 0, (n + 1, 2) :: r, hf => exact Or.inr ⟨_, _, rfl, fok_tail hf, by omega⟩
    | 0, (n + 2, 1) :: r, hf =>
      exact Or.inr ⟨_, _, rfl, ⟨fok_push n 1 r (by omega) (fok_tail hf), by omega⟩, by omega⟩
    | 0, [(1, 1)], _ => exact Or.inl rfl
    | 0, (1, 1) :: (n', 0) :: r, hf => exact absurd (fok_head (fok_tail hf)).2 (by omega)
    | 0, (1, 1) :: (n', z' + 1) :: r, _ => exact Or.inl rfl
  | z x w =>
    have hz : Inv ⟨fs, .z true []⟩ := by cases fs <;> exact hs
    have e : mstep ⟨fs, .z x w⟩ = match lead (x :: w) with
        | (a, false :: X) => .next (zcall fs (3 * a + 2) X) (3 * a + 2)
        | (a + 1, []) => .next (zcall fs (3 * a + 3) []) (3 * a + 3)
        | _ => .stuck := by
      cases fs <;> rfl
    rw [e]
    cases x with
    | false => exact Or.inr ⟨_, _, rfl, inv_zcall fs _ _ (by omega) hz, by omega⟩
    | true =>
      rw [lead_cons_true]
      rcases lead_shape w with h | ⟨X, h⟩
      · rw [h]; exact Or.inr ⟨_, _, rfl, inv_zcall fs _ _ (by omega) hz, by omega⟩
      · rw [h]; exact Or.inr ⟨_, _, rfl, inv_zcall fs _ _ (by omega) hz, by omega⟩
  | call m X =>
    obtain ⟨hf, hm⟩ := hs
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e : mstep ⟨fs, .call (m + 1) X⟩ = match lead X with
        | (j, false :: Y) => .next ⟨push m (3 * j + 2) fs, .ret 0 true Y⟩ (9 * j + 7)
        | (0, []) => .next ⟨fs, .ret m true []⟩ 1
        | (j + 1, []) => .next ⟨push m (3 * (j + 1)) fs, .ret 0 true []⟩ (9 * (j + 1) + 1)
        | _ => .stuck := by
      cases fs <;> rfl
    rw [e]
    rcases lead_shape X with h | ⟨Y, h⟩
    · rcases hl : lead X with ⟨j, L⟩
      rw [hl] at h; simp only at h; subst h
      cases j with
      | zero => exact Or.inr ⟨_, _, rfl, hf, by omega⟩
      | succ j => exact Or.inr ⟨_, _, rfl, fok_push m _ fs (by omega) hf, by omega⟩
    · rcases hl : lead X with ⟨j, L⟩
      rw [hl] at h; simp only at h; subst h
      exact Or.inr ⟨_, _, rfl, fok_push m _ fs (by omega) hf, by omega⟩


theorem inv_start : Inv start := fok_nil

/-- One more transition at the end of a run of the model. -/
theorem mrun_snoc (n : Nat) (s : MS) (k : Nat) (s' : MS) (K : Nat) (h : mrun n s k = some (s', K))
    (s'' : MS) (d : Nat) (h' : mstep s' = .next s'' d) : mrun (n + 1) s k = some (s'', K + d) := by
  induction n generalizing s k with
  | zero =>
    simp only [mrun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    simp only [mrun, h']
  | succ n ih =>
    unfold mrun at h
    split at h
    · rename_i s1 d1 hs
      have := ih s1 (k + d1) h
      show (match mstep s with | .next s' d => mrun (n + 1) s' (k + d) | _ => none) = _
      rw [hs]; exact this
    · cases h

/-- The model halts from blank tape: some run of it from `start` ends in a state whose transition is the halt. -/
def ModelHalts : Prop := ∃ n s K, mrun n start 2 = some (s, K) ∧ mstep s = .halt

/-- If the model does not halt, it runs `n` transitions for every `n`, through states of the run, counting at least
`n` steps. -/
theorem mrun_total (hn : ¬ ModelHalts) (n : Nat) : ∃ s K, mrun n start 2 = some (s, K) ∧ Inv s ∧ n ≤ K := by
  induction n with
  | zero => exact ⟨start, 2, rfl, inv_start, by omega⟩
  | succ n ih =>
    obtain ⟨s, K, h, hi, hK⟩ := ih
    rcases inv_step s hi with hh | ⟨s', d, hs, hi', hd⟩
    · exact absurd ⟨n, s, K, h, hh⟩ hn
    · exact ⟨s', K + d, mrun_snoc n start 2 s K h s' d hs, hi', by omega⟩

/-- **The machine halts from blank tape exactly when the model does.**  The model never gets stuck on the states of
the run (`inv_step`), so it either halts or runs forever, and each transition is at least one step of the machine. -/
theorem halts_iff_model : HaltsFromBlank ↔ ModelHalts := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hn => ?_
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun m => ∃ n s, mrun n start 2 = some (s, m))
    · intro n
      obtain ⟨s, K, h, _, hK⟩ := mrun_total hn n
      exact ⟨K, hK, n, s, h⟩
    · rintro m ⟨n, s, h⟩
      exact blank_runs_of_mrun n m (by rw [h]; rfl)
  · rintro ⟨n, s, K, h, hh⟩
    obtain ⟨d, hK, hd⟩ := mrun_sound n start 2 s K h
    obtain ⟨c, hc, hstop⟩ := mstep_halt s hh
    exact ⟨2 + d + 3, c, steps_seq trans (steps_seq trans blank_to_model hd) hc, hstop⟩

end H129887
