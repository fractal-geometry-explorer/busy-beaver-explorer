import Steps

/-!
# 1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC: only a B-overflow can lead to a halt

From blank tape the run reaches a steady visit (`start`, visit 280 at step 1,882,602, by `native_decide`).  From a
steady visit that is not a B-overflow the run reaches another steady visit (`steady_step`, Steps.lean: shallow
visits, deep visits, A-overflows, for every counter value, width and block length).  So:

* `halt_needs_B_overflow`: if the machine halts from blank tape, the run first reaches a steady visit that is a
  B-overflow (`BStart`); `halt_needs_later_B_overflow`: one after step 31,879,658, since the run through the first
  B-overflow transient to visit 2688 is evaluated as well (`second_eval`, `native_decide`);
* `nonhalting_of_transients`: if every B-overflow visit leads to a steady visit again, the machine never halts.
-/

namespace H154101

open TM

/-- The list form of a phase-A visit, for the evaluation of the start-up. -/
def visL (m : Nat) (b0 : Bool) (ds : List Bool) (t i0 i1 i2 : Bool) : List Bool :=
  [false, true] ++ (List.replicate m [true, true, false, true]).flatten ++ Irev i0 i1 i2 ++ Mrev t ++ [true, false, b0]
    ++ ds.flatMap Ur

theorem app_flatten_rep (m : Nat) (w : List Bool) (s : Tape) :
    app (List.replicate m w).flatten s = rep m w s := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.flatten_cons, ← app_app, ih, rep_succ]

theorem app_flatMap_digs (ds : List Bool) (s : Tape) : app (ds.flatMap Ur) s = digs ds s := by
  induction ds with
  | nil => rfl
  | cons b ds ih => rw [List.flatMap_cons, ← app_app, ih, digs_cons]

theorem visL_toCfg (m : Nat) (b0 : Bool) (ds : List Bool) (t i0 i1 i2 : Bool) :
    (FCfg.mk (visL m b0 ds t i0 i1 i2) [] St.C).toCfg = vis m (Xv blank b0 ds t i0 i1 i2) := by
  simp only [FCfg.toCfg, visL, vis, Xv, ← app_app, app_flatten_rep, app_flatMap_digs, app_cons, app_nil]

/-- Visit 280, step 1,882,602: phase A, 13 digits, V = 4380, t = 0, i = 0, a block of 267 copies. -/
theorem start_eval : fsteps 1882602 (FCfg.blank St.A) = some (FCfg.mk
    (visL 267 false [false, true, true, true, false, false, false, true, false, false, false, true] false false false
      false) [] St.C) := by
  native_decide

theorem start : ∃ j c, steps j init = some c ∧ Steady c := by
  refine ⟨1882602, _, blank_reaches trans start_eval, ?_⟩
  rw [visL_toCfg]
  exact steady_mk (Or.inl rfl) (by decide) (by decide)

/-- From a steady visit at step `j0`, every length of run is reached by a steady visit, unless a B-overflow comes
first. -/
theorem reach_from {j0 : Nat} {c0 : Config} (h0 : steps j0 init = some c0) (hs0 : Steady c0) (n : Nat) :
    ∃ j c, steps j init = some c ∧ Steady c ∧ j0 ≤ j ∧ (n ≤ j ∨ BStart c) := by
  induction n with
  | zero => exact ⟨j0, c0, h0, hs0, Nat.le_refl _, Or.inl (Nat.zero_le _)⟩
  | succ n ih =>
    obtain ⟨j, c, h, hs, hj0, hj | hb⟩ := ih
    · rcases Classical.em (BStart c) with hb | hb
      · exact ⟨j, c, h, hs, hj0, Or.inr hb⟩
      · obtain ⟨n', c', h', hs'⟩ := steady_step hs hb
        exact ⟨j + (n' + 1), c', steps_seq trans h h', hs', by omega, Or.inl (by omega)⟩
    · exact ⟨j, c, h, hs, hj0, Or.inr hb⟩

theorem not_none_of_some {a b : Nat} {c : Config} (h : steps a init = some c) (hab : b ≤ a) :
    ∃ c', steps b init = some c' := by
  have e : a = b + (a - b) := by omega
  rw [e] at h
  exact steps_le trans h

theorem halt_needs_B_overflow_from {j0 : Nat} {c0 : Config} (h0 : steps j0 init = some c0) (hs0 : Steady c0)
    (h : HaltsFromBlank) : ∃ j c, steps j init = some c ∧ Steady c ∧ BStart c ∧ j0 ≤ j := by
  obtain ⟨n, c', h1, h2⟩ := h
  have hn : steps (n + (0 + 1)) init = none := steps_halt trans h1 h2 0
  obtain ⟨j, c, hj, hs, hj0, hj' | hb⟩ := reach_from h0 hs0 (n + 1)
  · obtain ⟨c'', h''⟩ := not_none_of_some hj hj'
    rw [hn] at h''
    cases h''
  · exact ⟨j, c, hj, hs, hb, hj0⟩

/-- A halt from blank tape is preceded by a steady visit that is a B-overflow. -/
theorem halt_needs_B_overflow (h : HaltsFromBlank) : ∃ j c, steps j init = some c ∧ Steady c ∧ BStart c := by
  obtain ⟨j0, c0, h0, hs0⟩ := start
  obtain ⟨j, c, hj, hs, hb, _⟩ := halt_needs_B_overflow_from h0 hs0 h
  exact ⟨j, c, hj, hs, hb⟩

/-- Visit 2688, step 31,879,658, after the first B-overflow transient (visits 2656-2687): phase A, 14 digits,
V = 8395, t = 0, i = 1, a block of 2675 copies. -/
theorem second_eval : fsteps 31879658 (FCfg.blank St.A) = some (FCfg.mk
    (visL 2675 true [true, false, true, false, false, true, true, false, false, false, false, false, true] false true
      false false) [] St.C) := by
  native_decide

/-- The first B-overflow is passed: a halt needs a B-overflow after step 31,879,658 (the next one is at visit 7502,
step 230,416,382 or so). -/
theorem halt_needs_later_B_overflow (h : HaltsFromBlank) :
    ∃ j c, steps j init = some c ∧ Steady c ∧ BStart c ∧ 31879658 ≤ j := by
  have h0 := blank_reaches trans second_eval
  rw [visL_toCfg] at h0
  exact halt_needs_B_overflow_from h0 (steady_mk (Or.inl rfl) (by decide) (by decide)) h

/-- If every B-overflow leads to a steady visit again, the machine never halts from blank tape. -/
theorem nonhalting_of_transients
    (H : ∀ c, Steady c → BStart c → ∃ n c', steps (n + 1) c = some c' ∧ Steady c') : ¬ HaltsFromBlank := by
  have r : ∀ n, ∃ j c, steps j init = some c ∧ Steady c ∧ n ≤ j := by
    intro n
    induction n with
    | zero =>
      obtain ⟨j, c, h, hs⟩ := start
      exact ⟨j, c, h, hs, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨j, c, h, hs, hj⟩ := ih
      have step : ∃ n' c', steps (n' + 1) c = some c' ∧ Steady c' := by
        rcases Classical.em (BStart c) with hb | hb
        · exact H c hs hb
        · exact steady_step hs hb
      obtain ⟨n', c', h', hs'⟩ := step
      exact ⟨j + (n' + 1), c', steps_seq trans h h', hs', by omega⟩
  apply not_halts_of_forall trans
  intro n
  obtain ⟨j, c, h, _, hj⟩ := r n
  exact not_none_of_some h hj

end H154101
