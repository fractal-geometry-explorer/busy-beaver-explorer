import Rle

/-!
# The first nested run, by direct simulation

At sweep 5,391 (step 115,650,647) the carry of the counter reaches the leftmost block `1^12`, whose length is
even, and the machine starts a nested run of inner sweeps that the sweep rules do not cover.  Here that one run is
checked cell by cell: the list simulator of `tools/lean/TM/Fin.lean` (proved to agree with `steps`) is evaluated by
compiled code (`native_decide`) for the 115,676,475 steps of the run, and its end configuration is compared with the
sweep configuration `1^15 | 2 0 0 1 1 1 1 1 1 0 2 1^2686 | 0 1^4 B>0` (the right end in its other phase).  Trailing
blank cells of the lists are dropped before the comparison (`trim`, `app_trim`).
-/

namespace H115779

open TM

/-- The tape left of the head for digits `ds` after the list `l`, as a list (nearest cell first). -/
def encL : List Nat → List Bool → List Bool
  | [], l => l
  | d :: ds, l => encL ds (ones (3 * d + 2) ++ false :: l)

theorem enc_encL : ∀ (ds : List Nat) (l : List Bool), enc ds (app l blank) = app (encL ds l) blank
  | [], _ => rfl
  | d :: ds, l => by
    show enc ds (app (ones (3 * d + 2)) (cons false (app l blank))) = _
    rw [show cons false (app l blank) = app (false :: l) blank from rfl, app_app, enc_encL ds]; rfl

/-- Drop the trailing `false`s of a list. -/
def trim : List Bool → List Bool
  | [] => []
  | x :: w => if trim w = [] ∧ x = false then [] else x :: trim w

theorem app_trim : ∀ w : List Bool, app (trim w) blank = app w blank
  | [] => rfl
  | x :: w => by
    unfold trim
    split
    · rename_i h
      obtain ⟨h1, h2⟩ := h
      subst h2
      rw [app_cons, ← app_trim w, h1]
      exact cons_false_blank.symm
    · rw [app_cons, app_cons, app_trim w]

theorem toCfg_trim {c c' : FCfg St} (h : (trim c.l, trim c.r, c.st) = (trim c'.l, trim c'.r, c'.st)) :
    c.toCfg = c'.toCfg := by
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  show (⟨app c.l blank, app c.r blank, c.st⟩ : Config) = ⟨app c'.l blank, app c'.r blank, c'.st⟩
  rw [← app_trim c.l, ← app_trim c.r, ← app_trim c'.l, ← app_trim c'.r, h1, h2, h3]

theorem P_toCfg (r : Nat) (ds : List Nat) :
    (⟨true :: false :: encL ds (ones r), [], .B⟩ : FCfg St).toCfg = P (raw r) ds := by
  show (⟨app (true :: false :: encL ds (ones r)) blank, app [] blank, .B⟩ : Config) = _
  rw [P, raw, enc_encL]; rfl

theorem Q_toCfg (r : Nat) (ds : List Nat) :
    (⟨[true, true, true, true, false] ++ encL ds (ones r), [], .B⟩ : FCfg St).toCfg = Q (raw r) ds := by
  show (⟨app ([true, true, true, true, false] ++ encL ds (ones r)) blank, app [] blank, .B⟩ : Config) = _
  rw [Q, raw, enc_encL, ← app_app]; rfl

/-- The digits where the first nested run starts and where it ends. -/
def dsA : List Nat := [1, 3, 1, 1, 1, 1, 1, 3] ++ List.replicate 2686 1
def dsB : List Nat := [2, 0, 0, 1, 1, 1, 1, 1, 1, 0, 2] ++ List.replicate 2686 1

theorem nested_eval :
    (TM.fsteps trans 115676475 ⟨true :: false :: encL dsA (ones 12), [], .B⟩).map
        (fun c => (trim c.l, trim c.r, c.st)) =
      some (trim ([true, true, true, true, false] ++ encL dsB (ones 15)), trim [], St.B) := by
  native_decide

/-- **The first nested run**: from `1^12 | 1 3 1^5 3 1^2686 | 0 1 B>0` the machine reaches
`1^15 | 2 0 0 1^6 0 2 1^2686 | 0 1^4 B>0` in 115,676,475 steps. -/
theorem nested_run : steps 115676475 (P (raw 12) dsA) = some (Q (raw 15) dsB) := by
  have h := nested_eval
  cases e : TM.fsteps trans 115676475 ⟨true :: false :: encL dsA (ones 12), [], .B⟩ with
  | none => rw [e] at h; cases h
  | some c =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have h2 := FCfg.steps_eq trans 115676475 ⟨true :: false :: encL dsA (ones 12), [], .B⟩
    rw [e, P_toCfg] at h2
    change TM.steps trans 115676475 (P (raw 12) dsA) = _
    rw [h2, ← Q_toCfg]
    simp only [Option.map_some, Option.some.injEq]
    exact toCfg_trim (c' := ⟨[true, true, true, true, false] ++ encL dsB (ones 15), [], .B⟩) h

end H115779
