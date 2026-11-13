import Machine
import Window
import Pass
import Data

/-!
# The bouncer phase: one period, for every number of blocks

From step 16,730,681,219 on (observed: `py/dumpT.c`), the run is an exact bouncer. At each period start the head is
in state A on the left end of the tape

    C k = 0^inf A> 0 (1010001000100)^k X 0^inf

with X the fixed stretch of 222,182 cells in `Data.lean`. One period (two sweeps) takes C (n+1) to C (n+2) in
184 n + 3,029,224 steps (`period`): the blocks are crossed by the symbolic passes of `Pass.lean` (kernel), the
two excursions into X by evaluation on a finite window (`Window.lean`, `native_decide`), which never looks at
the blocks on its left. So once some C k with k ≥ 1 is reached the machine never halts (`nonhalt_of_reach`).
-/

namespace H32641

open TM

/-- The block, left to right. -/
def accb : List Bool := [true, false, true, false, false, false, true, false, false, false, true, false, false]

/-- The configuration at the start of a period. -/
def C (k : Nat) : Config := ⟨blank, cons false (rep k accb (app X blank)), .A⟩

/-- The first excursion into X. -/
@[irreducible] def W1 : Option (FCfg St) := wsteps 1517479 ⟨[true], X, .B⟩

/-- What the first excursion leaves right of the head (after its first cell). -/
@[irreducible] def r1t : List Bool := match W1 with
  | some c => c.r.tail
  | none => []

/-- The second excursion. -/
@[irreducible] def W2 : Option (FCfg St) := wsteps 1511551 ⟨[true, true, false], r1t, .B⟩

@[irreducible] def r2t : List Bool := match W2 with
  | some c => c.r.tail
  | none => []

/-- The first excursion stays in the window and comes back in state E onto a 0. -/
theorem w1_ok : wsteps 1517479 ⟨[true], X, .B⟩ = some ⟨[], false :: r1t, .E⟩ := by native_decide

theorem w2_ok : wsteps 1511551 ⟨[true, true, false], r1t, .B⟩ = some ⟨[], false :: r2t, .E⟩ := by native_decide

/-- After the second excursion the stretch is X again, one block further on. -/
theorem close : [true, false] ++ r2t = accb ++ X := by native_decide

/-- **One period**: `C (n+1)` reaches `C (n+2)` in `184 n + 3029224` steps. -/
theorem period (n : Nat) : steps (184 * n + 3029224) (C (n + 1)) = some (C (n + 2)) := by
  have h1 := pass1 n (app X blank)
  have hw1 : steps 1517479
      ⟨cons true (rep (n + 1) [true, false, false, false, true, false, false, true, false, true, false, true, false]
        blank), app X blank, .B⟩ =
      some ⟨rep (n + 1) [true, false, false, false, true, false, false, true, false, true, false, true, false] blank,
        cons false (app r1t blank), .E⟩ :=
    wsteps_over1 w1_ok _
  have h2 := pass2 n (app r1t blank)
  have hw2 : steps 1511551
      ⟨cons true (cons true (cons false (rep (n + 1)
        [true, false, false, false, true, false, false, true, false, true, false, true, false] blank))),
        app r1t blank, .B⟩ =
      some ⟨rep (n + 1) [true, false, false, false, true, false, false, true, false, true, false, true, false] blank,
        cons false (app r2t blank), .E⟩ :=
    wsteps_over3 w2_ok _
  have h3 := pass3 n (app r2t blank)
  have e : cons true (cons false (rep (n + 1)
      [true, false, false, false, true, false, false, false, true, false, false, true, false] (app r2t blank))) =
      rep (n + 2) accb (app X blank) := by
    have hr := rep_rotate (n + 1) [true, false]
      [true, false, false, false, true, false, false, false, true, false, false, true, false] accb rfl
      (app r2t blank)
    have hx : app [true, false] (app r2t blank) = app accb (app X blank) := by
      rw [app_app, close, ← app_app]
    rw [hx, rep_app_comm] at hr
    exact hr
  rw [e] at h3
  exact steps_congr trans (by omega)
    (steps_seq trans h1 (steps_seq trans hw1 (steps_seq trans h2 (steps_seq trans hw2 h3))))

/-- From any `C (m+1)` the run goes on for ever. -/
theorem runs_C : ∀ j m, ∃ t, j ≤ t ∧ ∃ c, steps t (C (m + 1)) = some c := by
  intro j
  induction j with
  | zero => intro m; exact ⟨0, Nat.le_refl 0, _, rfl⟩
  | succ j ih =>
    intro m
    obtain ⟨t, hj, c, hc⟩ := ih (m + 1)
    exact ⟨184 * m + 3029224 + t, by omega, c, steps_seq trans (period m) hc⟩

theorem not_halts_C (m : Nat) : ¬ Halts trans (C (m + 1)) := by
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun t => ∃ c, steps t (C (m + 1)) = some c)
  · intro n
    obtain ⟨t, h, c, hc⟩ := runs_C n m
    exact ⟨t, h, c, hc⟩
  · intro t h; exact h

/-- **Reduction**: if the run from blank tape reaches some `C (m+1)`, the machine never halts. -/
theorem nonhalt_of_reach {t m : Nat} (h : steps t init = some (C (m + 1))) : ¬ HaltsFromBlank := by
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun n => t ≤ n)
  · intro n; exact ⟨n + t, by omega, by omega⟩
  · intro n hn
    obtain ⟨k, hk⟩ : ∃ k, n = t + k := ⟨n - t, by omega⟩
    subst hk
    have hall := forall_of_unbounded trans (c := C (m + 1)) (fun t => ∃ c, steps t (C (m + 1)) = some c)
      (fun n => by obtain ⟨t, h, c, hc⟩ := runs_C n m; exact ⟨t, h, c, hc⟩) (fun _ h => h) k
    obtain ⟨c, hc⟩ := hall
    exact ⟨c, steps_seq trans h hc⟩

end H32641
