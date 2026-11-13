import Rules
import TM.Fin

/-!
# 1RB0LF_1LC1RA_0RD1LB_0LA0RE_1RC1RB_---0LD: the bounce phase

`C n m` is the configuration `0^∞ 1000 (100)^(n+1) 1000 100 100 E>0 0 (100)^m 1 0^∞`: a marker `1000` with n + 1
units `100` on its left and, right of it, two units and the head, then m more units.  One bounce (`bounce`,
10m + 53 steps) moves the marker one unit left and adds two units at the right end: `C (n+1) m → C n (m+2)`.
So `C n m` reaches `C 0 (m + 2n)` (`bounces`), and blank tape reaches `C 17 4` after 5467 steps (`init_C`).
Everything is checked by Lean's kernel.
-/

namespace H69875

open TM

def u3 : List Bool := [false, false, true]
def mk4 : List Bool := [false, false, false, true]

def leftT (n : Nat) : Tape := rep 2 u3 (app mk4 (rep (n + 1) u3 (app mk4 blank)))
def rightT (m : Nat) : Tape := cons false (cons false (rep m [true, false, false] (cons true blank)))
def C (n m : Nat) : Config := ⟨leftT n, rightT m, .E⟩

theorem cons_true_u (k : Nat) (s : Tape) : cons true (rep k [false, false, true] s) = rep k [true, false, false] (cons true s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    show cons true (cons false (cons false (cons true (rep k [false, false, true] s)))) = _
    rw [ih]; rfl

theorem bounceC (n m : Nat) : steps (10 * m + 53) (C (n + 1) m) = some (C n (m + 2)) := by
  have h := bounce m (rep n u3 (app mk4 blank))
  have e1 : leftT (n + 1) = cons false (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (rep n u3 (app mk4 blank))))))))))))))))) := rfl
  have e2 : leftT n = cons false (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (cons true (cons false (cons false (cons true (rep n u3 (app mk4 blank)))))))))))))) := rfl
  have e3 : cons false (cons false (cons true (cons false (cons false (cons true (rep m [false, false, true]
      (cons false (cons false (cons true blank))))))))) = rightT (m + 2) := by
    show _ = cons false (cons false (cons true (cons false (cons false (rep (m + 1) [true, false, false] (cons true blank))))))
    rw [cons_true_u, show cons true (cons false (cons false (cons true blank))) = app [true, false, false] (cons true blank)
      from rfl, rep_app_comm]
  show steps _ (⟨leftT (n + 1), rightT m, .E⟩ : Config) = some ⟨leftT n, rightT (m + 2), .E⟩
  rw [e1, e2, ← e3]; exact h

/-- The cost of `n` bounces from `C n m`. -/
def bcost : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => 10 * m + 53 + bcost n (m + 2)

theorem bounces : ∀ (n m : Nat), steps (bcost n m) (C n m) = some (C 0 (m + 2 * n))
  | 0, m => rfl
  | n + 1, m => by
    have h := bounces n (m + 2)
    rw [show m + 2 + 2 * n = m + 2 * (n + 1) by omega] at h
    exact steps_seq trans (bounceC n m) h

theorem bcost_closed : ∀ (n m : Nat), bcost n m + 10 * n = n * (10 * m + 53) + 10 * n * n
  | 0, m => by simp [bcost]
  | n + 1, m => by
    have h := bcost_closed n (m + 2)
    simp only [bcost]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_comm, Nat.mul_left_comm] at h ⊢
    omega

set_option maxRecDepth 100000 in
theorem init_C : steps 5467 init = some (C 17 4) := by
  have h : steps 5467 init = some (FCfg.toCfg ⟨[false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,true,false,false,false,true,false,false,false,false], [false,false,true,false,false,true,false,false,true,false,false,true,false,false,true], .E⟩) :=
    blank_reaches trans (by decide)
  rw [h]
  simp only [FCfg.toCfg, C, leftT, rightT, u3, mk4, rep, app, cons_false_blank]

/-- From blank tape the machine reaches `C 0 38`, where the two markers meet, after 5467 + bcost 17 4 steps. -/
theorem init_meet : steps (5467 + bcost 17 4) init = some (C 0 38) := steps_seq trans init_C (bounces 17 4)

end H69875
