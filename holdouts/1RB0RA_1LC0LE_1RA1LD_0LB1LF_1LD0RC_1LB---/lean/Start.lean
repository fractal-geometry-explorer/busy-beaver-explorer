import Machine
import Macro

/-!
# From blank tape into the clean regime

`start`: after 58,429 steps from blank tape the machine is at the sweep configuration
`(p, y) = (2, 72)` with the levels `(12, 26) (10, 3) (2, 1) (2, 0) (2, 0)` and `11` behind it (`native_decide`, by the
list simulator of `TM/Fin.lean`).  `clean_chain` then runs four clean phases by the kernel-checked rules of
`Macro.lean`: `y = 72 → 96 → 128 → 170 → 226`, the counter `p = 2 → 10` and the second level `(12, 26) → (20, 18)`,
reaching step 399,523 — the step at which the C simulator sees that configuration too.  There `y = 226 ≡ 1 (mod 3)`,
and the phase ends in the other regime.
-/

namespace H112769

open TM

/-- Lists that mirror `rep`, `lv` and `cfg`, for comparing with the list simulator. -/
def lrep (n : Nat) (w : List Bool) (l : List Bool) : List Bool := (List.replicate n w).flatten ++ l
def llv (x y : Nat) (l : List Bool) : List Bool := lrep x W ([true, true, true, false, false] ++ lrep y V l)
def lfront (p : Nat) (l : List Bool) : List Bool := [false, true, false] ++ lrep p W ([true, true, true, true] ++ l)

theorem app_lrep (n : Nat) (w l : List Bool) (s : Tape) : app (lrep n w l) s = rep n w (app l s) := by
  induction n with
  | zero => simp [lrep]
  | succ n ih =>
    simp only [lrep, List.replicate_succ, List.flatten_cons, List.append_assoc] at ih ⊢
    rw [← app_app, ih]; rfl

theorem app_llv (x y : Nat) (l : List Bool) (s : Tape) : app (llv x y l) s = lv x y (app l s) := by
  simp only [llv, app_lrep, ← app_app, lv]; rfl

theorem app_lfront (p : Nat) (l : List Bool) (s : Tape) :
    app (lfront p l) s = cons false (cons true (cons false (rep p W (cons true (cons true (cons true (cons true
      (app l s)))))))) := by
  simp only [lfront, ← app_app, app_lrep]; rfl

/-- Drop trailing blank cells. -/
def trim : List Bool → List Bool
  | [] => []
  | a :: t =>
    match trim t with
    | [] => if a = false then [] else [a]
    | b :: u => a :: b :: u

theorem app_trim (l : List Bool) : app (trim l) blank = app l blank := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [trim]
    split
    · next h =>
      rw [h] at ih
      split
      · next ha => rw [app_cons, ← ih, ha]; exact cons_false_blank.symm
      · next ha =>
        have : a = true := by cases a <;> simp_all
        subst this
        show cons true (app [] blank) = cons true (app t blank)
        rw [ih]
    · next b u h =>
      rw [h] at ih
      show cons a (app (b :: u) blank) = cons a (app t blank)
      rw [ih]

/-- The tape right of the head at step 58,429, as a list. -/
def r0 : List Bool :=
  lfront 2 (llv 0 72 (llv 12 26 (llv 10 3 (llv 2 1 (llv 2 0 (llv 2 0 [true, true]))))))

/-- The rest of the tape behind the second level at step 58,429. -/
def R3 : Tape := lv 10 3 (lv 2 1 (lv 2 0 (lv 2 0 (cons true (cons true blank)))))

theorem start_list : (fsteps 58429 (FCfg.blank .A)).map (fun c => (trim c.l, trim c.r, c.st)) =
    some ([], r0, .C) := by native_decide

theorem start : steps 58429 init = some (cfg 2 (lv 0 72 (lv 12 26 R3))) := by
  have hS := start_list
  cases e : fsteps 58429 (FCfg.blank .A) with
  | none => rw [e] at hS; cases hS
  | some c =>
    rw [e] at hS
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨hl, hr, hs⟩ := hS
    have h := blank_reaches trans e
    refine h.trans ?_
    obtain ⟨l, r, s⟩ := c
    simp only [FCfg.toCfg] at hl hr hs ⊢
    rw [← app_trim l, ← app_trim r, hl, hr, hs]
    simp only [r0, app_lfront, app_llv, cfg, R3]
    rfl

/-- Four clean phases after `start`, all by the kernel. -/
theorem clean_chain : steps 399523 init = some (cfg 10 (lv 0 226 (lv 20 18 R3))) := by
  have h1 := cleanA 2 23 10 24 (R3)
  have h2 := cleanA 4 31 12 22 (R3)
  have h3 := cleanB 6 41 14 20 (R3)
  have h4 := cleanB 8 55 16 18 (R3)
  have h := steps_seq trans start (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))
  exact steps_congr trans (by decide) h

end H112769
