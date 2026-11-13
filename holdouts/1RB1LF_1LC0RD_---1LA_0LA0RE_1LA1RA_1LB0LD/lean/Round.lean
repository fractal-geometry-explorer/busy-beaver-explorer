import Rules

/-!
# One round, for every length of the block of ones

A round starts at `R0 n T`: the tape `D> 0 0 111 0 1^n T` with the head at its left end, blank on both sides.  The
machine sweeps back and forth: each sweep takes three ones from the block `1^n` and adds one counting block `1110`
on its left (and one cell to the tape on the left).  When one, two or three ones are left, the end of the round turns
the counting blocks back into ones, so the next round starts with about `4/3 n` ones.  Here `n = c + 3 t`
(`c ∈ {1, 2, 3}`), and the rules of `Rules.lean` are chained by induction on the number of sweeps.

Proved for the three tails `T` that the run from blank tape visits most (empty, `011`, `010111`); the others are
handled by `py/roundmap.py` (simulation, not Lean).
-/

namespace H176107

open TM

def tE : List Bool := []
def tA : List Bool := [false, true, true]
def tB : List Bool := [false, true, false, true, true, true]

/-- The start of a round: `D> 0 0 111 0 1^n T`, blank on both sides. -/
def R0 (n : Nat) (T : List Bool) : Config :=
  ⟨blank, app [false, false, true, true, true, false] (rep n [true] (app T blank)), .D⟩

/-- After `k + 1` sweeps: `A> 0 11 0 11 0 111 (0111)^k 0 1^c T`. -/
def X (k c : Nat) (T : List Bool) : Config :=
  ⟨blank, app [false, true, true, false, true, true, false, true, true, true]
    (rep k [false, true, true, true] (cons false (rep c [true] (app T blank)))), .A⟩

theorem rep4 (k : Nat) (s : Tape) : rep k [true, true, true, true] s = rep (4 * k) [true] s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by omega, rep_succ, ih]; rfl

theorem ones_cons (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl

theorem rep_ones_cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s

theorem first (n : Nat) (T : List Bool) : steps (60 + 35) (R0 (n + 1) T) = some (X 0 (n + 1) T) :=
  steps_seq trans (start (n + 1) (app T blank)) (sweep0 n (app T blank))

theorem one_sweep (k m : Nat) (T : List Bool) :
    steps (10 * k + 45) (X k (m + 4) T) = some (X (k + 1) (m + 1) T) := by
  have h := sweep k m (app T blank)
  have e : cons false (cons true (rep k [true, true, false, true] (cons true (cons true (cons false (cons true
      (rep m [true] (app T blank)))))))) =
      rep (k + 1) [false, true, true, true] (cons false (rep (m + 1) [true] (app T blank))) := by
    have r := rep_rotate k [false, true] [true, true, false, true] [false, true, true, true] rfl
      (cons true (cons true (cons false (cons true (rep m [true] (app T blank))))))
    simp only [app_cons, app_nil] at r
    rw [r, ← rep_app_comm]; rfl
  simp only [X, app_cons, app_nil]
  rw [← e]; exact h

/-- `t` sweeps. -/
theorem sweeps (T : List Bool) : ∀ t k c, ∃ s, steps s (X k (c + 1 + 3 * t) T) = some (X (k + t) (c + 1) T) := by
  intro t
  induction t with
  | zero => intro k c; exact ⟨0, rfl⟩
  | succ t ih =>
    intro k c
    obtain ⟨s, hs⟩ := ih (k + 1) c
    have e : c + 1 + 3 * (t + 1) = (c + 3 * t) + 4 := by omega
    have h1 := one_sweep k (c + 3 * t) T
    rw [show c + 3 * t + 1 = c + 1 + 3 * t by omega] at h1
    rw [show k + 1 + t = k + (t + 1) by omega] at hs
    exact ⟨_, by rw [e]; exact steps_seq trans h1 hs⟩

/-- From a round start to the end of its sweeps. -/
theorem to_end (T : List Bool) (t c : Nat) :
    ∃ s, steps s (R0 (c + 1 + 3 * t) T) = some (X t (c + 1) T) := by
  have h1 := first (c + 3 * t) T
  rw [show c + 3 * t + 1 = c + 1 + 3 * t by omega] at h1
  obtain ⟨s, hs⟩ := sweeps T t 0 c
  rw [Nat.zero_add] at hs
  exact ⟨_, steps_seq trans h1 hs⟩

/-! ## The nine round rules -/

macro "fin_end" h:term : tactic =>
  `(tactic| (have hh := $h; simp only [R0, X, tE, tA, tB, app_cons, app_nil, rep4] at hh ⊢;
             simp only [rep_ones_cons, ones_cons, Nat.add_assoc, Nat.reduceAdd] at hh ⊢;
             exact ⟨_, hh⟩))

theorem end_e_1 (t : Nat) : ∃ s, steps s (X t 1 tE) = some (R0 (4 * t + 11) tE) := by fin_end end_e1 t
theorem end_e_2 (t : Nat) : ∃ s, steps s (X t 2 tE) = some (R0 (4 * t + 7) tA) := by fin_end end_e2 t
theorem end_e_3 (t : Nat) : ∃ s, steps s (X t 3 tE) = some (R0 (4 * t + 11) tE) := by fin_end end_e3 t
theorem end_a_1 (t : Nat) : ∃ s, steps s (X t 1 tA) = some (R0 (4 * t + 11) tA) := by fin_end end_a1 t
theorem end_a_2 (t : Nat) : ∃ s, steps s (X t 2 tA) = some (R0 (4 * t + 7) tB) := by fin_end end_a2 t
theorem end_a_3 (t : Nat) : ∃ s, steps s (X t 3 tA) = some (R0 (4 * t + 11) tA) := by fin_end end_a3 t
theorem end_b_1 (t : Nat) : ∃ s, steps s (X t 1 tB) = some (R0 (4 * t + 19) tE) := by fin_end end_b1 t
theorem end_b_3 (t : Nat) : ∃ s, steps s (X t 3 tB) = some (R0 (4 * t + 19) tE) := by fin_end end_b3 t

/-! ## The round map on these tails -/

/-- The tails `T` of `R0 n T` that this file handles. -/
inductive Tl where
  | e | a | b
  deriving DecidableEq, Repr

def Tl.word : Tl → List Bool
  | .e => tE
  | .a => tA
  | .b => tB

/-- The next round start, for `n = c + 1 + 3 t`: `none` for `n = 0` and for the case (tail `b`, `c = 1`), which
leads to a tail not handled here (`01101`). -/
def next (n : Nat) (T : Tl) : Option (Nat × Tl) :=
  if n = 0 then none else
  let t := (n - 1) / 3
  match (n - 1) % 3, T with
  | 0, .e => some (4 * t + 11, .e)
  | 1, .e => some (4 * t + 7, .a)
  | 2, .e => some (4 * t + 11, .e)
  | 0, .a => some (4 * t + 11, .a)
  | 1, .a => some (4 * t + 7, .b)
  | 2, .a => some (4 * t + 11, .a)
  | 0, .b => some (4 * t + 19, .e)
  | 2, .b => some (4 * t + 19, .e)
  | _, _ => none

/-- A round, whenever `next` is defined: the machine goes from `R0 n T` to the next round start. -/
theorem round {n n' : Nat} {T T' : Tl} (h : next n T = some (n', T')) :
    ∃ s, steps s (R0 n T.word) = some (R0 n' T'.word) := by
  unfold next at h
  split at h
  · cases h
  · obtain ⟨c, t, hc, hn⟩ : ∃ c t, c < 3 ∧ n = c + 1 + 3 * t := ⟨(n - 1) % 3, (n - 1) / 3, Nat.mod_lt _ (by omega), by omega⟩
    have ht : (n - 1) / 3 = t := by omega
    have hcm : (n - 1) % 3 = c := by omega
    rw [ht, hcm] at h
    obtain ⟨s1, h1⟩ := to_end T.word t c
    rw [← hn] at h1
    have fin : ∀ s2, steps s2 (X t (c + 1) T.word) = some (R0 n' T'.word) →
        ∃ s, steps s (R0 n T.word) = some (R0 n' T'.word) := fun s2 h2 => ⟨_, steps_seq trans h1 h2⟩
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> cases T <;>
      simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · obtain ⟨s2, h2⟩ := end_e_1 t; exact fin s2 h2
    · obtain ⟨s2, h2⟩ := end_a_1 t; exact fin s2 h2
    · obtain ⟨s2, h2⟩ := end_b_1 t; exact fin s2 h2
    · obtain ⟨s2, h2⟩ := end_e_2 t; exact fin s2 h2
    · obtain ⟨s2, h2⟩ := end_a_2 t; exact fin s2 h2
    · obtain ⟨s2, h2⟩ := end_e_3 t; exact fin s2 h2
    · obtain ⟨s2, h2⟩ := end_a_3 t; exact fin s2 h2
    · obtain ⟨s2, h2⟩ := end_b_3 t; exact fin s2 h2

/-- The run from blank tape reaches the round start `R0 3 []` after 51 steps. -/
theorem blank_to_round : steps 51 init = some (R0 3 tE) := rfl

/-! ## A round start that halts

The round map is defined on tails of any shape (py/roundmap.py follows them), and some tails lead to the halting
transition.  An example, far from the run from blank tape: the tail `0110101010 11` (blocks of ones 2, 1, 1, 1, 2)
with 57 ones in the block halts within its round. -/

def tH : List Bool := [false, true, true, false, true, false, true, false, true, false, true, true]

theorem halting_round : steps 2575 (R0 57 tH) = none := by
  have e : R0 57 tH = FCfg.toCfg ⟨[], [false, false, true, true, true, false] ++ List.replicate 57 true ++ tH, .D⟩ := by
    simp only [R0, FCfg.toCfg, app_nil, ← app_app]
    congr 2
  rw [e]
  show TM.steps trans 2575 _ = none
  rw [FCfg.steps_eq]
  decide +kernel

end H176107
