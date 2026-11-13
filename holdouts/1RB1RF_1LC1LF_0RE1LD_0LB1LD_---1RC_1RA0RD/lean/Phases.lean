import Pieces
import Norm

/-!
# 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD: the whole phase map

Two kinds of configurations (tapes left to right, `S>` the head in state S):

* `PS a c` = `0^inf B> 0 0 (10)^a 1^c 0^inf`, a *pass start*;
* `Q R m c` = `0^inf (10)^R (11)^m A> 1^c 0^inf`, a *phase* of a pass.

`next` is the map from one of them to the next one the machine reaches, and `next_sound` proves that the machine
really goes there, in every case and for all parameters (each case is one symbolic run of `Pieces.lean`, or the
rounds lemma `q_rounds` built from one of them by induction, glued to `PS`/`Q` by `tape_eq`).  `PS a 0` and `PS a 1`
halt (`ps_halts`); `next` returns `none` exactly there and on configurations that are never reached (`m < 2`, `c = 0`,
see `next_some`).  The run from blank tape reaches `PS 0 2` (`init_ps`).

So the machine halts from blank tape if and only if iterating `next` from `PS 0 2` reaches `PS a 0` or `PS a 1`
(`halts_iff_iter`, one direction proved here: `reach_iter` and `ps_halts`; the other direction holds because every
step of `next` is a run of the deterministic machine that does not pass a halting configuration).  The map, read at
pass starts, is the pass map of `py/passmap.py` (checked there with `lean_map`).  Whether the iteration ever reaches
`c ≤ 1` is open.
-/

namespace H149707

open TM

/-- `0^inf B> 0 0 (10)^a 1^c 0^inf`. -/
def PS (a c : Nat) : Config := ⟨blank, cons false (cons false (rep a [true, false] (rep c [true] blank))), .B⟩

/-- `0^inf (10)^R (11)^m A> 1^c 0^inf`. -/
def Q (R m c : Nat) : Config := ⟨rep m [true, true] (rep R [false, true] blank), rep c [true] blank, .A⟩

/-- A phase: a pass start or a configuration inside a pass. -/
inductive Ph where
  | ps (a c : Nat)
  | q (R m c : Nat)
  deriving DecidableEq, Repr

def Ph.cfg : Ph → Config
  | .ps a c => PS a c
  | .q R m c => Q R m c

/-- The phase map.  Rounds are taken all at once: `j = min (R + 1) ((c + 2) / 2)` of them, until no `10` is left
or the block of 1s on the right is down to one or two. -/
def next : Ph → Option Ph
  | .ps _ 0 => none
  | .ps _ 1 => none
  | .ps 0 2 => some (.ps 0 5)
  | .ps 0 (c + 3) => some (.ps 2 (c + 1))
  | .ps (a + 1) (c + 2) => some (.q a 2 (c + 2))
  | .q (R + 1) (m + 2) (c + 3) =>
      some (.q (R + 1 - min (R + 1) ((c + 2) / 2)) (m + 2 + 2 * min (R + 1) ((c + 2) / 2))
        (c + 3 - 2 * min (R + 1) ((c + 2) / 2)))
  | .q 0 (m + 2) (c + 5) => some (.ps (m + 4) (c + 1))
  | .q 0 (m + 2) 1 => some (.ps 0 (2 * m + 8))
  | .q 0 (m + 2) 2 => some (.ps 0 (2 * m + 6))
  | .q 0 (m + 2) 3 => some (.ps 0 (2 * m + 11))
  | .q 0 (m + 2) 4 => some (.ps 0 (2 * m + 9))
  | .q 1 (m + 2) 1 => some (.ps 2 (2 * m + 6))
  | .q 1 (m + 2) 2 => some (.ps 2 (2 * m + 4))
  | .q (R + 2) (m + 2) 1 => some (.q R 2 (2 * m + 8))
  | .q (R + 2) (m + 2) 2 => some (.q R 2 (2 * m + 6))
  | .q _ _ _ => none

/-- One round, `Q (a+1) (m+2) (c+3)` to `Q a (m+4) (c+1)`. -/
theorem q_round (a m c : Nat) : ∃ n, 0 < n ∧ steps n (Q (a + 1) (m + 2) (c + 3)) = some (Q a (m + 4) (c + 1)) :=
  ⟨_, by omega, steps_eq_of (pc_round a c m) (cfg_eq (by tape_eq) (by tape_eq)) (cfg_eq (by tape_eq) (by tape_eq))⟩

/-- `j` rounds. -/
theorem q_rounds (j : Nat) : ∀ R m c, ∃ n, j ≤ n ∧ steps n (Q (R + j) (m + 2) (c + 2 * j + 1)) = some (Q R (m + 2 + 2 * j) (c + 1)) := by
  induction j with
  | zero => intro R m c; exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ j ih =>
    intro R m c
    obtain ⟨n1, p1, h1⟩ := q_round (R + j) m (c + 2 * j)
    obtain ⟨n2, p2, h2⟩ := ih R (m + 2) c
    rw [show R + j + 1 = R + (j + 1) by omega, show c + 2 * j + 3 = c + 2 * (j + 1) + 1 by omega] at h1
    rw [show m + 2 + 2 = m + 4 by omega, show m + 4 + 2 * j = m + 2 + 2 * (j + 1) by omega] at h2
    exact ⟨n1 + n2, by omega, steps_seq trans h1 h2⟩

theorem next_sound : ∀ p p', next p = some p' → ∃ n, 0 < n ∧ steps n p.cfg = some p'.cfg
  | .ps _ 0, _, h => by simp [next] at h
  | .ps _ 1, _, h => by simp [next] at h
  | .ps 0 2, _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, PS]
    exact ⟨_, by omega, steps_eq_of pc_ps02 (cfg_eq (by tape_eq) (by tape_eq)) (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .ps 0 (c + 3), _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, PS]
    exact ⟨_, by omega, steps_eq_of (pc_ps0 c) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .ps (a + 1) (c + 2), _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, PS, Q]
    exact ⟨_, by omega, steps_eq_of (pc_start a c) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .q (R + 1) (m + 2) (c + 3), _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    have hj1 : min (R + 1) ((c + 2) / 2) ≤ R + 1 := Nat.min_le_left _ _
    have hj2 : 2 * min (R + 1) ((c + 2) / 2) ≤ c + 2 := by
      have := Nat.min_le_right (R + 1) ((c + 2) / 2); omega
    have hj0 : 1 ≤ min (R + 1) ((c + 2) / 2) := by
      have : 1 ≤ (c + 2) / 2 := by omega
      exact Nat.le_min.mpr ⟨by omega, this⟩
    obtain ⟨n, hn, h⟩ := q_rounds (min (R + 1) ((c + 2) / 2)) (R + 1 - min (R + 1) ((c + 2) / 2)) m
      (c + 2 - 2 * min (R + 1) ((c + 2) / 2))
    refine ⟨n, by omega, steps_eq_of h ?_ ?_⟩
    · simp only [Ph.cfg]; congr 1 <;> omega
    · simp only [Ph.cfg]; congr 1; omega
  | .q 0 (m + 2) (c + 5), _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, PS, Q]
    exact ⟨_, by omega, steps_eq_of (pc_end c m) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .q 0 (m + 2) 1, _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, PS, Q]
    exact ⟨_, by omega, steps_eq_of (pc_end1 m) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .q 0 (m + 2) 2, _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, PS, Q]
    exact ⟨_, by omega, steps_eq_of (pc_end2 m) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .q 0 (m + 2) 3, _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, PS, Q]
    exact ⟨_, by omega, steps_eq_of (pc_end3 m) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .q 0 (m + 2) 4, _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, PS, Q]
    exact ⟨_, by omega, steps_eq_of (pc_end4 m) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .q 1 (m + 2) 1, _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, PS, Q]
    exact ⟨_, by omega, steps_eq_of (pc_one1 m) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .q 1 (m + 2) 2, _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, PS, Q]
    exact ⟨_, by omega, steps_eq_of (pc_one2 m) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .q (R + 2) (m + 2) 1, _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, Q]
    exact ⟨_, by omega, steps_eq_of (pc_reb1 R m) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .q (R + 2) (m + 2) 2, _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    simp only [Ph.cfg, Q]
    exact ⟨_, by omega, steps_eq_of (pc_reb2 R m) (cfg_eq (by tape_eq) (by tape_eq))
      (cfg_eq (by tape_eq) (by tape_eq))⟩
  | .q 0 0 _, _, h => by simp [next] at h
  | .q 0 1 _, _, h => by simp [next] at h
  | .q (_ + 1) 0 _, _, h => by simp [next] at h
  | .q (_ + 1) 1 _, _, h => by simp [next] at h
  | .q _ (_ + 2) 0, _, h => by simp [next] at h

/-- `k` steps of the phase map. -/
def iter : Nat → Ph → Option Ph
  | 0, p => some p
  | k + 1, p => (next p).bind (iter k)

theorem reach_iter : ∀ k p p', iter k p = some p' → ∃ n, k ≤ n ∧ steps n p.cfg = some p'.cfg
  | 0, p, p', h => by simp only [iter, Option.some.injEq] at h; subst h; exact ⟨0, Nat.le_refl 0, rfl⟩
  | k + 1, p, p', h => by
    simp only [iter] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp, Option.bind_some] at h
      obtain ⟨n1, p1, h1⟩ := next_sound p q hp
      obtain ⟨n2, p2, h2⟩ := reach_iter k q p' h
      exact ⟨n1 + n2, by omega, steps_seq trans h1 h2⟩

/-- The run from blank tape reaches `PS 0 2` after 4 steps. -/
theorem init_ps : steps 4 init = some (PS 0 2) := pc_init

/-- `PS a 0` and `PS a 1` halt (C and E zip right over the `10`s and E reads a blank). -/
theorem ps_halts (a c : Nat) (hc : c ≤ 1) : TM.Halts trans (PS a c) := by
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · exact ⟨_, _, pc_halt0 a, rfl⟩
  · exact ⟨_, _, pc_halt1 a, rfl⟩

/-- The phases that occur: in `Q R m c` always `m ≥ 2` and `c ≥ 1`. -/
def Good : Ph → Prop
  | .ps _ _ => True
  | .q _ m c => 2 ≤ m ∧ 1 ≤ c

theorem next_good (p p' : Ph) (h : next p = some p') : Good p' := by
  unfold next at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp only [Good] <;> omega

/-- On a phase that occurs, `next` fails only at `PS a 0` and `PS a 1`. -/
theorem next_none : ∀ p, Good p → next p = none → ∃ a c, c ≤ 1 ∧ p = .ps a c
  | .ps a 0, _, _ => ⟨a, 0, by omega, rfl⟩
  | .ps a 1, _, _ => ⟨a, 1, by omega, rfl⟩
  | .ps 0 2, _, h | .ps 0 (_ + 3), _, h | .ps (_ + 1) (_ + 2), _, h => by simp [next] at h
  | .q (_ + 1) (_ + 2) (_ + 3), _, h | .q 0 (_ + 2) (_ + 5), _, h => by simp [next] at h
  | .q 0 (_ + 2) 1, _, h | .q 0 (_ + 2) 2, _, h | .q 0 (_ + 2) 3, _, h | .q 0 (_ + 2) 4, _, h => by simp [next] at h
  | .q 1 (_ + 2) 1, _, h | .q 1 (_ + 2) 2, _, h | .q (_ + 2) (_ + 2) 1, _, h | .q (_ + 2) (_ + 2) 2, _, h => by
    simp [next] at h
  | .q _ 0 _, hg, _ | .q _ 1 _, hg, _ | .q _ (_ + 2) 0, hg, _ => by simp [Good] at hg

theorem iter_good : ∀ k p p', Good p → iter k p = some p' → Good p'
  | 0, p, p', hg, h => by simp only [iter, Option.some.injEq] at h; subst h; exact hg
  | k + 1, p, p', _, h => by
    simp only [iter] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp, Option.bind_some] at h
      exact iter_good k q p' (next_good p q hp) h

theorem iter_succ (k : Nat) (p p' : Ph) (h : iter k p = some p') : iter (k + 1) p = next p' := by
  induction k generalizing p with
  | zero => simp only [iter, Option.some.injEq] at h; subst h; simp [iter]
  | succ k ih =>
    simp only [iter] at h ⊢
    cases hp : next p with
    | none => simp [hp] at h
    | some q => simp only [hp, Option.bind_some] at h ⊢; exact ih q h

/-- **The machine halts from blank tape if and only if the phase map, iterated from `PS 0 2`, reaches `PS a c`
with `c ≤ 1`.** -/
theorem halts_iff :
    HaltsFromBlank ↔ ∃ k a c, c ≤ 1 ∧ iter k (.ps 0 2) = some (.ps a c) := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    -- every iterate exists
    have hall : ∀ k, ∃ p, iter k (.ps 0 2) = some p := by
      intro k
      induction k with
      | zero => exact ⟨_, rfl⟩
      | succ k ih =>
        obtain ⟨p, hp⟩ := ih
        rw [iter_succ k _ p hp]
        cases hn : next p with
        | some q => exact ⟨q, rfl⟩
        | none =>
          obtain ⟨a, c, hc, rfl⟩ := next_none p (iter_good k (.ps 0 2) p True.intro hp) hn
          exact absurd ⟨k, a, c, hc, hp⟩ hno
    apply TM.not_halts_of_forall trans _ hh
    apply TM.forall_of_unbounded trans (fun m => ∃ c', steps m init = some c')
    · intro n
      obtain ⟨p, hp⟩ := hall n
      obtain ⟨m, hm, h⟩ := reach_iter n _ p hp
      exact ⟨4 + m, by omega, _, steps_seq trans init_ps h⟩
    · exact fun _ h => h
  · rintro ⟨k, a, c, hc, h⟩
    obtain ⟨n, -, h1⟩ := reach_iter k _ _ h
    obtain ⟨m, c', h2, h3⟩ := ps_halts a c hc
    exact ⟨4 + (n + m), c', steps_seq trans init_ps (steps_seq trans h1 h2), h3⟩

/-- `next` is defined `k` times in a row from `p`. -/
def okFor : Nat → Ph → Bool
  | 0, _ => true
  | k + 1, p => match next p with
    | none => false
    | some q => okFor k q

theorem okFor_sound : ∀ k p, okFor k p = true → ∀ j, j < k → ∀ a c, iter j p = some (.ps a c) → 2 ≤ c
  | 0, _, _, j, hj, _, _, _ => absurd hj (Nat.not_lt_zero j)
  | k + 1, p, h, j, hj, a, c, hi => by
    simp only [okFor] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp] at h
      cases j with
      | zero =>
        simp only [iter, Option.some.injEq] at hi; subst hi
        rcases c with _ | _ | c
        · simp [next] at hp
        · simp [next] at hp
        · omega
      | succ j =>
        simp only [iter, hp, Option.bind_some] at hi
        exact okFor_sound k q h j (by omega) a c hi

/-- The first 10^8 phases of the run from blank tape contain no `PS a 0` or `PS a 1`, so by
`halts_iff` a halt, if any, comes later. -/
theorem no_halt_phases : ∀ j, j < 100000000 → ∀ a c, iter j (.ps 0 2) = some (.ps a c) → 2 ≤ c :=
  okFor_sound _ _ (by native_decide)

end H149707
