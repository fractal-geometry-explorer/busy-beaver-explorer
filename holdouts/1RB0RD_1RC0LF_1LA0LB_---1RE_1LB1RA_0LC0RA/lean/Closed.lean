import Rules

/-!
# 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA: a closed set of round ends implies that the machine never halts

`node B T` is the tape at the end of a round, when state A arrives at the left end and the left block is used up:

    A> 01001000 (01)^B T        (T: the tail, a short word; the rest of the tape blank)

`py/closure/closure.py` computes a set of 1144 classes (a tail T out of 62, a residue of B modulo 27, 45, 48 or 66,
B >= 20000) such that every `node B T` of a class reaches, after one round, a `node B' T'` of a class again
(`py/closure/cert.json`), and finds that the run from blank tape is at such a node after 2,340,515,329 steps
(B = 28531).  What is proved here, by the kernel, is that two facts of this form imply that the machine never
halts.  The two facts themselves are proved in `Replay.lean` by a verified symbolic executor (`Exec.lean`,
`Classes.lean`).
-/

namespace H11019

open TM

/-- The tape at the end of a round: `A> 01001000 (01)^B T`. -/
def node (B : Nat) (T : List Bool) : Config :=
  ⟨blank, app [false, true, false, false, true, false, false, false] (rep B [false, true] (app T blank)), .A⟩

/-- If the run from blank tape reaches a round end in a set `S`, and every round end in `S` reaches a round end in
`S` in at least one step, then the machine does not halt from blank tape. -/
theorem nonhalting_of_closed_set (S : Nat → List Bool → Prop)
    (reach : ∃ n B T, S B T ∧ steps n init = some (node B T))
    (closed : ∀ B T, S B T → ∃ n B' T', 0 < n ∧ S B' T' ∧ steps n (node B T) = some (node B' T')) :
    ¬ HaltsFromBlank := by
  have far : ∀ j, ∃ m, j ≤ m ∧ ∃ B T, S B T ∧ steps m init = some (node B T) := by
    intro j
    induction j with
    | zero =>
      obtain ⟨n, B, T, hS, h⟩ := reach
      exact ⟨n, Nat.zero_le n, B, T, hS, h⟩
    | succ j ih =>
      obtain ⟨m, hm, B, T, hS, h⟩ := ih
      obtain ⟨n, B', T', hn, hS', h'⟩ := closed B T hS
      exact ⟨m + n, by omega, B', T', hS', steps_seq trans h h'⟩
  exact not_halts_of_forall trans
    (forall_of_unbounded trans (fun m => ∃ B T, S B T ∧ steps m init = some (node B T)) far
      (fun m ⟨B, T, _, h⟩ => ⟨_, h⟩))

end H11019
