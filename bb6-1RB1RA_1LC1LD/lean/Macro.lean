import Rules

/-!
# The pass from one right-end configuration to the next

From blank tape the run keeps returning to A on the blank cell right of the tape,

  `0^∞ 1^{b_k} 0 … 0 1^{b_2} 0 1^{b_1} A> 0^∞`

(blocks of ones separated by single 0s).  Three steps later (`start`) it is in the pass configuration

  `K ls n  =  0^∞ … 0 1^{l_1} 0 1^n B> 1 0 1 0^∞`        (`ls = [l_1, l_2, …]` the blocks left of the last, nearest first)

with `n + 1` the last block.  B then converts the last block from the right, `111` into `101` (7 steps per three
cells, `Rules.lean`), and what happens at its left end depends on `n mod 3`:

* `n ≡ 0 (mod 3)`, `n = 3m`: the block to the left gains 6, and the converted cells come back as a new last block
  (`kA`, `kB`); `n = 0` halts (`K_zero_halts`), and `n = 3` gives `n' = 0` (`kA0`), so a last block 4 halts on the
  next pass;
* `n ≡ 1 (mod 3)`: the two blocks to the left gain, and the last block is rebuilt from them (`kC`, `kD`);
* `n ≡ 2 (mod 3)`: the converter carries on into the next block, which is the recursive case and is not covered here.

On the way back to the right the head alternates between two phases, A and Y, one word `011` at a time; every second
word the two blocks to the left gain 2 and 4 (`aphase`, `yphase`).  `next` is the resulting map on block lists and
`next_sound` says the machine really does it, for every block length and every tape to the left (kernel only).
-/

namespace BB6c

open TM

/-- Some run from `c` ends at `c'`. -/
def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches.trans {a b c : Config} (h₁ : Reaches a b) (h₂ : Reaches b c) : Reaches a c := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  exact ⟨n₁ + n₂, steps_seq BB6c.trans h₁ h₂⟩

theorem reaches_of {n : Nat} {c c' : Config} (h : steps n c = some c') : Reaches c c' := ⟨n, h⟩

theorem reaches_eq {c c' c'' : Config} (h : Reaches c c') (e : c' = c'') : Reaches c c'' := e ▸ h

/-- The blocks to the left of the head, nearest first, each followed (outward) by a 0. -/
def lt : List Nat → Tape
  | [] => blank
  | l :: ls => rep l [true] (cons false (lt ls))

/-- A block of length 0 at the far end changes nothing: blank tape is all 0s. -/
theorem lt_zero : lt [0] = lt [] := cons_false_blank

/-- The pass configuration: B on the cell after the block `1^n`, which has `ls` to its left, with `1 0 1` and blank
tape to its right. -/
def K (ls : List Nat) (n : Nat) : Config := ⟨rep n [true] (cons false (lt ls)), cons true (cons false (cons true blank)), .B⟩

/-- The word `011` twice, read to the right: two converted words. -/
abbrev W : List Bool := [false, true, true, false, true, true]

/-- Phase A: `L 0 1^x 0 1^y A> R`. -/
def PA (L : Tape) (x y : Nat) (R : Tape) : Config := ⟨rep y [true] (cons false (rep x [true] (cons false L))), R, .A⟩

/-- Phase Y: `L 0 1^x 0 1^y 0 0 1 B> R`. -/
def PY (L : Tape) (x y : Nat) (R : Tape) : Config :=
  ⟨cons true (cons false (cons false (rep y [true] (cons false (rep x [true] (cons false L)))))), R, .B⟩

theorem ones_cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s := rep_app_comm n [true] s

theorem ones_add (a b : Nat) (s : Tape) : rep (a + b) [true] s = rep a [true] (rep b [true] s) := rep_add a b [true] s

/-- Six ones, `t` times. -/
theorem ones_six (t : Nat) (s : Tape) : rep (6 * t) [true] s = rep t [true, true, true, true, true, true] s := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show 6 * (t + 1) = 6 + 6 * t by omega, ones_add, ih]; rfl

/-- The A-to-A bounce, with the blocks in normal form. -/
theorem bump (L : Tape) (x y : Nat) :
    cons true (cons true (cons true (rep y [true] (cons true (cons false (cons true (cons true (rep x [true]
      (cons false L))))))))) = rep (y + 4) [true] (cons false (rep (x + 2) [true] (cons false L))) := by
  rw [ones_cons]; rfl

/-- Phase A over `t` double words: the two blocks gain `2t` and `4t`. -/
theorem aphase (L : Tape) (t : Nat) : ∀ (x y : Nat) (R : Tape),
    Reaches (PA L x y (rep t W R)) (PA L (x + 2 * t) (y + 4 * t) R) := by
  induction t with
  | zero => intro x y R; exact ⟨0, rfl⟩
  | succ t ih =>
    intro x y R
    have h₁ := a_two x y L (cons false (cons true (cons true (rep t W R))))
    have h₂ := y_two x y L (rep t W R)
    rw [bump] at h₂
    have h := (reaches_of (steps_seq trans h₁ h₂)).trans (ih (x + 2) (y + 4) R)
    rw [show x + 2 + 2 * t = x + 2 * (t + 1) by omega, show y + 4 + 4 * t = y + 4 * (t + 1) by omega] at h
    exact h

/-- Phase Y over `t` double words. -/
theorem yphase (L : Tape) (t : Nat) : ∀ (x y : Nat) (R : Tape),
    Reaches (PY L x y (rep t W R)) (PY L (x + 2 * t) (y + 4 * t) R) := by
  induction t with
  | zero => intro x y R; exact ⟨0, rfl⟩
  | succ t ih =>
    intro x y R
    have h₁ := y_two x y L (cons false (cons true (cons true (rep t W R))))
    rw [bump] at h₁
    have h₂ := a_two (x + 2) (y + 4) L (rep t W R)
    have h := (reaches_of (steps_seq trans h₁ h₂)).trans (ih (x + 2) (y + 4) R)
    rw [show x + 2 + 2 * t = x + 2 * (t + 1) by omega, show y + 4 + 4 * t = y + 4 * (t + 1) by omega] at h
    exact h

/-- Converted words written from the left end of a block, re-read from the right. -/
theorem rot1 (t : Nat) (s : Tape) :
    rep t [true, false, true, true, false, true] (cons true s) = cons true (rep t W s) :=
  (rep_rotate t [true] W _ rfl s).symm

theorem rot2 (t : Nat) (s : Tape) :
    cons false (cons true (rep t [true, false, true, true, false, true] s)) = rep t W (cons false (cons true s)) :=
  rep_rotate t [false, true] [true, false, true, true, false, true] W rfl s

/-! ## The pass, case by case (`n` the index of `K`, the last block `n + 1`) -/

/-- `K ls 0` halts: D reads a 0 with a 0 to its right at the right end of the tape. -/
theorem K_zero_halts (ls : List Nat) : ∃ c, steps 6 (K ls 0) = some c ∧ step c = none := ⟨_, rfl, rfl⟩

/-- Last block 4: the block to its left gains 6, and the new last block is 1, which halts next. -/
theorem kA0 (x : Nat) (ls : List Nat) : Reaches (K (x :: ls) 3) (K ((x + 6) :: ls) 0) :=
  reaches_of (conv3 x (lt ls))

/-- Two blocks written by a bounce, in normal form. -/
theorem blk2 (c d : Nat) (s : Tape) :
    rep c [true] (cons true (cons false (cons true (cons true (rep d [true] s))))) =
      rep (c + 1) [true] (cons false (rep (d + 2) [true] s)) := by
  rw [ones_cons]; rfl

/-- A on the blank cell after the last block: the pass configuration. -/
theorem pa_end (ls : List Nat) (x y : Nat) : steps 3 (PA (lt ls) x (y + 1) blank) = some (K (x :: ls) y) :=
  start y _

/-- Last block `6t + 10`. -/
theorem kA (t x : Nat) (ls : List Nat) :
    Reaches (K (x :: ls) (6 * (t + 1) + 3)) (K ((x + 2 * t + 8) :: ls) (4 * t + 4)) := by
  have h₁ : steps (14 * t + 32) (K (x :: ls) (6 * (t + 1) + 3)) =
      some (PA (lt ls) (x + 6) 3 (rep t W (cons false (cons true (cons true blank))))) := by
    have e : K (x :: ls) (6 * (t + 1) + 3) = ⟨rep (t + 1) [true, true, true, true, true, true] (cons true (cons true
        (cons true (cons false (rep x [true] (cons false (lt ls))))))), cons true (cons false (cons true blank)), .B⟩ := by
      simp only [K, lt]; rw [ones_add, ones_six]; rfl
    rw [e, conv6t9, rot2]; rfl
  have h₂ := aphase (lt ls) t (x + 6) 3 (cons false (cons true (cons true blank)))
  have h₃ : steps (7 + (10 * (3 + 4 * t) + 12)) (PA (lt ls) (x + 6 + 2 * t) (3 + 4 * t)
      (cons false (cons true (cons true blank)))) = some (K ((x + 2 * t + 8) :: ls) (4 * t + 4)) := by
    have h := steps_seq trans (a_two (x + 6 + 2 * t) (3 + 4 * t) (lt ls) blank) (y_end (x + 6 + 2 * t) (3 + 4 * t) (lt ls))
    rw [blk2, show 3 + 4 * t + 1 = 4 * t + 4 by omega, show x + 6 + 2 * t + 2 = x + 2 * t + 8 by omega] at h
    exact h
  exact ((reaches_of h₁).trans h₂).trans (reaches_of h₃)

/-- Last block `6t + 7`. -/
theorem kB (t x : Nat) (ls : List Nat) :
    Reaches (K (x :: ls) (6 * (t + 1))) (K ((x + 2 * t + 6) :: ls) (4 * t + 2)) := by
  have h₁ : steps (14 * t + 24 + 1) (K (x :: ls) (6 * (t + 1))) = some (PA (lt ls) (x + 6) 3 (rep t W blank)) := by
    have e : K (x :: ls) (6 * (t + 1)) = ⟨rep (t + 1) [true, true, true, true, true, true]
        (cons false (rep x [true] (cons false (lt ls)))), cons true (cons false (cons true blank)), .B⟩ := by
      simp only [K, lt]; rw [ones_six]
    have h : steps (14 * t + 24) (K (x :: ls) (6 * (t + 1))) =
        some (PA (lt ls) (x + 6) 2 (cons true (rep t W blank))) := by
      rw [e, conv6t6, rot1]; rfl
    exact steps_seq trans h rfl
  have h₂ := aphase (lt ls) t (x + 6) 3 blank
  have h₃ : steps 3 (PA (lt ls) (x + 6 + 2 * t) (3 + 4 * t) blank) = some (K ((x + 2 * t + 6) :: ls) (4 * t + 2)) := by
    rw [show 3 + 4 * t = 4 * t + 2 + 1 by omega, show x + 2 * t + 6 = x + 6 + 2 * t by omega]; exact pa_end _ _ _
  exact ((reaches_of h₁).trans h₂).trans (reaches_of h₃)

/-- Last block `6t + 2`. -/
theorem kC (t c d : Nat) (ls : List Nat) :
    Reaches (K (c :: d :: ls) (6 * t + 1)) (K ((d + 2 * t + 2) :: ls) (c + 4 * t + 2)) := by
  have h₁ : steps (10 * c + 14 * t + 12 + 1) (K (c :: d :: ls) (6 * t + 1)) =
      some (PA (lt ls) (d + 2) (c + 3) (rep t W blank)) := by
    have e : K (c :: d :: ls) (6 * t + 1) = ⟨rep t [true, true, true, true, true, true] (cons true (cons false
        (rep c [true] (cons false (rep d [true] (cons false (lt ls))))))), cons true (cons false (cons true blank)), .B⟩ := by
      simp only [K, lt]; rw [ones_add, ones_six]; rfl
    have h : steps (10 * c + 14 * t + 12) (K (c :: d :: ls) (6 * t + 1)) =
        some (PA (lt ls) (d + 2) (c + 2) (cons true (rep t W blank))) := by
      rw [e, conv6t1, rot1, blk2]; rfl
    exact steps_seq trans h rfl
  have h₂ := aphase (lt ls) t (d + 2) (c + 3) blank
  have h₃ : steps 3 (PA (lt ls) (d + 2 + 2 * t) (c + 3 + 4 * t) blank) =
      some (K ((d + 2 * t + 2) :: ls) (c + 4 * t + 2)) := by
    rw [show c + 3 + 4 * t = c + 4 * t + 2 + 1 by omega, show d + 2 * t + 2 = d + 2 + 2 * t by omega]
    exact pa_end _ _ _
  exact ((reaches_of h₁).trans h₂).trans (reaches_of h₃)

/-- Last block `6t + 5`. -/
theorem kD (t c d : Nat) (ls : List Nat) :
    Reaches (K (c :: d :: ls) (6 * t + 4)) (K ((d + 2 * t + 4) :: ls) (c + 4 * t + 4)) := by
  have e : K (c :: d :: ls) (6 * t + 4) = ⟨rep t [true, true, true, true, true, true]
      (cons true (cons true (cons true (cons true (cons false (rep c [true] (cons false (rep d [true]
        (cons false (lt ls)))))))))), cons true (cons false (cons true blank)), .B⟩ := by
    simp only [K, lt]; rw [ones_add, ones_six]; rfl
  have h₁ := conv6t4 c d t (lt ls)
  rw [← e] at h₁
  rw [blk2] at h₁
  cases t with
  | zero =>
    have h₂ := left_end (c + 3) (d + 2) (lt ls)
    rw [blk2] at h₂
    have h := steps_seq trans h₁ h₂
    exact reaches_of h
  | succ s =>
    rw [rot1] at h₁
    have h₂ := left_two (c + 3) (d + 2) (lt ls) (rep s W blank)
    rw [blk2] at h₂
    have h₃ := yphase (lt ls) s (d + 4) (c + 7) blank
    have h₄ := y_end (d + 4 + 2 * s) (c + 7 + 4 * s) (lt ls)
    rw [blk2] at h₄
    have h := ((reaches_of (steps_seq trans h₁ h₂)).trans h₃).trans (reaches_of h₄)
    rw [show c + 7 + 4 * s + 1 = c + 4 * (s + 1) + 4 by omega,
      show d + 4 + 2 * s + 2 = d + 2 * (s + 1) + 4 by omega] at h
    exact h

/-! ## The map on block lists -/

/-- One pass, on the blocks: `ls` the blocks left of the last (nearest first) and `n + 1` the last block.  `none`
when the last block is 1 (the machine halts, `K_zero_halts`) or a multiple of 3 (the recursive case, not covered). -/
def next (ls : List Nat) (n : Nat) : Option (List Nat × Nat) :=
  let x := ls.headD 0
  let d := ls.tail.headD 0
  if n = 3 then some ((x + 6) :: ls.tail, 0)
  else if n % 6 = 3 then some ((x + 2 * ((n - 9) / 6) + 8) :: ls.tail, 4 * ((n - 9) / 6) + 4)
  else if n % 6 = 0 ∧ 0 < n then some ((x + 2 * ((n - 6) / 6) + 6) :: ls.tail, 4 * ((n - 6) / 6) + 2)
  else if n % 6 = 1 then some ((d + 2 * (n / 6) + 2) :: ls.tail.tail, x + 4 * (n / 6) + 2)
  else if n % 6 = 4 then some ((d + 2 * (n / 6) + 4) :: ls.tail.tail, x + 4 * (n / 6) + 4)
  else none

/-- Missing blocks at the far end are blocks of length 0. -/
theorem K_pad1 (ls : List Nat) (n : Nat) : K ls n = K (ls.headD 0 :: ls.tail) n := by
  cases ls with
  | nil => simp only [K, List.headD, List.tail, lt, rep_zero, cons_false_blank]
  | cons _ _ => rfl

theorem K_pad2 (ls : List Nat) (n : Nat) :
    K ls n = K (ls.headD 0 :: ls.tail.headD 0 :: ls.tail.tail) n := by
  rcases ls with _ | ⟨x, _ | ⟨y, r⟩⟩
  · simp only [K, List.headD, List.tail, lt, rep_zero, cons_false_blank]
  · simp only [K, List.headD, List.tail, lt, rep_zero, cons_false_blank]
  · rfl

/-- **The macro step**: whenever `next` gives the next pass, the machine gets there, for every block length and every
tape to the left. -/
theorem next_sound {ls ls' : List Nat} {n n' : Nat} (h : next ls n = some (ls', n')) :
    Reaches (K ls n) (K ls' n') := by
  dsimp only [next] at h
  split at h
  · rename_i h3; cases h; subst h3; rw [K_pad1]; exact kA0 _ _
  split at h
  · rename_i _ h63; cases h
    obtain ⟨t, rfl⟩ : ∃ t, n = 6 * (t + 1) + 3 := ⟨(n - 9) / 6, by omega⟩
    rw [show (6 * (t + 1) + 3 - 9) / 6 = t by omega, K_pad1]; exact kA _ _ _
  split at h
  · rename_i _ _ h60; cases h
    obtain ⟨t, rfl⟩ : ∃ t, n = 6 * (t + 1) := ⟨(n - 6) / 6, by omega⟩
    rw [show (6 * (t + 1) - 6) / 6 = t by omega, K_pad1]; exact kB _ _ _
  split at h
  · rename_i _ _ _ h61; cases h
    obtain ⟨t, rfl⟩ : ∃ t, n = 6 * t + 1 := ⟨n / 6, by omega⟩
    rw [show (6 * t + 1) / 6 = t by omega, K_pad2]; exact kC _ _ _ _
  split at h
  · rename_i _ _ _ _ h64; cases h
    obtain ⟨t, rfl⟩ : ∃ t, n = 6 * t + 4 := ⟨n / 6, by omega⟩
    rw [show (6 * t + 4) / 6 = t by omega, K_pad2]; exact kD _ _ _ _
  cases h

/-- The macro run reaches a configuration that halts: then the machine halts. -/
theorem halts_of_reaches {c : Config} {ls : List Nat} (h : Reaches c (K ls 0)) : TM.Halts trans c := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨c', h₁, h₂⟩ := K_zero_halts ls
  exact ⟨n + 6, c', steps_seq trans hn h₁, h₂⟩

/-- From blank tape: 13 steps to the first pass configuration `1^2 0 1 B> 1 0 1`, then three passes by `next`
(`1^2 0 1^2`, `1^2 0 1^5`, `1^4 0 1^7`, `1^10 0 1^3`); the last block 3 is the recursive case. -/
theorem blank_passes : Reaches init (K [10] 2) := by
  have h₀ : steps 13 init = some (K [2] 1) := by
    have h := blank_reaches trans (q := St.A) (n := 13) (c := ⟨[true, false, true, true], [true, false, true], .B⟩)
      (by decide +kernel)
    refine h.trans ?_
    simp only [K, lt, FCfg.toCfg, app, rep, cons_false_blank]
  exact (reaches_of h₀).trans <| (next_sound (ls := [2]) (n := 1) rfl).trans <|
    (next_sound (ls := [2]) (n := 4) rfl).trans (next_sound (ls := [4]) (n := 6) rfl)

end BB6c
