import Machine

/-!
# 1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF: the block machine

The tape is a row of blocks of 1s, each followed by one 0, with one *gap*: a place where two 0s stand side by side.
`enc [a, b, c]` is `1^a 0 1^b 0 1^c 0 0 0 ...` read outward from the head (nearest cell first), so `enc []` is blank
tape.  `gap b ls rs` is the configuration

    (blocks ls, reversed) 0 1^b 0 B>0 (blocks rs)

the head in state B on the second 0 of the gap, the block `b` just left of the gap, the blocks `ls` further left
(nearest first) and `rs` right of the gap (nearest first; the first of them may be empty).

* `round_gap`: one round moves the gap one cell left: `b + 3` loses two 1s and each neighbour gains one.
* `rounds_gap`: m rounds at once.
* `even_gap`: an even block `2m + 2` is used up: m + 1 rounds give half of it to each side, and the gap moves on to
  the block on the left (`b = 2`, `round2`).
* `odd_gap`: an odd block `2m + 1` keeps one 1 after m rounds; the gap closes (`dissolve`: `1 0 0` becomes
  `1 1 1`), D runs to the right end of the tape and starts a new gap there: the next sweep.
* `halt1`, `halt0`: the only ways to stop: an odd block with nothing at all left of it after its rounds
  (`gap 1 [] rs`), or an empty block at the gap (`gap 0 ls rs`).

`mstep` is the macro machine, block by block, and `mstep_sound` / `mstep_halt` say the machine follows it.
Everything is checked by Lean's kernel.
-/

namespace H141594

open TM

/-- Blocks of 1s, each followed by one 0, then blank tape (nearest block first). -/
def enc : List Nat → Tape
  | [] => blank
  | a :: ls => rep a [true] (cons false (enc ls))

/-- Add `k` to the nearest block (creating it at a blank end). -/
def addH (k : Nat) : List Nat → List Nat
  | [] => if k = 0 then [] else [k]
  | a :: ls => (a + k) :: ls

/-- The configuration at a gap: `(ls) 0 1^b 0 B>0 (rs)`. -/
def gap (b : Nat) (ls rs : List Nat) : Config :=
  ⟨cons false (rep b [true] (cons false (enc ls))), cons false (enc rs), .B⟩

theorem rep_ones (a k : Nat) (s : Tape) : rep k [true] (rep a [true] s) = rep (a + k) [true] s := by
  rw [← rep_add, Nat.add_comm]

theorem enc_addH (k : Nat) (ls : List Nat) : enc (addH k ls) = rep k [true] (enc ls) := by
  cases ls with
  | nil =>
    by_cases hk : k = 0
    · subst hk; rfl
    · simp only [addH, hk, ite_false, enc, cons_false_blank]
  | cons a ls => simp only [addH, enc, rep_ones]

theorem addH_addH (k m : Nat) (ls : List Nat) : addH m (addH k ls) = addH (k + m) ls := by
  cases ls with
  | nil =>
    by_cases hk : k = 0
    · subst hk; simp [addH]
    · have : k + m ≠ 0 := by omega
      simp [addH, hk]
  | cons a ls => simp [addH, Nat.add_assoc]

@[simp] theorem addH_zero (ls : List Nat) : addH 0 ls = ls := by
  cases ls <;> simp [addH]

theorem addH_ne_nil (k : Nat) (ls : List Nat) : addH (k + 1) ls ≠ [] := by
  cases ls <;> simp [addH]

/-! ## The rules on cells (written by `bbtools.symtm.prove`) -/

theorem round (b : Nat) (L R : Tape) :
    steps (2 * b + 11) ⟨cons false (rep (b + 3) [true] (cons false (L))), cons false (R), .B⟩ = some ⟨cons false (rep (b) [true] (cons true (cons false (cons true (L))))), cons false (cons true (R)), .B⟩ := by
  have h0 : steps 3 ⟨cons false (rep (b + 3) [true] (cons false (L))), cons false (R), .B⟩ = some ⟨rep (b + 1) [true] (cons false (L)), cons true (cons false (cons false (cons true (R)))), .F⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .F⟩ = some ⟨L, app [true] (app [true] R), .F⟩ := fun _ _ => rfl
  have h1 : steps ((b + 1) * 1) ⟨rep (b + 1) [true] (cons false (L)), cons true (cons false (cons false (cons true (R)))), .F⟩ = some ⟨cons false (L), cons true (rep (b + 1) [true] (cons false (cons false (cons true (R))))), .F⟩ :=
    cross_l trans c1 (b + 1) (cons false (L)) (cons false (cons false (cons true (R))))
  have h2 : steps 6 ⟨cons false (L), cons true (rep (b + 1) [true] (cons false (cons false (cons true (R))))), .F⟩ = some ⟨cons true (cons false (cons true (L))), rep (b) [true] (cons false (cons false (cons true (R)))), .D⟩ := rfl
  have c3 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .D⟩ = some ⟨app [] (app [true] L), R, .D⟩ := fun _ _ => rfl
  have h3 : steps ((b) * 1) ⟨cons true (cons false (cons true (L))), rep (b) [true] (cons false (cons false (cons true (R)))), .D⟩ = some ⟨rep (b) [true] (cons true (cons false (cons true (L)))), cons false (cons false (cons true (R))), .D⟩ :=
    cross_r trans c3 (b) (cons true (cons false (cons true (L)))) (cons false (cons false (cons true (R))))
  have h4 : steps 1 ⟨rep (b) [true] (cons true (cons false (cons true (L)))), cons false (cons false (cons true (R))), .D⟩ = some ⟨cons false (rep (b) [true] (cons true (cons false (cons true (L))))), cons false (cons true (R)), .B⟩ := rfl
  exact steps_congr trans (a := 3 + ((b + 1) * 1 + (6 + ((b) * 1 + (1))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

theorem round2 (L R : Tape) :
    steps 8 ⟨cons false (rep 2 [true] (cons false L)), cons false R, .B⟩ =
      some ⟨cons false (cons true L), cons false (cons false (cons true R)), .B⟩ := rfl

theorem dissolve (L R : Tape) :
    steps 8 ⟨cons false (cons true (cons false (cons true L))), cons false R, .B⟩ =
      some ⟨L, cons true (cons false (cons true (cons true (cons true R)))), .D⟩ := rfl

/-- D crosses a block and the 0 after it: `D>0 1^(x+1)` becomes `0 1^(x+1) D>` (here: from the 0 before it). -/
theorem dblock (x : Nat) (L R : Tape) :
    steps (x + 2) ⟨L, cons false (rep (x + 1) [true] R), .D⟩ = some ⟨rep (x + 1) [true] (cons false L), R, .D⟩ := by
  have h0 : steps 2 ⟨L, cons false (rep (x + 1) [true] R), .D⟩ = some ⟨cons true (cons false L), rep x [true] R, .D⟩ :=
    rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .D⟩ = some ⟨app [] (app [true] L), R, .D⟩ :=
    fun _ _ => rfl
  have h1 := cross_r trans c1 x (cons true (cons false L)) R
  simp only [app_nil, Nat.mul_one] at h1
  have h := steps_seq trans h0 h1
  rw [show rep x [true] (cons true (cons false L)) = rep (x + 1) [true] (cons false L) from
    rep_app_comm x [true] _] at h
  exact steps_congr trans (by omega) h

/-! ## The rules on blocks -/

theorem round_gap (b : Nat) (ls rs : List Nat) :
    steps (2 * b + 11) (gap (b + 3) ls rs) = some (gap (b + 1) (addH 1 ls) (addH 1 rs)) := by
  have h := round b (enc ls) (enc rs)
  have e1 : rep b [true] (cons true (cons false (cons true (enc ls)))) =
      rep (b + 1) [true] (cons false (enc (addH 1 ls))) := by
    rw [enc_addH]; exact rep_app_comm b [true] _
  have e2 : cons true (enc rs) = enc (addH 1 rs) := by rw [enc_addH]; rfl
  rw [e1, e2] at h
  exact h

/-- The cost of m rounds that end with the block at c. -/
def rcost (m c : Nat) : Nat := m * (2 * c + 2 * m + 7)

theorem rounds_gap (m b : Nat) (ls rs : List Nat) :
    steps (rcost m (b + 1)) (gap (b + 1 + 2 * m) ls rs) = some (gap (b + 1) (addH m ls) (addH m rs)) := by
  induction m generalizing ls rs with
  | zero => simp [rcost]
  | succ m ih =>
    have h1 := round_gap (b + 2 * m) ls rs
    have h2 := ih (addH 1 ls) (addH 1 rs)
    rw [addH_addH, addH_addH, Nat.add_comm 1 m] at h2
    have e : b + 1 + 2 * (m + 1) = b + 2 * m + 3 := by omega
    rw [e]
    refine steps_congr trans ?_ (steps_seq trans h1 (by rw [show b + 2 * m + 1 = b + 1 + 2 * m by omega]; exact h2))
    simp only [rcost, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

theorem even_gap (m : Nat) (ls rs : List Nat) {a : Nat} {l : List Nat} (h : addH (m + 1) ls = a :: l) :
    steps (rcost m 2 + 8) (gap (2 * m + 2) ls rs) = some (gap a l (0 :: addH (m + 1) rs)) := by
  have h1 := rounds_gap m 1 ls rs
  rw [show 1 + 1 + 2 * m = 2 * m + 2 by omega] at h1
  have h2 := round2 (enc (addH m ls)) (enc (addH m rs))
  have e1 : cons true (enc (addH m ls)) = enc (a :: l) := by
    rw [← h, ← addH_addH m 1, enc_addH 1 (addH m ls)]; rfl
  have e2 : cons true (enc (addH m rs)) = enc (addH (m + 1) rs) := by
    rw [← addH_addH m 1, enc_addH 1 (addH m rs)]; rfl
  rw [e1, e2] at h2
  exact steps_seq trans h1 h2

/-- The steps D takes to cross blocks from the 0 before them. -/
def runCost : List Nat → Nat
  | [] => 0
  | x :: rs => x + 1 + runCost rs

/-- D runs right across blocks of at least one 1 each, to the end of the tape. -/
theorem drun : ∀ (rs ls : List Nat), (∀ x ∈ rs, 1 ≤ x) →
    steps (runCost rs) ⟨enc ls, cons false (enc rs), .D⟩ = some ⟨enc (rs.reverseAux ls), cons false blank, .D⟩
  | [], ls, _ => rfl
  | x :: rs, ls, h => by
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by have := h x (by simp); omega⟩
    have h1 := dblock y (enc ls) (cons false (enc rs))
    have h2 := drun rs ((y + 1) :: ls) (fun z hz => h z (by simp [hz]))
    exact steps_congr trans (by simp only [runCost]) (steps_seq trans h1 h2)

/-- A new sweep: D at the right end of the tape writes the 0 that starts the new gap. -/
theorem sweep_start (n : Nat) (rest : List Nat) :
    steps 1 ⟨enc (n :: rest), cons false blank, .D⟩ = some (gap n rest []) := by
  show steps 1 _ = some ⟨_, cons false blank, _⟩
  rw [cons_false_blank]; rfl

theorem odd_gap (m : Nat) (ls rs : List Nat) {a : Nat} {l : List Nat} (h : addH m ls = (a + 1) :: l)
    (hr : ∀ x ∈ addH 3 (addH m rs), 1 ≤ x) {n : Nat} {rest : List Nat}
    (hn : (addH 3 (addH m rs)).reverseAux ((a + 1) :: l) = n :: rest) :
    steps (rcost m 1 + 8 + 1 + runCost (addH 3 (addH m rs)) + 1) (gap (2 * m + 1) ls rs) =
      some (gap n rest []) := by
  have h1 := rounds_gap m 0 ls rs
  rw [show 0 + 1 + 2 * m = 2 * m + 1 by omega, h] at h1
  have h2 := dissolve (rep a [true] (cons false (enc l))) (enc (addH m rs))
  have h3 : steps 1 ⟨rep a [true] (cons false (enc l)),
      cons true (cons false (cons true (cons true (cons true (enc (addH m rs)))))), .D⟩ =
      some ⟨enc ((a + 1) :: l), cons false (enc (addH 3 (addH m rs))), .D⟩ := by
    rw [enc_addH 3 (addH m rs)]; rfl
  have h4 := drun (addH 3 (addH m rs)) ((a + 1) :: l) hr
  rw [hn] at h4
  exact steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans h1 h2) h3) h4) (sweep_start n rest)

/-- An odd block with nothing left of it: the gap closes onto blank tape and the machine halts (`E` reads a 0). -/
theorem halt1 (rs : List Nat) : ∃ c, steps 11 (gap 1 [] rs) = some c ∧ step c = none := ⟨_, rfl, rfl⟩

/-- An empty block at the gap: three 0s in a row, and `E` reads a 0. -/
theorem halt0 (ls rs : List Nat) : ∃ c, steps 2 (gap 0 ls rs) = some c ∧ step c = none := ⟨_, rfl, rfl⟩

/-! ## The macro machine -/

/-- A macro configuration: a gap, a halt, or a case the rules do not cover. -/
inductive MS where
  | gap (b : Nat) (ls rs : List Nat)
  | halt
  | stuck
  deriving DecidableEq, Repr

/-- One block at the gap.  Even `b`: half to each side, the gap moves on left.  Odd `b`: the gap closes after
`b / 2` rounds and the next sweep starts at the right end. -/
def mstep (b : Nat) (ls rs : List Nat) : MS :=
  if b = 0 then .halt
  else if b % 2 = 0 then
    match addH (b / 2) ls with
    | a :: l => .gap a l (0 :: addH (b / 2) rs)
    | [] => .stuck
  else
    match addH (b / 2) ls with
    | [] => .halt
    | 0 :: _ => .stuck
    | (a + 1) :: l =>
      if (addH 3 (addH (b / 2) rs)).all (fun x => decide (1 ≤ x)) then
        match (addH 3 (addH (b / 2) rs)).reverseAux ((a + 1) :: l) with
        | n :: rest => .gap n rest []
        | [] => .stuck
      else .stuck

/-- The machine steps one macro step takes. -/
def mcost (b : Nat) (rs : List Nat) : Nat :=
  if b % 2 = 0 then rcost (b / 2 - 1) 2 + 8
  else rcost (b / 2) 1 + 8 + 1 + runCost (addH 3 (addH (b / 2) rs)) + 1

theorem mstep_sound {b : Nat} {ls rs : List Nat} {b' : Nat} {ls' rs' : List Nat}
    (h : mstep b ls rs = .gap b' ls' rs') : steps (mcost b rs) (gap b ls rs) = some (gap b' ls' rs') := by
  unfold mstep at h
  split at h
  · cases h
  rename_i hb
  split at h
  · rename_i he
    obtain ⟨m, rfl⟩ : ∃ m, b = 2 * m + 2 := ⟨b / 2 - 1, by omega⟩
    have e : (2 * m + 2) / 2 = m + 1 := by omega
    rw [e] at h
    split at h
    · rename_i a l hal
      cases h
      have := even_gap m ls rs hal
      simpa [mcost, show (2 * m + 2) % 2 = 0 by omega, e] using this
    · cases h
  · rename_i ho
    obtain ⟨m, rfl⟩ : ∃ m, b = 2 * m + 1 := ⟨b / 2, by omega⟩
    have e : (2 * m + 1) / 2 = m := by omega
    rw [e] at h
    split at h
    · cases h
    · cases h
    · rename_i a l hal
      split at h
      · rename_i hall
        split at h
        · rename_i n rest hn
          cases h
          have hr : ∀ x ∈ addH 3 (addH m rs), 1 ≤ x := by
            intro x hx; simpa using List.all_eq_true.mp hall x hx
          have := odd_gap m ls rs hal hr hn
          simpa [mcost, show (2 * m + 1) % 2 = 1 by omega, e] using this
        · cases h
      · cases h

theorem mstep_halt {b : Nat} {ls rs : List Nat} (h : mstep b ls rs = .halt) :
    ∃ n c, steps n (gap b ls rs) = some c ∧ step c = none := by
  unfold mstep at h
  split at h
  · rename_i hb; subst hb; exact ⟨2, halt0 ls rs⟩
  split at h
  · split at h <;> cases h
  · split at h
    · rename_i hal
      have hm : b / 2 = 0 := by
        rcases Nat.eq_zero_or_pos (b / 2) with h0 | h0
        · exact h0
        · exact absurd hal (by rw [show b / 2 = (b / 2 - 1) + 1 by omega]; exact addH_ne_nil _ _)
      rw [hm, addH_zero] at hal
      subst hal
      rw [show b = 1 by omega]
      exact ⟨11, halt1 rs⟩
    · cases h
    · split at h
      · split at h <;> cases h
      · cases h

end H141594
