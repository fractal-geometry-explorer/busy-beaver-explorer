import Machine

/-!
# 1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE: the machine is a block-list system

At each visit of the right end in state B (`B> 0^inf`) the tape is a list of blocks of 1s separated by single 0s.
`enc ns` is that tape, the list written nearest block first (the last block z first, the front block last; a block
may be empty, two 0s in a row).  `sweep` is one visit-to-visit sweep on the list:

* the sweep goes left over the last block z in state C, then over every further block in state D (`scanC`); it passes
  a block that leaves it in state C, i.e. z if z is even and every later odd block, and it stops at the first one
  that does not (z if z is odd, else the first even block e, a target);
* there it fills the separator left of e (`fill`): if the block x left of e is not empty, x loses one 1 and the head
  turns right; if x is empty (or e is the front block) a new block of two 1s appears and e loses two;
* on the way back (`casc`) every block it crosses gives three 1s to the block before it, plus one from its separator,
  so the blocks it passed keep their lengths, the target e gains 4 (or z gains 2) and z loses 2.

Theorem `visit`: whenever `sweep ns = some ns'`, the machine goes from `enc ns` to `enc ns'` (in B at the right end)
in at least one step, for every list.  Theorem `nonhalt_of_orbit`: if the orbit of `[1]` under `sweep` is defined
forever, the machine does not halt from blank tape.  `sweep` is `none` exactly where the machine halts (F reads 0)
or for shapes that cannot occur; so the question of the machine is the question of the block-list system.

Written by hand (not generated); see `py/blocks.py` for the same rule in Python.
-/

namespace H41677

open TM

/-- `n` cells holding 1. -/
def ones (n : Nat) (s : Tape) : Tape := rep n [true] s

/-- A list of blocks, nearest first, each followed (away from the head) by one 0; the end is blank. -/
def enc : List Nat → Tape
  | [] => blank
  | n :: ns => ones n (cons false (enc ns))

/-- The cascade on the way back: the head in A on the separator right of the first block of `ls` (blocks behind
the head, nearest first), `os` the blocks still ahead (nearest first). -/
def casc : List Nat → List Nat → Option (List Nat)
  | [], _ => none
  | l :: ls, [] => some ((l + 1) :: ls)
  | l :: ls, n :: os =>
    if 3 ≤ n then casc ((n - 3) :: (l + 3) :: ls) os
    else if n = 2 ∧ os = [] then some (0 :: (l + 3) :: ls) else none

/-- The turn at the target `e`: the head in D on the separator left of `e`, `ns` the blocks left of it (nearest
first), `os` the blocks right of it (nearest first). -/
def fill (ns : List Nat) (e : Nat) (os : List Nat) : Option (List Nat) :=
  match ns with
  | (x + 1) :: ns' => casc ((e + 1) :: x :: ns') os
  | _ =>
    if e = 0 then none
    else if e = 1 then (if os = [] then some (0 :: 2 :: ns.tail) else none)
    else casc ((e - 2) :: 2 :: ns.tail) os

/-- The sweep to the left: the head in C on the separator right of the first block of `ns`. -/
def scanC : List Nat → List Nat → Option (List Nat)
  | [], _ => none
  | n :: ns, os => if n % 2 = 1 then scanC ns (n :: os) else fill ns n os

/-- One visit-to-visit sweep of the block list (nearest block first). -/
def sweep : List Nat → Option (List Nat)
  | [] => none
  | z :: ns => if z = 0 then scanC ns [] else if z % 2 = 0 then scanC ns [z] else fill ns z []

/-! ## Tape identities -/

theorem ones_zero (s : Tape) : ones 0 s = s := rfl
theorem ones_succ (n : Nat) (s : Tape) : ones (n + 1) s = cons true (ones n s) := rfl

theorem ones_add (a b : Nat) (s : Tape) : ones a (ones b s) = ones (a + b) s := by
  unfold ones; rw [rep_add]

theorem rep2 (b : Nat) (s : Tape) : rep b [true, true] s = ones (2 * b) s := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show cons true (cons true (rep b [true, true] s)) = ones (2 * (b + 1)) s
    rw [ih, show 2 * (b + 1) = 2 * b + 1 + 1 by omega]
    rfl

theorem ones_cons_true (n : Nat) (s : Tape) : ones n (cons true s) = cons true (ones n s) := by
  rw [show cons true s = ones 1 s from rfl, ones_add, ← ones_succ]

theorem ones_odd (b : Nat) (s : Tape) : ones (2 * b + 1) s = cons true (rep b [true, true] s) := by
  rw [rep2]; rfl

theorem ones_even (b : Nat) (s : Tape) : ones (2 * b) s = rep b [true, true] s := (rep2 b s).symm

theorem enc_cons (n : Nat) (ns : List Nat) : enc (n :: ns) = ones n (cons false (enc ns)) := rfl

/-! ## The pieces of a sweep -/

theorem cC : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .C⟩ =
    some ⟨L, app [true] (app [true, true] R), .C⟩ := fun _ _ => rfl
theorem cD : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .D⟩ =
    some ⟨L, app [true] (app [true, true] R), .D⟩ := fun _ _ => rfl
theorem cA : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [true] L), R, .A⟩ :=
  fun _ _ => rfl

/-- A in a run of 1s moves to its far end. -/
theorem crossA (k : Nat) (L R : Tape) : steps k ⟨L, ones k R, .A⟩ = some ⟨ones k L, R, .A⟩ := by
  have h := cross_r trans cA k L R
  rw [Nat.mul_one] at h
  exact h

/-- Passing an odd block to the left, C on the separator right of it to C on the separator left of it. -/
theorem passC_odd (b : Nat) (L R : Tape) :
    steps (2 * b + 2) ⟨ones (2 * b + 1) (cons false L), cons false R, .C⟩ =
      some ⟨L, cons false (ones (2 * b + 1) (cons false R)), .C⟩ := by
  rw [ones_odd, ones_odd]
  have h0 : steps 1 ⟨cons true (rep b [true, true] (cons false L)), cons false R, .C⟩ =
      some ⟨rep b [true, true] (cons false L), cons true (cons false R), .D⟩ := rfl
  have h1 : steps (b * 2) ⟨rep b [true, true] (cons false L), cons true (cons false R), .D⟩ =
      some ⟨cons false L, cons true (rep b [true, true] (cons false R)), .D⟩ :=
    cross_l trans cD b (cons false L) (cons false R)
  have h2 : steps 1 ⟨cons false L, cons true (rep b [true, true] (cons false R)), .D⟩ =
      some ⟨L, cons false (cons true (rep b [true, true] (cons false R))), .C⟩ := rfl
  exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

/-- Reaching an even block: C on the separator right of it to D on the separator left of it. -/
theorem passC_even (b : Nat) (L R : Tape) :
    ∃ n, steps (n + 1) ⟨ones (2 * b) (cons false L), cons false R, .C⟩ =
      some ⟨L, cons false (ones (2 * b) (cons false R)), .D⟩ := by
  cases b with
  | zero => exact ⟨0, rfl⟩
  | succ b =>
    refine ⟨2 * b + 2, ?_⟩
    rw [show 2 * (b + 1) = 2 * b + 1 + 1 by omega, ones_succ, ones_odd, ones_succ, ones_odd]
    have h0 : steps 2 ⟨cons true (cons true (rep b [true, true] (cons false L))), cons false R, .C⟩ =
        some ⟨rep b [true, true] (cons false L), cons true (cons true (cons false R)), .C⟩ := rfl
    have h1 : steps (b * 2) ⟨rep b [true, true] (cons false L), cons true (cons true (cons false R)), .C⟩ =
        some ⟨cons false L, cons true (rep b [true, true] (cons true (cons false R))), .C⟩ :=
      cross_l trans cC b (cons false L) (cons true (cons false R))
    have h2 : steps 1 ⟨cons false L, cons true (rep b [true, true] (cons true (cons false R))), .C⟩ =
        some ⟨L, cons false (cons true (rep b [true, true] (cons true (cons false R)))), .D⟩ := rfl
    have e : rep b [true, true] (cons true (cons false R)) = cons true (rep b [true, true] (cons false R)) := by
      rw [rep2, rep2, ones_cons_true]
    rw [e] at h1 h2
    exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

/-! ## Positions -/

/-- C on the separator right of the first block of `ns`, `os` to the right. -/
def PC (ns os : List Nat) : Config := ⟨enc ns, cons false (enc os), .C⟩
/-- D on the separator left of block `e`. -/
def PD (ns : List Nat) (e : Nat) (os : List Nat) : Config := ⟨enc ns, cons false (enc (e :: os)), .D⟩
/-- A on the separator right of the first block of `ls`. -/
def PA (ls os : List Nat) : Config := ⟨enc ls, cons false (enc os), .A⟩
/-- A visit: B at the right end. -/
def V (ns : List Nat) : Config := ⟨enc ns, blank, .B⟩

/-- `c` reaches `c'` in at least one step. -/
def Reach (c c' : Config) : Prop := ∃ n, steps (n + 1) c = some c'

theorem reach_trans {a b c : Config} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + (m + 1), steps_congr trans (by omega) (steps_seq trans hn hm)⟩

theorem cascade (os : List Nat) : ∀ (ls : List Nat) (r : List Nat), casc ls os = some r → Reach (PA ls os) (V r) := by
  induction os with
  | nil =>
    intro ls r h
    cases ls with
    | nil => simp [casc] at h
    | cons l ls =>
      simp only [casc, Option.some.injEq] at h
      subst h
      refine ⟨0, ?_⟩
      show steps 1 ⟨ones l (cons false (enc ls)), cons false blank, .A⟩ =
        some ⟨ones (l + 1) (cons false (enc ls)), blank, .B⟩
      rw [cons_false_blank]
      rfl
  | cons n os ih =>
    intro ls r h
    cases ls with
    | nil => simp [casc] at h
    | cons l ls =>
      unfold casc at h
      by_cases h3 : 3 ≤ n
      · simp only [h3, ↓reduceIte] at h
        obtain ⟨b, rfl⟩ : ∃ b, n = b + 3 := ⟨n - 3, by omega⟩
        have hb : b + 3 - 3 = b := by omega
        rw [hb] at h
        refine reach_trans ?_ (ih _ _ h)
        refine ⟨b + 3, ?_⟩
        show steps (b + 3 + 1) ⟨enc (l :: ls), cons false (ones (b + 3) (cons false (enc os))), .A⟩ =
          some ⟨ones b (cons false (ones (l + 3) (cons false (enc ls)))), cons false (enc os), .A⟩
        have h0 : steps 4 ⟨enc (l :: ls), cons false (ones (b + 3) (cons false (enc os))), .A⟩ =
            some ⟨cons false (ones 3 (enc (l :: ls))), ones b (cons false (enc os)), .A⟩ := rfl
        have h1 := crossA b (cons false (ones 3 (enc (l :: ls)))) (cons false (enc os))
        have e : ones 3 (enc (l :: ls)) = ones (l + 3) (cons false (enc ls)) := by
          rw [enc_cons, ones_add, Nat.add_comm]
        rw [e] at h0 h1
        exact steps_congr trans (by omega) (steps_seq trans h0 h1)
      · simp only [h3, ↓reduceIte] at h
        by_cases h2 : n = 2 ∧ os = []
        · obtain ⟨rfl, rfl⟩ := h2
          simp only [Option.some.injEq, and_self, ↓reduceIte] at h
          subst h
          refine ⟨3, ?_⟩
          show steps 4 ⟨enc (l :: ls), cons false (ones 2 (cons false blank)), .A⟩ =
            some ⟨cons false (ones (l + 3) (cons false (enc ls))), blank, .B⟩
          have e : ones (l + 3) (cons false (enc ls)) = ones 3 (enc (l :: ls)) := by
            rw [enc_cons, ones_add, Nat.add_comm]
          rw [e]
          rfl
        · simp only [h2, ↓reduceIte] at h
          cases h

theorem fill_reach (ns : List Nat) (e : Nat) (os : List Nat) (r : List Nat) (h : fill ns e os = some r) :
    Reach (PD ns e os) (V r) := by
  unfold fill at h
  split at h
  · -- x + 1 :: ns'
    rename_i x ns'
    refine reach_trans ?_ (cascade os _ r h)
    refine ⟨e + 2, ?_⟩
    show steps (e + 2 + 1) ⟨ones (x + 1) (cons false (enc ns')), cons false (ones e (cons false (enc os))), .D⟩ =
      some ⟨ones (e + 1) (cons false (ones x (cons false (enc ns')))), cons false (enc os), .A⟩
    have h0 : steps 2 ⟨ones (x + 1) (cons false (enc ns')), cons false (ones e (cons false (enc os))), .D⟩ =
        some ⟨cons false (ones x (cons false (enc ns'))), ones (e + 1) (cons false (enc os)), .A⟩ := rfl
    have h1 := crossA (e + 1) (cons false (ones x (cons false (enc ns')))) (cons false (enc os))
    exact steps_congr trans (by omega) (steps_seq trans h0 h1)
  · -- x = 0 or the front
    rename_i hx
    have hl : enc ns = cons false (enc ns.tail) := by
      cases ns with
      | nil => exact cons_false_blank.symm
      | cons x ns' =>
        cases x with
        | zero => rfl
        | succ x => exact absurd rfl (hx x ns')
    have hP : PD ns e os = ⟨cons false (enc ns.tail), cons false (enc (e :: os)), .D⟩ := by
      unfold PD; rw [hl]
    rw [hP]
    by_cases he0 : e = 0
    · simp only [he0, ↓reduceIte] at h; cases h
    simp only [he0, ↓reduceIte] at h
    by_cases he1 : e = 1
    · simp only [he1, ↓reduceIte] at h
      subst he1
      by_cases ho : os = []
      · simp only [ho, ↓reduceIte] at h
        subst ho
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨4, ?_⟩
        show steps 5 ⟨cons false (enc ns.tail), cons false (ones 1 (cons false blank)), .D⟩ =
          some ⟨cons false (ones 2 (cons false (enc ns.tail))), blank, .B⟩
        rfl
      · simp only [ho, ↓reduceIte] at h; cases h
    simp only [he1, ↓reduceIte] at h
    obtain ⟨b, rfl⟩ : ∃ b, e = b + 2 := ⟨e - 2, by omega⟩
    have hb : b + 2 - 2 = b := by omega
    rw [hb] at h
    refine reach_trans ?_ (cascade os _ r h)
    refine ⟨b + 4, ?_⟩
    show steps (b + 4 + 1) ⟨cons false (enc ns.tail), cons false (ones (b + 2) (cons false (enc os))), .D⟩ =
      some ⟨ones b (cons false (ones 2 (cons false (enc ns.tail)))), cons false (enc os), .A⟩
    have h0 : steps 5 ⟨cons false (enc ns.tail), cons false (ones (b + 2) (cons false (enc os))), .D⟩ =
        some ⟨cons false (ones 2 (cons false (enc ns.tail))), ones b (cons false (enc os)), .A⟩ := rfl
    have h1 := crossA b (cons false (ones 2 (cons false (enc ns.tail)))) (cons false (enc os))
    exact steps_congr trans (by omega) (steps_seq trans h0 h1)

theorem scan_reach (ns : List Nat) : ∀ (os r : List Nat), scanC ns os = some r → Reach (PC ns os) (V r) := by
  induction ns with
  | nil => intro os r h; simp [scanC] at h
  | cons n ns ih =>
    intro os r h
    unfold scanC at h
    by_cases hn : n % 2 = 1
    · simp only [hn, ↓reduceIte] at h
      refine reach_trans ?_ (ih _ _ h)
      obtain ⟨b, rfl⟩ : ∃ b, n = 2 * b + 1 := ⟨n / 2, by omega⟩
      exact ⟨2 * b + 1, passC_odd b (enc ns) (enc os)⟩
    · simp only [hn, ↓reduceIte] at h
      refine reach_trans ?_ (fill_reach ns n os r h)
      obtain ⟨b, rfl⟩ : ∃ b, n = 2 * b := ⟨n / 2, by omega⟩
      exact passC_even b (enc ns) (enc os)

/-- **One visit to the next.** For every block list, `sweep` gives the tape at the next visit of the right end. -/
theorem visit (ns r : List Nat) (h : sweep ns = some r) : Reach (V ns) (V r) := by
  cases ns with
  | nil => simp [sweep] at h
  | cons z ns =>
    simp only [sweep] at h
    by_cases hz : z = 0
    · simp only [hz, ↓reduceIte] at h
      subst hz
      refine reach_trans ⟨0, ?_⟩ (scan_reach ns [] r h)
      have h0 : steps 1 ⟨cons false (enc ns), blank, .B⟩ = some ⟨enc ns, cons false (cons false blank), .C⟩ := rfl
      rw [cons_false_blank] at h0
      exact h0
    simp only [hz, ↓reduceIte] at h
    by_cases he : z % 2 = 0
    · simp only [he, ↓reduceIte] at h
      refine reach_trans ?_ (scan_reach ns [z] r h)
      obtain ⟨b, rfl⟩ : ∃ b, z = 2 * b + 2 := ⟨z / 2 - 1, by omega⟩
      refine ⟨2 * b + 2, ?_⟩
      show steps (2 * b + 2 + 1) ⟨ones (2 * b + 2) (cons false (enc ns)), blank, .B⟩ =
        some ⟨enc ns, cons false (ones (2 * b + 2) (cons false blank)), .C⟩
      rw [show 2 * b + 2 = 2 * b + 1 + 1 by omega, ones_succ, ones_odd, ones_succ, ones_odd]
      have h0 : steps 2 ⟨cons true (cons true (rep b [true, true] (cons false (enc ns)))), blank, .B⟩ =
          some ⟨rep b [true, true] (cons false (enc ns)), cons true (cons true (cons false blank)), .D⟩ := rfl
      have h1 : steps (b * 2) ⟨rep b [true, true] (cons false (enc ns)), cons true (cons true (cons false blank)), .D⟩ =
          some ⟨cons false (enc ns), cons true (rep b [true, true] (cons true (cons false blank))), .D⟩ :=
        cross_l trans cD b (cons false (enc ns)) (cons true (cons false blank))
      have h2 : steps 1 ⟨cons false (enc ns), cons true (rep b [true, true] (cons true (cons false blank))), .D⟩ =
          some ⟨enc ns, cons false (cons true (rep b [true, true] (cons true (cons false blank)))), .C⟩ := rfl
      have e : rep b [true, true] (cons true (cons false blank)) =
          cons true (rep b [true, true] (cons false blank)) := by
        rw [rep2, rep2, ones_cons_true]
      rw [e] at h1 h2
      exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))
    · simp only [he, ↓reduceIte] at h
      refine reach_trans ?_ (fill_reach ns z [] r h)
      obtain ⟨b, rfl⟩ : ∃ b, z = 2 * b + 1 := ⟨z / 2, by omega⟩
      refine ⟨2 * b + 1, ?_⟩
      show steps (2 * b + 1 + 1) ⟨ones (2 * b + 1) (cons false (enc ns)), blank, .B⟩ =
        some ⟨enc ns, cons false (ones (2 * b + 1) (cons false blank)), .D⟩
      rw [ones_odd, ones_odd]
      have h0 : steps 1 ⟨cons true (rep b [true, true] (cons false (enc ns))), blank, .B⟩ =
          some ⟨rep b [true, true] (cons false (enc ns)), cons true (cons false blank), .C⟩ := rfl
      have h1 : steps (b * 2) ⟨rep b [true, true] (cons false (enc ns)), cons true (cons false blank), .C⟩ =
          some ⟨cons false (enc ns), cons true (rep b [true, true] (cons false blank)), .C⟩ :=
        cross_l trans cC b (cons false (enc ns)) (cons false blank)
      have h2 : steps 1 ⟨cons false (enc ns), cons true (rep b [true, true] (cons false blank)), .C⟩ =
          some ⟨enc ns, cons false (cons true (rep b [true, true] (cons false blank))), .D⟩ := rfl
      exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

/-- The orbit of the block list `[1]` (the tape after the first step) under `sweep`. -/
def orbit : Nat → Option (List Nat)
  | 0 => some [1]
  | k + 1 => (orbit k).bind sweep

theorem orbit_reach : ∀ k ns, orbit k = some ns → ∃ n, k ≤ n ∧ steps n init = some (V ns) := by
  intro k
  induction k with
  | zero =>
    intro ns h
    simp only [orbit, Option.some.injEq] at h
    subst h
    refine ⟨1, by omega, ?_⟩
    show steps 1 ⟨blank, blank, .A⟩ = some ⟨cons true (cons false blank), blank, .B⟩
    rw [cons_false_blank]
    rfl
  | succ k ih =>
    intro ns h
    simp only [orbit] at h
    cases hk : orbit k with
    | none => rw [hk] at h; cases h
    | some ms =>
      rw [hk] at h
      obtain ⟨n, hn, hs⟩ := ih ms hk
      obtain ⟨m, hm⟩ := visit ms ns h
      exact ⟨n + (m + 1), by omega, steps_seq trans hs hm⟩

/-- **The reduction.** If the block-list orbit of `[1]` never reaches `none`, the machine never halts. -/
theorem nonhalt_of_orbit (h : ∀ k, orbit k ≠ none) : ¬ HaltsFromBlank := by
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun n => ∃ c, steps n init = some c)
  · intro n
    cases hk : orbit n with
    | none => exact absurd hk (h n)
    | some ns =>
      obtain ⟨m, hm, hs⟩ := orbit_reach n ns hk
      exact ⟨m, hm, V ns, hs⟩
  · intro m hm; exact hm

end H41677
