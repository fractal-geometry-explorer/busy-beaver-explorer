import Drain

/-!
# 1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD: bounded runs with the drain as a jump

The run-length simulator of `TM/RLE.lean` with one jump: in state A at the left end (all cells left of the head
blank), the right part is read as `0 (10)^X` and a bit list (`parseE`), and the longest run of regular decrements
(`maxReg`, checked by `regN`) is made at once by `drain_reach`.  Everything else (the exceptional visits, where a
block is empty or the counter is zero and the blocks are rewritten) is simulated by crossings and single steps.
-/

namespace H180268

open TM

/-! ## Reading the counter off the runs -/

/-- All cells blank. -/
def allZero : Side → Bool
  | [] => true
  | (w, _) :: s => w.all (· = false) && allZero s

theorem app_zeros (w : List Bool) (h : w.all (· = false) = true) : app w blank = blank := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp at h
    obtain ⟨rfl, h2⟩ := h
    show cons false (app w blank) = blank
    rw [ih (by simpa using h2)]
    exact cons_false_blank

theorem rep_zeros (n : Nat) (w : List Bool) (h : w.all (· = false) = true) : rep n w blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih, app_zeros w h]

theorem allZero_spec : ∀ s : Side, allZero s = true → den s = blank
  | [], _ => rfl
  | (w, n) :: s, h => by
    simp [allZero] at h
    simp only [den_cons]
    rw [allZero_spec s (by simpa using h.2)]
    exact rep_zeros n w (by simpa using h.1)

/-- `1 (01)^n = (10)^n 1`. -/
theorem one_rep01 (n : Nat) (X : Tape) : cons true (rep n [false, true] X) = rep n [true, false] (cons true X) :=
  rep_rotate n [true] [false, true] [true, false] rfl X

/-- Copies of `10` at the front of a side (as many as it finds within the fuel). -/
def munch : Nat → Side → Nat × Side
  | 0, s => (0, s)
  | _ + 1, [] => (0, [])
  | f + 1, (w, n) :: s =>
    if n = 0 ∨ w = [] then munch f s
    else if w = [true, false] then
      let p := munch f s
      (n + p.1, p.2)
    else
      match w, n, s with
      | [true], 1, ([false, true], m) :: s' =>
        let p := munch f (([true], 1) :: s')
        (m + p.1, p.2)
      | w, n, s =>
        let q := pop ((w, n) :: s)
        if q.1 then
          let q2 := pop q.2
          if q2.1 then (0, (w, n) :: s)
          else
            let p := munch f q2.2
            (1 + p.1, p.2)
        else (0, (w, n) :: s)

theorem munch_spec : ∀ (f : Nat) (s : Side), den s = rep (munch f s).1 [true, false] (den (munch f s).2)
  | 0, s => rfl
  | _ + 1, [] => rfl
  | f + 1, (w, n) :: s => by
    simp only [munch]
    split
    · rename_i hz
      rw [← munch_spec f s]
      rcases hz with hz | hz
      · subst hz; rfl
      · subst hz; simp [rep_nil_word]
    split
    · rename_i hw
      subst hw
      simp only [den_cons]
      rw [munch_spec f s, rep_add]
    · split
      · rw [rep_add, ← munch_spec f _]
        show cons true (den (([false, true], _) :: _)) = _
        rw [den_cons, one_rep01]; rfl
      · have hp := den_pop ((w, n) :: s)
        split
        · rename_i h1
          have hp2 := den_pop (pop ((w, n) :: s)).2
          split
          · rfl
          · rename_i h2
            simp at h2
            rw [rep_add, ← munch_spec f _, hp, h1, hp2, h2]; rfl
        · rfl

/-- The bits and their blocks, to the end of the side. -/
def pBits : Nat → Side → Option (List (Bool × Nat))
  | 0, _ => none
  | f + 1, s =>
    if allZero s then some [] else
    let q := pop s
    let p := munch (4 * q.2.length + 64) q.2
    (pBits f p.2).map ((q.1, p.1) :: ·)

theorem pBits_spec : ∀ (f : Nat) (s : Side) (bl : List (Bool × Nat)), pBits f s = some bl → den s = encB bl blank
  | 0, _, _, h => by simp [pBits] at h
  | f + 1, s, bl, h => by
    simp only [pBits] at h
    split at h
    · rename_i hz; simp at h; subst h; exact allZero_spec s hz
    · cases e : pBits f (munch (4 * (pop s).2.length + 64) (pop s).2).2 with
      | none => rw [e] at h; cases h
      | some bl' =>
        rw [e] at h
        simp at h; subst h
        rw [den_pop s, munch_spec (4 * (pop s).2.length + 64) (pop s).2, pBits_spec f _ bl' e]
        rfl

/-- The right part at an event: `0 (10)^X` and the bit list. -/
def parseE (s : Side) : Option (Nat × List (Bool × Nat)) :=
  let q := pop s
  if q.1 then none else
  let p := munch (4 * q.2.length + 64) q.2
  (pBits (2 * p.2.length + 64) p.2).map (fun bl => (p.1, bl))

theorem parseE_spec (s : Side) (X : Nat) (bl : List (Bool × Nat)) (h : parseE s = some (X, bl)) :
    den s = cons false (rep X [true, false] (encB bl blank)) := by
  unfold parseE at h
  simp only at h
  split at h
  · cases h
  · rename_i h1
    simp at h1
    cases e : pBits (2 * (munch (4 * (pop s).2.length + 64) (pop s).2).2.length + 64)
        (munch (4 * (pop s).2.length + 64) (pop s).2).2 with
    | none => rw [e] at h; cases h
    | some bl' =>
      rw [e] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      rw [den_pop s, h1, munch_spec (4 * (pop s).2.length + 64) (pop s).2, pBits_spec _ _ bl' e]

/-! ## Writing it back -/

def encBS : List (Bool × Nat) → Side
  | [] => []
  | (b, y) :: bl => ([b], 1) :: rcons [true, false] y (encBS bl)

theorem den_encBS : ∀ bl, den (encBS bl) = encB bl blank
  | [] => rfl
  | (b, y) :: bl => by simp only [encBS, den_cons, den_rcons, den_encBS bl]; rfl

def encE (X : Nat) (bl : List (Bool × Nat)) : Side := ([false], 1) :: rcons [true, false] X (encBS bl)

theorem den_encE (X : Nat) (bl : List (Bool × Nat)) :
    den (encE X bl) = cons false (rep X [true, false] (encB bl blank)) := by
  simp only [encE, den_cons, den_rcons, den_encBS]; rfl

/-! ## The jump -/

/-- At an event, all regular decrements up to the first exceptional one. -/
def jumpD (c : RCfg St) : Option (RCfg St × Nat) :=
  match c.st with
  | .A =>
    if allZero c.l then
      match parseE c.r with
      | some (X, bl) =>
        let n := maxReg bl
        if 0 < n ∧ regN bl n = true then some (⟨[], encE (X + 2 * n) (drainL bl n), .A⟩, lowN n X) else none
      | none => none
    else none
  | _ => none

theorem jumpD_ok : JumpOK trans jumpD := by
  intro c c' n h
  obtain ⟨L, R, q⟩ := c
  unfold jumpD at h
  simp only at h
  match q, h with
  | .A, h =>
    simp only at h
    split at h
    · rename_i hl
      cases e : parseE R with
      | none => rw [e] at h; cases h
      | some p =>
        obtain ⟨X, bl⟩ := p
        rw [e] at h
        simp only at h
        split at h
        · rename_i hr
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          have := drain_reach X bl blank (maxReg bl) hr.2
          unfold RCfg.toCfg
          simp only
          rw [allZero_spec L hl, parseE_spec R X bl e, den_encE, den_nil]
          exact this
        · cases h
    · cases h

/-- The words literal cells are folded into. -/
def words : List (List Bool) := [[true, false], [false, true]]

def start : RCfg St := ⟨[], [], .A⟩

theorem bound_of_run {N fuel : Nat} (h : TM.run trans words jumpD N fuel start 0 = true) :
    ∃ c, steps N init = some c :=
  TM.run_ok trans words jumpD_ok h

theorem bound_1e30 : ∃ c, steps (10 ^ 30) init = some c :=
  bound_of_run (fuel := 10 ^ 12) (by native_decide)

end H180268
