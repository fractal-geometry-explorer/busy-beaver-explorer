import Sim

/-!
# 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE: the simulator with jumps, and its soundness

At a visit the simulator rewrites the tape left of the head in one phase (`canonL`: every run of 110 or 101 as a
run of 011 and a few cells), reads the zone at its end (`parseZone`), moves to the coordinates of `Jump.lean`
(`toN`), picks a number of visits `V` (`chooseV`) and, if the hypotheses of the theorem `jump` hold for it, replaces
the zone by the zone `V` visits later.  Only `den_canonL`, `den_encZone` and the checks made in `tryJump` matter for
correctness; `parseZone`, `toN` and `chooseV` are untrusted (what they return is checked).

`run_sound`: if `run fuel c = true`, the machine halts from `sem c`.
-/

namespace H172044

open TM

/-! ## One phase for the runs -/

/-- Put a cell in front of a stack in canonical phase. -/
def cbit (b : Bool) (out : List Item) : List Item :=
  match b, out with
  | true, .bit true :: .bit false :: .run w m :: s =>
    if w = W then .run W (m + 1) :: s else .bit b :: out
  | true, .bit true :: .bit false :: .bit true :: .bit true :: .bit false :: s => pushRun W 2 s
  | _, _ => .bit b :: out

theorem den_cbit (b : Bool) (out : List Item) (t : Tape) : den (cbit b out) t = cons b (den out t) := by
  unfold cbit
  split
  · next w m s =>
    by_cases h : w = W
    · subst h; simp [den]
    · simp [h, den]
  · rw [den_pushRun]; rfl
  · rfl

/-- Put `n` copies of 011 in front of a stack, taking in the copies that lie behind them. -/
def crun (n : Nat) : List Item → List Item
  | .bit true :: .bit true :: .bit false :: s => crun (n + 1) s
  | .run w m :: s => if w = W then .run W (n + m) :: s else .run W n :: .run w m :: s
  | s => .run W n :: s

theorem den_crun (t : Tape) (n : Nat) (out : List Item) : den (crun n out) t = rep n W (den out t) := by
  fun_induction crun n out with
  | case1 n s ih =>
    rw [ih]
    show rep (n + 1) W (den s t) = rep n W (app W (den s t))
    rw [rep_app_comm]
  | case2 n m s => simp [den, rep_add]
  | case3 n w m s h => simp [den]
  | case4 n s h1 h2 => simp [den]

def crun0 (n : Nat) (out : List Item) : List Item := if n = 0 then out else crun n out

theorem den_crun0 (t : Tape) (n : Nat) (out : List Item) : den (crun0 n out) t = rep n W (den out t) := by
  unfold crun0
  by_cases h : n = 0
  · subst h; rfl
  · simp only [h, ite_false]; exact den_crun t n out

/-- One item in canonical phase: a run of 110 is `11 (011)^(n-1) 0`, a run of 101 is `1 (011)^(n-1) 01`. -/
def emit (x : Item) (out : List Item) : List Item :=
  match x with
  | .bit b => cbit b out
  | .run w n =>
    if w = W then crun0 n out
    else if w = [false, true, true] then
      (if n = 0 then out else cbit false (crun0 (n - 1) (cbit true (cbit true out))))
    else if w = [true, false, true] then
      (if n = 0 then out else cbit true (cbit false (crun0 (n - 1) (cbit true out))))
    else .run w n :: out

theorem rot110 (m : Nat) (s : Tape) :
    rep (m + 1) [false, true, true] s = cons false (rep m W (cons true (cons true s))) := by
  rw [← rep_app_comm]
  exact (rep_rotate m [false] W [false, true, true] rfl (cons true (cons true s))).symm

theorem rot101 (m : Nat) (s : Tape) :
    rep (m + 1) [true, false, true] s = cons true (cons false (rep m W (cons true s))) := by
  rw [← rep_app_comm]
  exact (rep_rotate m [true, false] W [true, false, true] rfl (cons true s)).symm

theorem den_emit (x : Item) (out : List Item) (t : Tape) : den (emit x out) t = den [x] (den out t) := by
  cases x with
  | bit b => exact den_cbit b out t
  | run w n =>
    unfold emit
    by_cases h1 : w = W
    · subst h1; simp only [ite_true]; exact den_crun0 t n out
    · simp only [h1, ite_false]
      by_cases h2 : w = [false, true, true]
      · subst h2
        simp only [ite_true]
        cases n with
        | zero => rfl
        | succ m =>
          simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
          rw [den_cbit, den_crun0, den_cbit, den_cbit]
          exact (rot110 m (den out t)).symm
      · simp only [h2, ite_false]
        by_cases h3 : w = [true, false, true]
        · subst h3
          simp only [ite_true]
          cases n with
          | zero => rfl
          | succ m =>
            simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
            rw [den_cbit, den_cbit, den_crun0, den_cbit]
            exact (rot101 m (den out t)).symm
        · simp only [h3, ite_false]; rfl

/-- The whole stack in canonical phase. -/
def canonL : List Item → List Item
  | [] => []
  | x :: s => emit x (canonL s)

theorem den_canonL (t : Tape) : ∀ s : List Item, den (canonL s) t = den s t
  | [] => rfl
  | x :: s => by
    show den (emit x (canonL s)) t = _
    rw [den_emit, den_canonL t s]
    cases x <;> rfl

/-! ## Reading and writing a zone -/

def encLv : List (Bool × Nat) → List Item → List Item
  | [], rest => rest
  | (b, n) :: r, rest => .bit true :: .bit (!b) :: .run W n :: encLv r rest

def encZone (n0 : Nat) (lv : List (Bool × Nat)) (rest : List Item) : List Item :=
  .bit false :: .run W n0 :: encLv lv rest

theorem den_encLv (t : Tape) (rest : List Item) : ∀ lv : List (Bool × Nat),
    den (encLv lv rest) t = lvT lv (den rest t)
  | [] => rfl
  | (b, n) :: r => by
    show cons true (cons (!b) (rep n W (den (encLv r rest) t))) = _
    rw [den_encLv t rest r]; rfl

theorem den_encZone (n0 : Nat) (lv : List (Bool × Nat)) (rest : List Item) (t : Tape) :
    den (encZone n0 lv rest) t = zoneT n0 lv (den rest t) := by
  show cons false (rep n0 W (den (encLv lv rest) t)) = _
  rw [den_encLv]; rfl

/-- The levels of a zone in a canonical stack (counts of at least 7), and what is left. -/
def parseLv : Nat → List Item → List (Bool × Nat) × List Item
  | 0, s => ([], s)
  | fuel + 1, .bit true :: .bit x :: .run w n :: s =>
    if w = W ∧ 7 ≤ n then
      let p := parseLv fuel s
      ((!x, n) :: p.1, p.2)
    else ([], .bit true :: .bit x :: .run w n :: s)
  | _ + 1, s => ([], s)

def parseZone : List Item → Option (Nat × List (Bool × Nat) × List Item)
  | .bit false :: .run w n0 :: s =>
    if w = W then
      let p := parseLv s.length s
      some (n0, p.1, p.2)
    else none
  | _ => none

/-- To the coordinates of `Jump.lean`: previous bit and count, the levels above. -/
def toNaux : Bool → Nat → List (Bool × Nat) → List (Bool × Nat) × Nat
  | b, n, [] => ([], n + b.toNat)
  | b, n, (b', n') :: r =>
    let p := toNaux b' n' r
    ((b', n + b.toNat - b'.toNat) :: p.1, p.2)

def toN (n0 : Nat) : List (Bool × Nat) → List (Bool × Nat) × Nat
  | [] => ([], 0)
  | (b1, n1) :: r =>
    let p := toNaux b1 n1 r
    ((b1, n0 - b1.toNat) :: p.1, p.2)

/-- The largest number of visits after which the bits of the levels given have not overflowed and their counts
are still at least 6: `pow = 2^(j-1)`, `blow` the value of the bits below, `lim` the bound so far. -/
def chooseAux : List (Bool × Nat) → Nat → Nat → Option Nat → Nat
  | [], pow, blow, lim =>
    let v0 := pow - 1 - blow
    match lim with
    | none => v0
    | some l => min v0 l
  | (b, M) :: r, pow, blow, lim =>
    if M < 6 then 0 else
      let l := (2 * (M - 6) + b.toNat + 1) * pow - 1 - blow
      let lim' := match lim with
        | none => some l
        | some l0 => some (min l0 l)
      chooseAux r (2 * pow) (blow + b.toNat * pow) lim'

def chooseV : List (Bool × Nat) → Nat
  | [] => 0
  | (b, _) :: r => chooseAux r 2 b.toNat none

/-- At a visit, jump over as many visits of the zone as `chooseV` says, if the theorem `jump` applies. -/
def tryJump (c : MC) : Option MC :=
  if c.dir = true ∧ c.front = [] ∧ c.st = .A then
    let cb := canonL c.back
    match parseZone cb with
    | none => none
    | some (n0, lv, rest) =>
      let p := toN n0 lv
      let V := chooseV p.1
      let ps' := after V p.1
      if 8 ≤ V ∧ ovf V p.1 = 0 ∧ goodN ps' p.2 = true ∧ n0of p.1 = n0 ∧ physP p.1 p.2 = lv ∧
          encZone n0 lv rest = cb then
        some ⟨true, [], encZone (n0of ps') (physP ps' p.2) rest, .A⟩
      else none
  else none

theorem tryJump_sound (c c' : MC) (h : tryJump c = some c') : Reach (sem c) (sem c') := by
  obtain ⟨d, f, b, q⟩ := c
  unfold tryJump at h
  by_cases hv : d = true ∧ f = [] ∧ q = .A
  · obtain ⟨hd, hf, hq⟩ := hv
    subst hd; subst hf; subst hq
    simp only [and_self, ite_true] at h
    cases hp : parseZone (canonL b) with
    | none => rw [hp] at h; simp at h
    | some x =>
      obtain ⟨n0, lv, rest⟩ := x
      rw [hp] at h
      simp only at h
      split at h
      · next hc =>
        obtain ⟨_, hov, hgood, hn0, hlv, henc⟩ := hc
        have e : c' = ⟨true, [], encZone (n0of (after (chooseV (toN n0 lv).1) (toN n0 lv).1))
            (physP (after (chooseV (toN n0 lv).1) (toN n0 lv).1) (toN n0 lv).2) rest, .A⟩ := by
          simpa using h.symm
        subst e
        have hj := jump (toN n0 lv).1 (toN n0 lv).2 (den rest blank) (chooseV (toN n0 lv).1) hov hgood
        have e1 : sem ⟨true, [], b, .A⟩ = ⟨zoneN (toN n0 lv).1 (toN n0 lv).2 (den rest blank), blank, .A⟩ := by
          show (⟨den b blank, blank, .A⟩ : Config) = _
          rw [← den_canonL blank b, ← henc, den_encZone]
          unfold zoneN
          rw [hn0, hlv]
        rw [e1]
        show Reach _ ⟨den (encZone _ _ rest) blank, blank, .A⟩
        rw [den_encZone]
        exact hj
      · simp at h
  · simp only [hv, ite_false] at h
    simp at h

/-! ## The loop -/

/-- Up to `fuel` rounds (a jump if one applies, then one step of the simulator); `true` if the halting transition is
met. -/
def run : Nat → MC → Bool
  | 0, _ => false
  | fuel + 1, c =>
    match mstep ((tryJump c).getD c) with
    | .halt => true
    | .next c' => run fuel c'

theorem halts_of_reach {c c' : Config} (h : Reach c c') (h' : TM.Halts trans c') : TM.Halts trans c := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, d, hm, hd⟩ := h'
  exact ⟨n + m, d, steps_seq trans hn hm, hd⟩

/-- **Soundness of the simulator.** -/
theorem run_sound : ∀ (fuel : Nat) (c : MC), run fuel c = true → TM.Halts trans (sem c)
  | 0, _, h => by simp [run] at h
  | fuel + 1, c, h => by
    have h0 : Reach (sem c) (sem ((tryJump c).getD c)) := by
      cases hj : tryJump c with
      | none => exact Reach.refl _
      | some c1 => exact tryJump_sound c c1 hj
    have hm := mstep_sound ((tryJump c).getD c)
    simp only [run] at h
    cases hr : mstep ((tryJump c).getD c) with
    | halt =>
      rw [hr] at hm
      exact halts_of_reach h0 ⟨0, _, rfl, hm⟩
    | next c2 =>
      rw [hr] at hm h
      exact halts_of_reach h0 (halts_of_reach hm (run_sound fuel c2 h))

/-- Blank tape, the head in A. -/
def start : MC := ⟨true, [], [], .A⟩

theorem sem_start : sem start = init := rfl

end H172044
