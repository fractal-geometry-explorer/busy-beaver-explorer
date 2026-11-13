import Rules

/-!
# The binary counter, as a program, run from blank tape

Read the tape left of the wall in units of six cells, from the wall leftwards: an `X` unit (one bit, `X0 = 111110`,
`X1 = 111011`), a `Y` unit (two bits, `Y0 = 111011`, `Y1 = 111010`, `Y2 = 111111`, `Y3 = 111110`), an `X` unit, and
so on.  `R ds n L` is the configuration at the right end in phase R: `L`, the units `ds` (nearest the wall first),
the unit `111110`, and the wall `10111 (010111)^n` with the head in state B after it.

Three sweeps add one to the counter and one unit to the wall (`Rules.lean`): `inc_*` restate the five cycle rules
on `R`, `next` is the increment as a program on the digit list and `next_sound` says it is exact.  `next` answers
`none` only when the carry runs off the end of `ds` (into the irregular left part `L`), which in the run from blank
tape first happens after about `8.4·10^19` more increments.

`reach_s0`: after 59,129 steps from blank tape the machine is in `R ds0 2 L0`.  `run_value` (`native_decide`) runs
`next` 100,000,000 times from there: no halt in the first 240,000,021,742,916,313 steps (about 2.4·10^17).
-/

namespace H136111

open TM

def x0 : List Bool := [false, true, true, true, true, true]
def x1 : List Bool := [true, true, false, true, true, true]
/-- An `X` unit, nearest-first (the cells right to left). -/
def xw : Nat → List Bool
  | 0 => x0
  | _ => x1
/-- A `Y` unit, nearest-first. -/
def yw : Nat → List Bool
  | 0 => x1
  | 1 => [false, true, false, true, true, true]
  | 2 => [true, true, true, true, true, true]
  | _ => x0
def tl : List Bool := [true, true, true, false, true]
def w6 : List Bool := [true, true, true, false, true, false]

/-- The units `ds`, nearest first, starting with an `X` unit when `b` is true. -/
def enc : Bool → List Nat → Tape → Tape
  | _, [], L => L
  | true, d :: ds, L => app (xw d) (enc false ds L)
  | false, d :: ds, L => app (yw d) (enc true ds L)

/-- Phase R. -/
def R (ds : List Nat) (n : Nat) (L : Tape) : Config := ⟨rep n w6 (app tl (app x0 (enc true ds L))), blank, .B⟩

/-- `j` pairs `Y3 X1` and `j` pairs `Y0 X0`. -/
def ones : Nat → List Nat
  | 0 => []
  | j + 1 => 3 :: 1 :: ones j
def zeros : Nat → List Nat
  | 0 => []
  | j + 1 => 0 :: 0 :: zeros j

theorem ones_succ (j : Nat) : ones (j + 1) = ones j ++ [3, 1] := by
  induction j with
  | zero => rfl
  | succ j ih => show 3 :: 1 :: ones (j + 1) = (3 :: 1 :: ones j) ++ [3, 1]; rw [ih]; rfl

theorem enc_ones (j : Nat) (r : List Nat) (L : Tape) :
    enc false (ones j ++ r) L = rep j (x0 ++ x1) (enc false r L) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show app (yw 3) (app (xw 1) (enc false (ones j ++ r) L)) = _
    rw [ih, app_app]; rfl

theorem enc_zeros (j : Nat) (r : List Nat) (L : Tape) :
    enc false (zeros j ++ r) L = rep j (x1 ++ x0) (enc false r L) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show app (yw 0) (app (xw 0) (enc false (zeros j ++ r) L)) = _
    rw [ih, app_app]; rfl

theorem wallR (n : Nat) (T : Tape) :
    rep (n + 1) w6 T = app [true, true, true, false] (rep n [true, false, true, true, true, false] (app [true, false] T)) := by
  rw [rep_rotate n [true, true, true, false] [true, false, true, true, true, false] w6 rfl, ← rep_app_comm]; rfl

theorem zrot (j : Nat) (S : Tape) :
    app x0 (rep j (x1 ++ x0) S) =
      app [false, true, true, true, true] (rep j [true, true, true, false, true, true, true, false, true, true, true, true] (app [true] S)) := by
  rw [← rep_rotate j [true] (x1 ++ x0) [true, true, true, false, true, true, true, false, true, true, true, true] rfl S]; rfl

theorem inc_x0 (ds : List Nat) (n : Nat) (L : Tape) :
    steps (48 * n + 122) (R (0 :: ds) n L) = some (R (1 :: ds) (n + 1) L) := by
  have h := cyc_x0 n (enc false ds L)
  simp only [R, enc, xw]
  rw [wallR]; exact h

theorem inc_y0 (j : Nat) (ds : List Nat) (n : Nat) (L : Tape) :
    steps (60 * j + 48 * n + 154) (R (1 :: ones j ++ 0 :: ds) n L) = some (R (0 :: zeros j ++ 1 :: ds) (n + 1) L) := by
  have h := cyc_y0 j n (enc true ds L)
  simp only [R, List.cons_append, enc, xw]
  rw [enc_ones, enc_zeros, wallR, zrot]; exact h

theorem inc_y1 (j : Nat) (ds : List Nat) (n : Nat) (L : Tape) :
    steps (60 * j + 48 * n + 162) (R (1 :: ones j ++ 1 :: ds) n L) = some (R (0 :: zeros j ++ 2 :: ds) (n + 1) L) := by
  have h := cyc_y1 j n (enc true ds L)
  simp only [R, List.cons_append, enc, xw]
  rw [enc_ones, enc_zeros, wallR, zrot]; exact h

theorem inc_y2 (j : Nat) (ds : List Nat) (n : Nat) (L : Tape) :
    steps (60 * j + 48 * n + 154) (R (1 :: ones j ++ 2 :: ds) n L) = some (R (0 :: zeros j ++ 3 :: ds) (n + 1) L) := by
  have h := cyc_y2 j n (enc true ds L)
  simp only [R, List.cons_append, enc, xw]
  rw [enc_ones, enc_zeros, wallR, zrot]; exact h

theorem inc_x (j : Nat) (ds : List Nat) (n : Nat) (L : Tape) :
    steps (60 * j + 48 * n + 182) (R (1 :: ones j ++ 3 :: 0 :: ds) n L) =
      some (R (0 :: zeros j ++ 0 :: 1 :: ds) (n + 1) L) := by
  have h := cyc_x j n (enc false ds L)
  simp only [R, List.cons_append, enc, xw]
  rw [enc_ones, enc_zeros, wallR, zrot]; exact h

/-- Scan the digits after a leading `1` (bit 0 set): skip pairs `3 1`; `inl (j, v, r)` for a stop at a `Y` digit
`v < 3`, `inr (j, r)` for a stop at an `X0` after a `Y3`. -/
def scan (j : Nat) : List Nat → Option (Sum (Nat × Nat × List Nat) (Nat × List Nat))
  | [] => none
  | v :: r =>
    if v < 3 then some (.inl (j, v, r))
    else if v = 3 then
      match r with
      | 1 :: r' => scan (j + 1) r'
      | 0 :: r' => some (.inr (j, r'))
      | _ => none
    else none

theorem scan_inl : ∀ (k : Nat) (r : List Nat) (j v : Nat) (r' : List Nat), scan k r = some (.inl (j, v, r')) →
    ones k ++ r = ones j ++ v :: r' ∧ v < 3
  | k, [], j, v, r', h => by cases h
  | k, d :: r, j, v, r', h => by
    unfold scan at h
    split at h
    · rename_i hd; simp at h; obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; exact ⟨rfl, hd⟩
    · split at h
      · rename_i hd hd3
        subst hd3
        split at h
        · rename_i r''
          obtain ⟨hi, hv⟩ := scan_inl (k + 1) r'' j v r' h
          refine ⟨?_, hv⟩
          rw [← hi, ones_succ]; simp
        · cases h
        · cases h
      · cases h

theorem scan_inr : ∀ (k : Nat) (r : List Nat) (j : Nat) (r' : List Nat), scan k r = some (.inr (j, r')) →
    ones k ++ r = ones j ++ 3 :: 0 :: r'
  | k, [], j, r', h => by cases h
  | k, d :: r, j, r', h => by
    unfold scan at h
    split at h
    · cases h
    · split at h
      · rename_i hd hd3
        subst hd3
        split at h
        · rename_i r''
          have := scan_inr (k + 1) r'' j r' h
          rw [← this, ones_succ]; simp
        · simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2; rfl
        · cases h
      · cases h

/-- A macro state: the digits (nearest the wall first) and the length of the wall. -/
structure MS where
  ds : List Nat
  n : Nat
  deriving DecidableEq, Repr

/-- One increment (three sweeps), with its number of steps. -/
def next (s : MS) : Option (MS × Nat) :=
  match s.ds with
  | 0 :: r => some (⟨1 :: r, s.n + 1⟩, 48 * s.n + 122)
  | 1 :: r =>
    match scan 0 r with
    | some (.inl (j, v, r')) =>
      some (⟨0 :: zeros j ++ (v + 1) :: r', s.n + 1⟩, 60 * j + 48 * s.n + (if v = 1 then 162 else 154))
    | some (.inr (j, r')) => some (⟨0 :: zeros j ++ 0 :: 1 :: r', s.n + 1⟩, 60 * j + 48 * s.n + 182)
    | none => none
  | _ => none

/-- **Soundness**: when `next` answers, the machine makes those three sweeps, for every tape `L` left of the digits. -/
theorem next_sound (L : Tape) (s s' : MS) (c : Nat) (h : next s = some (s', c)) :
    steps c (R s.ds s.n L) = some (R s'.ds s'.n L) := by
  obtain ⟨ds, n⟩ := s
  simp only [next] at h
  split at h
  · rename_i r
    simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2
    exact inc_x0 r n L
  · rename_i r
    split at h
    · rename_i j v r' hs
      obtain ⟨hr, hv⟩ := scan_inl 0 r j v r' hs
      simp only [ones, List.nil_append] at hr
      subst hr
      simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2
      show steps _ (R (1 :: ones j ++ v :: r') n L) = _
      have e : (1 :: ones j ++ v :: r') = 1 :: (ones j ++ v :: r') := rfl
      rcases (show v = 0 ∨ v = 1 ∨ v = 2 by omega) with hv0 | hv0 | hv0 <;> subst hv0
      · exact inc_y0 j r' n L
      · exact inc_y1 j r' n L
      · exact inc_y2 j r' n L
    · rename_i j r' hs
      have hr := scan_inr 0 r j r' hs
      simp only [ones, List.nil_append] at hr
      subst hr
      simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2
      exact inc_x j r' n L
    · cases h
  · cases h

/-- `k` increments, adding up the steps. -/
def run : Nat → MS → Nat → Option (MS × Nat)
  | 0, s, t => some (s, t)
  | k + 1, s, t =>
    match next s with
    | none => none
    | some (s', c) => run k s' (t + c)

theorem run_sound (L : Tape) : ∀ (k : Nat) (s : MS) (t : Nat) (s' : MS) (t' : Nat), run k s t = some (s', t') →
    steps t init = some (R s.ds s.n L) → steps t' init = some (R s'.ds s'.n L)
  | 0, s, t, s', t', h, h0 => by simp [run] at h; obtain ⟨h1, h2⟩ := h; subst h1 h2; exact h0
  | k + 1, s, t, s', t', h, h0 => by
    simp only [run] at h
    split at h
    · cases h
    · rename_i s1 c hn
      exact run_sound L k s1 (t + c) s' t' h (steps_seq trans h0 (next_sound L s s1 c hn))

/-- The 49 units of the run at step 59,129 (sweep 149), nearest the wall first: bit 0 is 1, then the counter's low
bits, the run of `Y3 X0` (the blocks `1^5`), and the units `X1 Y3 X1 Y3 X1` of the left part `(3 7)^2`. -/
def ds0 : List Nat := [1, 0, 1, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3,
  0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 1, 3, 1]

/-- The irregular left part `1 0 1^11 0 1^3 0 1 0 1^3 0 1 0 1 0 1^5 0` (34 cells), nearest-first. -/
def L0 : Tape := app [false, true, true, true, true, true, false, true, false, true, false, true, true, true, false,
  true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true] blank

def s0 : MS := ⟨ds0, 2⟩

set_option maxRecDepth 100000 in
/-- After 59,129 steps from blank tape (sweep 149) the machine is in phase R with the digits `ds0` and a wall of two
units, by compiled evaluation of the list simulator. -/
theorem reach_s0 : steps 59129 init = some (R s0.ds s0.n L0) := by
  have h := blank_reaches trans (n := 59129) (q := .A) (c := ⟨[true, true, true, false, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, false, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true], [], .B⟩) (by native_decide)
  exact h

theorem run_value : ((run 100000000 s0 59129).map (·.2)) = some 240000021742916313 := by native_decide

/-- **No halt in the first 240,000,021,742,916,313 steps**, by a hundred million proved increments of the counter. -/
theorem no_halt_240000021742916313 : ∃ c, steps 240000021742916313 init = some c := by
  have h := run_value
  cases e : run 100000000 s0 59129 with
  | none => rw [e] at h; cases h
  | some x =>
    rw [e] at h
    simp at h
    obtain ⟨s', t'⟩ := x
    simp at h
    subst h
    exact ⟨_, run_sound L0 100000000 s0 59129 s' _ e reach_s0⟩

end H136111
