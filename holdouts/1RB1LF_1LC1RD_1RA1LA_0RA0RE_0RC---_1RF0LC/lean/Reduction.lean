import Sweeps
import Zone

/-!
# The step map for every wall, and the reduction

A step starts at `S W N`: the tape `W A> 0 b^N 1` (b = 110), blank on both sides, `W` the wall (kept here as the
list of its cells from the head leftwards).  The step has three parts:

1. the head crosses the block, builds a few short-lived junctions at its right end, and then the junction
   `J x y`: `L 1 b^x 111 F> b^(y+1) 1` with `x = N - const`;
2. the transfer loop (`sweeps` of `Sweeps.lean`): `J (r + 2t) y` becomes `J r (y + 3t)`, `r ∈ {0, 1}`;
3. the end of the step works on the wall and leaves `W' A> 0 b^N' 1`.

Parts 1 and 3 are computed by the zone simulator of `Zone.lean`, with the middle of the long block of `b`s as the
block that the head only crosses whole (three shift rules).  The simulator never looks at the number of copies in
that block, so `stepMap (W, N)` is arithmetic on `N` plus two bounded computations on the wall, and
`step_next` / `step_halt` say that this is what the machine does whenever the simulator answers (it answers `stuck`
when `N` is too small for the buffers, when the head meets the block in a way the rules do not cover, or when the
fuel runs out).

`halts_iff`: as long as the orbit never gets the answer `stuck`, the machine halts from blank tape iff the orbit
reaches a halting step.
-/

namespace H3292

open TM TM.Zone

def rulesR : List (Rule St) :=
  [⟨.C, [false], [true, true, false], [false, true, true], 5⟩,
   ⟨.A, [false, true, true, false], [true, true, false], [true, true, true], 15⟩]

def rulesL : List (Rule St) :=
  [⟨.F, [true], [true, true, true], [true, true, false], 3⟩]

theorem rulesR_ok : ∀ r ∈ rulesR, RuleR trans r := by
  intro r hr
  simp only [rulesR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact fun _ _ => rfl

theorem rulesL_ok : ∀ r ∈ rulesL, RuleL trans r := by
  intro r hr
  simp only [rulesL, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl
  exact fun _ _ => rfl

/-! ## Words -/

/-- `n` copies of the three cells `x y z`. -/
def repl (x y z : Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => x :: y :: z :: repl x y z n

theorem repl_spec (x y z : Bool) (l : List Bool) (s : Tape) :
    ∀ n, app (repl x y z n ++ l) s = rep n [x, y, z] (app l s)
  | 0 => rfl
  | n + 1 => by simp only [repl, List.cons_append, app_cons, rep_succ, app_nil, repl_spec x y z l s n]

/-- The leading copies of `x y z` in a word: their number, and the rest. -/
def cnt (x y z : Bool) : List Bool → Nat × List Bool
  | a :: b :: c :: l => if a = x ∧ b = y ∧ c = z then ((cnt x y z l).1 + 1, (cnt x y z l).2) else (0, a :: b :: c :: l)
  | l => (0, l)

theorem cnt_spec (x y z : Bool) (s : Tape) :
    ∀ l : List Bool, app l s = rep (cnt x y z l).1 [x, y, z] (app (cnt x y z l).2 s)
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: l => by
    simp only [cnt]
    split
    · next h =>
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [app_cons, rep_succ, app_nil]
      rw [← cnt_spec a b c s l]
    · rfl

/-- Drop the zeros at the end of a word. -/
def trim : List Bool → List Bool
  | [] => []
  | x :: l =>
    match x, trim l with
    | false, [] => []
    | x, t => x :: t

theorem trim_spec : ∀ l : List Bool, app (trim l) blank = app l blank
  | [] => rfl
  | x :: l => by
    have ih := trim_spec l
    simp only [trim]
    split
    · next h => rw [h] at ih; simp only [app_cons, app_nil] at ih ⊢; rw [← ih, cons_false_blank]
    · simp only [app_cons, ih]

theorem rep3 (i k j : Nat) (w : List Bool) (s : Tape) :
    rep i w (rep k w (rep j w s)) = rep (k + (i + j)) w s := by
  rw [← rep_add, ← rep_add]
  congr 1
  omega

/-! ## The three parts of a step -/

/-- The start of a step: `W A> 0 b^N 1` (the wall `W` listed from the head leftwards). -/
def S (W : List Bool) (N : Nat) : Config :=
  ⟨app W blank, cons false (rep N [true, true, false] (cons true blank)), .A⟩

def ini1 (W : List Bool) (B1 B2 : Nat) : ACfg St :=
  ⟨.L, W, false :: repl true true false B1, [true, true, false], repl true true false B2 ++ [true], .A⟩

theorem ini1_spec (W : List Bool) (B1 B2 k : Nat) : enc k (ini1 W B1 B2) = S W (k + (B1 + B2)) := by
  have e1 := repl_spec true true false [] (rep k [true, true, false] (app (repl true true false B2 ++ [true]) blank)) B1
  rw [List.append_nil, app_nil] at e1
  simp only [enc, ini1, S, app_cons]
  rw [e1, repl_spec, rep3]
  rfl

/-- Reads the junction `J (k + x) y L` off a simulator configuration: `(x, y, L)`. -/
def decodeJ (c : ACfg St) : Option (Nat × Nat × List Bool) :=
  if c.z = .R ∧ c.st = .F ∧ c.m = [false, true, true] ∧ c.a.take 3 = [true, true, true] ∧
      (cnt false true true (c.a.drop 3)).2 = [] ∧
      (cnt false true true c.o).2.head? = some true ∧
      0 < (cnt true true false c.b).1 ∧ trim (cnt true true false c.b).2 = [true] then
    some ((cnt false true true (c.a.drop 3)).1 + (cnt false true true c.o).1,
      (cnt true true false c.b).1 - 1, (cnt false true true c.o).2.tail)
  else none

theorem decodeJ_spec (k : Nat) {c : ACfg St} {x y : Nat} {L : List Bool} (h : decodeJ c = some (x, y, L)) :
    enc k c = J (k + x) y (app L blank) := by
  obtain ⟨z, a, b, m, o, q⟩ := c
  unfold decodeJ at h
  split at h
  · next hc =>
    obtain ⟨rfl, rfl, rfl, ha, ha2, ho, hy, hb⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only at ha ha2 ho hy hb
    have ea : ∀ s : Tape, app a s = app [true, true, true] (rep (cnt false true true (a.drop 3)).1 [false, true, true] s) := by
      intro s
      have h1 := cnt_spec false true true s (a.drop 3)
      rw [ha2] at h1
      calc app a s = app (a.take 3 ++ a.drop 3) s := by rw [List.take_append_drop]
        _ = app (a.take 3) (app (a.drop 3) s) := (app_app _ _ _).symm
        _ = _ := by rw [h1, ha]; rfl
    have eo : app o blank = rep (cnt false true true o).1 [false, true, true]
        (cons true (app (cnt false true true o).2.tail blank)) := by
      rw [cnt_spec false true true blank o]
      cases e : (cnt false true true o).2 with
      | nil => rw [e] at ho; cases ho
      | cons t r =>
        rw [e] at ho
        simp only [List.head?_cons, Option.some.injEq] at ho
        subst ho
        rfl
    have eb : app b blank = rep ((cnt true true false b).1 - 1 + 1) [true, true, false] (cons true blank) := by
      rw [cnt_spec true true false blank b, ← trim_spec, hb]
      rw [show (cnt true true false b).1 - 1 + 1 = (cnt true true false b).1 by omega]
      rfl
    simp only [enc, J]
    rw [ea, eo, eb, rep3]
  · cases h

/-- The junction `J r y L` with `y + 1 = k + 2 B` copies on the right, `B` of them on each side of the block. -/
def ini2 (r : Nat) (L : List Bool) (B : Nat) : ACfg St :=
  ⟨.L, [true, true, true] ++ (repl false true true r ++ true :: L), repl true true false B, [true, true, false],
    repl true true false B ++ [true], .F⟩

theorem ini2_spec (r : Nat) (L : List Bool) (B k y : Nat) (hy : y + 1 = k + (B + B)) :
    enc k (ini2 r L B) = J r y (app L blank) := by
  have e1 := repl_spec true true false [] (rep k [true, true, false] (app (repl true true false B ++ [true]) blank)) B
  rw [List.append_nil, app_nil] at e1
  simp only [enc, ini2, J]
  rw [e1, repl_spec, rep3, ← app_app, repl_spec, hy]
  rfl

/-- Reads a step start `S W (k + x)` off a simulator configuration: `(x, W)`. -/
def decodeS (c : ACfg St) : Option (Nat × List Bool) :=
  if c.z = .L ∧ c.st = .A ∧ c.m = [true, true, false] ∧ c.b.head? = some false ∧
      (cnt true true false c.b.tail).2 = [] ∧ trim (cnt true true false c.o).2 = [true] then
    some ((cnt true true false c.b.tail).1 + (cnt true true false c.o).1, trim c.a)
  else none

theorem decodeS_spec (k : Nat) {c : ACfg St} {x : Nat} {W : List Bool} (h : decodeS c = some (x, W)) :
    enc k c = S W (k + x) := by
  obtain ⟨z, a, b, m, o, q⟩ := c
  unfold decodeS at h
  split at h
  · next hc =>
    obtain ⟨rfl, rfl, rfl, hb, hb2, ho⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only at hb hb2 ho
    cases b with
    | nil => cases hb
    | cons b0 b' =>
      simp only [List.head?_cons, Option.some.injEq] at hb
      subst hb
      simp only [List.tail_cons] at hb2 ⊢
      have eb : ∀ s : Tape, app b' s = rep (cnt true true false b').1 [true, true, false] s := by
        intro s
        have h1 := cnt_spec true true false s b'
        rw [hb2] at h1
        exact h1
      have eo : app o blank = rep (cnt true true false o).1 [true, true, false] (cons true blank) := by
        rw [cnt_spec true true false blank o, ← trim_spec, ho]
        rfl
      simp only [enc, S, app_cons]
      rw [eb, eo, rep3, trim_spec]
  · cases h

def fuel (n : Nat) : Nat := 200 * (n + 20) ^ 2

/-- The step map: from the step start `S W N`, the next step start, `halt`, or `stuck` (no answer). -/
def stepMap (p : List Bool × Nat) : Res (List Bool × Nat) :=
  let B1 := p.1.length + 2
  let B2 := p.1.length + 14
  if p.2 < B1 + B2 then .stuck else
  match arun trans rulesR rulesL (fun c => (decodeJ c).isSome) (fuel p.1.length) (ini1 p.1 B1 B2) with
  | .next c1 =>
    match decodeJ c1 with
    | some (x, y, L) =>
      let X := (p.2 - (B1 + B2)) + x
      let Y := y + 3 * (X / 2)
      let B := L.length + 14
      if Y + 1 < B + B then .stuck else
      match arun trans rulesR rulesL (fun c => (decodeS c).isSome) (fuel L.length) (ini2 (X % 2) L B) with
      | .next c2 =>
        match decodeS c2 with
        | some (x2, W') => .next (W', (Y + 1 - (B + B)) + x2)
        | none => .stuck
      | .halt => .halt
      | .stuck => .stuck
    | none => .stuck
  | .halt => .halt
  | .stuck => .stuck

theorem sweeps' (L : Tape) (X y : Nat) : ∃ s, steps s (J X y L) = some (J (X % 2) (y + 3 * (X / 2)) L) := by
  obtain ⟨s, hs⟩ := sweeps L (X / 2) (X % 2) y
  rw [show X % 2 + 2 * (X / 2) = X by omega] at hs
  exact ⟨s, hs⟩

/-- **A step, for every wall**: if the map answers `(W', N')`, the machine goes from `S W N` to `S W' N'`. -/
theorem step_next {p p' : List Bool × Nat} (h : stepMap p = .next p') :
    ∃ s, 0 < s ∧ steps s (S p.1 p.2) = some (S p'.1 p'.2) := by
  unfold stepMap at h
  simp only at h
  split at h
  · cases h
  · next hN =>
    split at h
    · next c1 hr1 =>
      split at h
      · next x y L hd1 =>
        split at h
        · cases h
        · next hY =>
          split at h
          · next c2 hr2 =>
            split at h
            · next x2 W' hd2 =>
              simp only [Res.next.injEq] at h
              subst h
              obtain ⟨_, n1, hp, h1⟩ := arun_sound_pos rulesR_ok rulesL_ok
                (p.2 - (p.1.length + 2 + (p.1.length + 14))) _ _ _ _ rfl (by simp [ini1]) hr1
              rw [ini1_spec, decodeJ_spec _ hd1,
                show p.2 - (p.1.length + 2 + (p.1.length + 14)) + (p.1.length + 2 + (p.1.length + 14)) = p.2 by omega] at h1
              obtain ⟨n2, h2⟩ := sweeps' (app L blank) (p.2 - (p.1.length + 2 + (p.1.length + 14)) + x) y
              obtain ⟨_, n3, h3⟩ := arun_sound rulesR_ok rulesL_ok
                (y + 3 * ((p.2 - (p.1.length + 2 + (p.1.length + 14)) + x) / 2) + 1 - (L.length + 14 + (L.length + 14)))
                _ _ _ _ hr2
              rw [ini2_spec _ _ _ _ (y + 3 * ((p.2 - (p.1.length + 2 + (p.1.length + 14)) + x) / 2)) (by omega),
                decodeS_spec _ hd2] at h3
              exact ⟨n1 + (n2 + n3), by omega, steps_seq trans h1 (steps_seq trans h2 h3)⟩
            · cases h
          · cases h
          · cases h
      · cases h
    · cases h
    · cases h

theorem halts_of_reach {n : Nat} {c c' : Config} (h : steps n c = some c') (hh : Halts trans c') : Halts trans c := by
  obtain ⟨n2, c2, h2, h3⟩ := hh
  exact ⟨_, c2, steps_seq trans h h2, h3⟩

/-- If the map answers `halt`, the machine halts from `S W N`. -/
theorem step_halt {p : List Bool × Nat} (h : stepMap p = .halt) : Halts trans (S p.1 p.2) := by
  unfold stepMap at h
  simp only at h
  split at h
  · cases h
  · next hN =>
    split at h
    · next c1 hr1 =>
      split at h
      · next x y L hd1 =>
        split at h
        · cases h
        · next hY =>
          obtain ⟨_, n1, h1⟩ := arun_sound rulesR_ok rulesL_ok
            (p.2 - (p.1.length + 2 + (p.1.length + 14))) _ _ _ _ hr1
          rw [ini1_spec, decodeJ_spec _ hd1,
            show p.2 - (p.1.length + 2 + (p.1.length + 14)) + (p.1.length + 2 + (p.1.length + 14)) = p.2 by omega] at h1
          obtain ⟨n2, h2⟩ := sweeps' (app L blank) (p.2 - (p.1.length + 2 + (p.1.length + 14)) + x) y
          split at h
          · split at h <;> cases h
          · next hr2 =>
            have h3 := arun_halt rulesR_ok rulesL_ok
              (y + 3 * ((p.2 - (p.1.length + 2 + (p.1.length + 14)) + x) / 2) + 1 - (L.length + 14 + (L.length + 14)))
              _ _ _ hr2
            rw [ini2_spec _ _ _ _ (y + 3 * ((p.2 - (p.1.length + 2 + (p.1.length + 14)) + x) / 2)) (by omega)] at h3
            exact halts_of_reach h1 (halts_of_reach h2 h3)
          · cases h
      · cases h
    · next hr1 =>
      have h1 := arun_halt rulesR_ok rulesL_ok (p.2 - (p.1.length + 2 + (p.1.length + 14))) _ _ _ hr1
      rw [ini1_spec,
        show p.2 - (p.1.length + 2 + (p.1.length + 14)) + (p.1.length + 2 + (p.1.length + 14)) = p.2 by omega] at h1
      exact h1
    · cases h

/-! ## The orbit from blank tape -/

/-- The wall `1110110 1111101` at step 10,206 of the run from blank tape, listed from the head leftwards. -/
def wall0 : List Bool :=
  [true, false, true, true, true, true, true, false, true, true, false, true, true, true]

/-- The orbit of the step map from the step start `11101101111101 A> 0 b^48 1`. -/
def orbit : Nat → Res (List Bool × Nat)
  | 0 => .next (wall0, 48)
  | i + 1 =>
    match orbit i with
    | .next p => stepMap p
    | r => r

/-- The run from blank tape reaches the step start `S wall0 48` after 10,206 steps. -/
theorem blank_to_start : steps 10206 init = some (S wall0 48) := by
  have h : fsteps 10206 (FCfg.blank .A) = some ⟨wall0, false :: (repl true true false 48 ++ [true]), .A⟩ := by
    decide +kernel
  have h2 := blank_reaches trans h
  have e := repl_spec true true false [true] blank 48
  refine h2.trans ?_
  simp only [FCfg.toCfg, S, app_cons, e]
  rfl

theorem orbit_reach : ∀ (i : Nat) (p : List Bool × Nat), orbit i = .next p →
    ∃ n, i ≤ n ∧ steps n init = some (S p.1 p.2) := by
  intro i
  induction i with
  | zero =>
    intro p h
    simp only [orbit, Res.next.injEq] at h
    subst h
    exact ⟨_, Nat.zero_le _, blank_to_start⟩
  | succ i ih =>
    intro p h
    simp only [orbit] at h
    cases e : orbit i with
    | next y =>
      rw [e] at h
      obtain ⟨n, hn, h1⟩ := ih y e
      obtain ⟨s, hs, h2⟩ := step_next h
      exact ⟨n + s, by omega, steps_seq trans h1 h2⟩
    | halt => rw [e] at h; cases h
    | stuck => rw [e] at h; cases h

theorem halts_of_orbit : ∀ i, orbit i = .halt → HaltsFromBlank := by
  intro i
  induction i with
  | zero => intro h; cases h
  | succ i ih =>
    intro h
    simp only [orbit] at h
    cases e : orbit i with
    | next y =>
      rw [e] at h
      obtain ⟨n, _, h1⟩ := orbit_reach i y e
      exact halts_of_reach h1 (step_halt h)
    | halt => exact ih e
    | stuck => rw [e] at h; cases h

theorem not_halts_of_orbit (h : ∀ i, ∃ p, orbit i = .next p) : ¬ HaltsFromBlank := by
  rintro ⟨n, c', h1, h2⟩
  obtain ⟨p, hp⟩ := h (n + 1)
  obtain ⟨m, hm, h3⟩ := orbit_reach _ p hp
  have e : m = n + ((m - n - 1) + 1) := by omega
  rw [e] at h3
  have h4 : (some _ : Option Config) = none := h3.symm.trans (steps_halt trans h1 h2 (m - n - 1))
  cases h4

/-- **The reduction.**  As long as the step map answers along the orbit, the machine halts from blank tape iff
the orbit reaches a halting step. -/
theorem halts_iff (h : ∀ i, orbit i ≠ .stuck) : HaltsFromBlank ↔ ∃ i, orbit i = .halt := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hn
    apply not_halts_of_orbit _ hh
    intro i
    cases e : orbit i with
    | next p => exact ⟨p, rfl⟩
    | halt => exact absurd ⟨i, e⟩ hn
    | stuck => exact absurd e (h i)
  · rintro ⟨i, hi⟩
    exact halts_of_orbit i hi

/-! ## The first steps of the orbit, evaluated -/

def isNext : Res (List Bool × Nat) → Bool
  | .next _ => true
  | _ => false

theorem isNext_mono : ∀ i j, i ≤ j → isNext (orbit j) = true → isNext (orbit i) = true := by
  intro i j hij
  induction j with
  | zero => intro h; rw [show i = 0 by omega]; exact h
  | succ j ih =>
    intro h
    by_cases e : i = j + 1
    · rw [e]; exact h
    · apply ih (by omega)
      simp only [orbit] at h
      cases e2 : orbit j with
      | next _ => rfl
      | halt => rw [e2] at h; exact h
      | stuck => rw [e2] at h; exact h

/-- The orbit after five steps: the wall `1` and 468 copies of b (step 1,133,743 of the run). -/
theorem orbit_5 : orbit 5 = .next ([true], 468) := by decide +kernel

/-- The orbit answers for its first 40 steps, by the kernel. -/
theorem orbit_40 : isNext (orbit 40) = true := by decide +kernel

theorem first_steps : ∀ i, i ≤ 40 → ∃ p, orbit i = .next p := by
  intro i hi
  have h := isNext_mono i 40 hi orbit_40
  cases e : orbit i with
  | next p => exact ⟨p, rfl⟩
  | halt => rw [e] at h; cases h
  | stuck => rw [e] at h; cases h

end H3292
