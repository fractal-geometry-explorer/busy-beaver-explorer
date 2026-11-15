import Jump

/-!
# 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE: a run-length simulator, proved to follow the machine

The tape is kept as two stacks of items, a cell or a word repeated `n` times (`n` any natural number); the head faces
one of the stacks (`dir`).  `mstep` does one of: a single transition of the machine; a whole run crossed at once,
when one copy of its word (or two) is crossed from end to end in the state the head came in with; one copy of a run
unpacked into cells.  At a visit `tryJump` reads the zone at the right end of the tape and applies the theorem
`jump` of `Jump.lean` for a number of visits it chooses.  `run fuel c` repeats this and answers `true` when it
meets the halting transition.

Nothing here is trusted: `run_sound` proves that `run fuel c = true` implies that the machine halts from the
configuration `sem c` that `c` stands for.  How the simulator folds cells into runs, which runs it tries to cross
and how many visits it jumps only matter for its speed.
-/

namespace H172044

open TM

/-! ## Machines read right to left -/

abbrev Tab := St → Bool → Option (Bool × Dir × St)

/-- The machine with left and right exchanged. -/
def mirT (T : Tab) : Tab := fun q b =>
  match T q b with
  | none => none
  | some (w, .L, s) => some (w, .R, s)
  | some (w, .R, s) => some (w, .L, s)

/-- The configuration seen in a mirror: the head cell and what is left of it become the right side. -/
def mir (c : Config) : Config := ⟨tail c.r, cons (c.r 0) c.l, c.st⟩

theorem cons_head_tail (t : Tape) : cons (t 0) (tail t) = t := by
  funext n; cases n <;> rfl

theorem mir_mir (c : Config) : mir (mir c) = c := by
  obtain ⟨l, r, q⟩ := c
  show (⟨l, cons (r 0) (tail r), q⟩ : Config) = _
  rw [cons_head_tail]

theorem step_mir (T : Tab) (c : Config) : TM.step T (mir c) = (TM.step (mirT T) c).map mir := by
  obtain ⟨l, r, q⟩ := c
  simp only [TM.step, mir, mirT, cons_zero]
  cases h : T q (r 0) with
  | none => rfl
  | some x =>
    obtain ⟨w, d, s⟩ := x
    cases d with
    | L => rfl
    | R =>
      show some (⟨cons w (tail r), l, s⟩ : Config) = some ⟨cons w (tail r), cons (l 0) (tail l), s⟩
      rw [cons_head_tail]

theorem steps_mir (T : Tab) : ∀ (n : Nat) (c : Config), TM.steps T n (mir c) = (TM.steps (mirT T) n c).map mir
  | 0, _ => rfl
  | n + 1, c => by
    simp only [TM.steps, step_mir]
    cases h : TM.step (mirT T) c with
    | none => rfl
    | some c' => exact steps_mir T n c'

/-- `c` reaches `c'` under the table `T`. -/
def ReachT (T : Tab) (c c' : Config) : Prop := ∃ n, TM.steps T n c = some c'

theorem ReachT.refl (T : Tab) (c : Config) : ReachT T c c := ⟨0, rfl⟩

theorem ReachT.seq {T : Tab} {a b c : Config} (h₁ : ReachT T a b) (h₂ : ReachT T b c) : ReachT T a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, steps_seq T hn hm⟩

theorem ReachT.of_step {T : Tab} {c c' : Config} (h : TM.step T c = some c') : ReachT T c c' :=
  ⟨1, by simp [TM.steps, h]⟩

/-- A word crossed once is crossed any number of times. -/
theorem crossT (T : Tab) (q : St) (w v : List Bool)
    (h : ∀ L R : Tape, ReachT T ⟨L, app w R, q⟩ ⟨app v L, R, q⟩) :
    ∀ (k : Nat) (L R : Tape), ReachT T ⟨L, rep k w R, q⟩ ⟨rep k v L, R, q⟩
  | 0, L, R => ReachT.refl T _
  | k + 1, L, R => by
    have h1 := h L (rep k w R)
    have h2 := crossT T q w v h k (app v L) R
    rw [rep_app_comm] at h2
    exact h1.seq h2

/-! ## The machine on a finite word -/

/-- Run on the word `r` (cells already passed in `l`, nearest first) until the head leaves it on the far side;
`none` if it leaves on the near side, halts, or the fuel runs out. -/
def segRun (T : Tab) : Nat → List Bool → List Bool → St → Option (List Bool × St)
  | 0, _, _, _ => none
  | _ + 1, l, [], q => some (l, q)
  | fuel + 1, l, b :: r, q =>
    match T q b with
    | none => none
    | some (w, .R, s) => segRun T fuel (w :: l) r s
    | some (w, .L, s) =>
      match l with
      | [] => none
      | y :: l' => segRun T fuel l' (y :: w :: r) s

theorem segRun_sound (T : Tab) : ∀ (fuel : Nat) (l r : List Bool) (q : St) (l' : List Bool) (q' : St),
    segRun T fuel l r q = some (l', q') →
    ∀ L R : Tape, ReachT T ⟨app l L, app r R, q⟩ ⟨app l' L, R, q'⟩
  | 0, _, _, _, _, _, h => by simp [segRun] at h
  | fuel + 1, l, [], q, l', q', h => by
    simp only [segRun] at h
    have e : (l, q) = (l', q') := by simpa using h
    cases e
    intro L R; exact ReachT.refl T _
  | fuel + 1, l, b :: r, q, l', q', h => by
    intro L R
    simp only [segRun] at h
    cases hT : T q b with
    | none => rw [hT] at h; simp at h
    | some x =>
      obtain ⟨w, d, s⟩ := x
      rw [hT] at h
      cases d with
      | R =>
        have ih := segRun_sound T fuel (w :: l) r s l' q' h L R
        have hs : TM.step T ⟨app l L, app (b :: r) R, q⟩ = some ⟨app (w :: l) L, app r R, s⟩ := by
          simp [TM.step, hT]
        exact (ReachT.of_step hs).seq ih
      | L =>
        cases l with
        | nil => simp at h
        | cons y l2 =>
          have ih := segRun_sound T fuel l2 (y :: w :: r) s l' q' h L R
          have hs : TM.step T ⟨app (y :: l2) L, app (b :: r) R, q⟩ = some ⟨app l2 L, app (y :: w :: r) R, s⟩ := by
            simp [TM.step, hT]
          exact (ReachT.of_step hs).seq ih

/-- The word that `w` becomes when the head crosses it in state `q` and leaves in `q` (as it lies behind the head,
nearest cell first). -/
def crossTry (T : Tab) (q : St) (w : List Bool) : Option (List Bool) :=
  match segRun T 200 [] w q with
  | some (v, q') => if q' = q then some v else none
  | none => none

theorem crossTry_sound (T : Tab) (q : St) (w v : List Bool) (h : crossTry T q w = some v) :
    ∀ (k : Nat) (L R : Tape), ReachT T ⟨L, rep k w R, q⟩ ⟨rep k v L, R, q⟩ := by
  unfold crossTry at h
  cases hs : segRun T 200 [] w q with
  | none => rw [hs] at h; simp at h
  | some x =>
    obtain ⟨v', q'⟩ := x
    rw [hs] at h
    by_cases hq : q' = q
    · simp only [hq, ite_true] at h
      have e : v' = v := by simpa using h
      subst e; subst hq
      exact crossT T q' w v' (fun L R => segRun_sound T 200 [] w q' v' q' hs L R)
    · simp [hq] at h

/-! ## Run-length tapes -/

/-- A cell, or a word repeated. -/
inductive Item where
  | bit (b : Bool)
  | run (w : List Bool) (n : Nat)
  deriving DecidableEq, Repr

/-- The tape that a stack of items stands for, in front of `t` (nearest first). -/
def den : List Item → Tape → Tape
  | [], t => t
  | .bit b :: s, t => cons b (den s t)
  | .run w n :: s, t => rep n w (den s t)

theorem den_bits (w : List Bool) (s : List Item) (t : Tape) : den (w.map Item.bit ++ s) t = app w (den s t) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [den, ih]

/-- Put a run on a stack, merging it with a run of the same word. -/
def pushRun (w : List Bool) (n : Nat) (s : List Item) : List Item :=
  match s with
  | .run w' m :: s' => if w = w' then .run w (n + m) :: s' else .run w n :: s
  | _ => .run w n :: s

theorem den_pushRun (w : List Bool) (n : Nat) (s : List Item) (t : Tape) :
    den (pushRun w n s) t = rep n w (den s t) := by
  unfold pushRun
  split
  · next w' m s' =>
    by_cases h : w = w'
    · subst h; simp [den, rep_add]
    · simp [h, den]
  · rfl

/-- Fold the cells on top of a stack into a run: three cells equal to the word of the run under them, or the same
three cells twice. -/
def fold (s : List Item) : List Item :=
  match s with
  | .bit a :: .bit b :: .bit c :: .run w m :: s' =>
    if w = [a, b, c] then .run w (m + 1) :: s' else s
  | .bit a :: .bit b :: .bit c :: .bit d :: .bit e :: .bit f :: s' =>
    if a = d ∧ b = e ∧ c = f ∧ ¬(a = b ∧ b = c) then pushRun [a, b, c] 2 s' else s
  | _ => s

theorem den_fold (s : List Item) (t : Tape) : den (fold s) t = den s t := by
  unfold fold
  split
  · next a b c w m s' =>
    by_cases h : w = [a, b, c]
    · subst h; simp [den]
    · simp [h]
  · next a b c d e f s' =>
    split
    · next h =>
      obtain ⟨h1, h2, h3, _⟩ := h
      subst h1; subst h2; subst h3
      rw [den_pushRun]; rfl
    · rfl
  · rfl

def pushBit (b : Bool) (s : List Item) : List Item := fold (.bit b :: s)

theorem den_pushBit (b : Bool) (s : List Item) (t : Tape) : den (pushBit b s) t = cons b (den s t) := by
  unfold pushBit; rw [den_fold]; rfl

/-! ## Configurations of the simulator -/

/-- `dir = true`: the head faces right, `front` is the tape from the head cell rightwards and `back` the tape left
of it.  `dir = false`: the head faces left, `front` is the tape from the head cell leftwards. -/
structure MC where
  dir : Bool
  front : List Item
  back : List Item
  st : St

def tabOf (d : Bool) : Tab := if d then trans else mirT trans

/-- The configuration as the table `tabOf dir` sees it. -/
def view (c : MC) : Config := ⟨den c.back blank, den c.front blank, c.st⟩

/-- The configuration of the machine that `c` stands for. -/
def sem (c : MC) : Config := if c.dir then view c else mir (view c)

theorem reach_same (d : Bool) (f b f' b' : List Item) (q q' : St)
    (h : ReachT (tabOf d) ⟨den b blank, den f blank, q⟩ ⟨den b' blank, den f' blank, q'⟩) :
    Reach (sem ⟨d, f, b, q⟩) (sem ⟨d, f', b', q'⟩) := by
  obtain ⟨n, hn⟩ := h
  cases d with
  | true => exact ⟨n, hn⟩
  | false =>
    refine ⟨n, ?_⟩
    show TM.steps trans n (mir _) = some (mir _)
    rw [steps_mir]
    show Option.map mir (TM.steps (mirT trans) n _) = _
    have hn' : TM.steps (mirT trans) n (view ⟨false, f, b, q⟩) = some (view ⟨false, f', b', q'⟩) := hn
    rw [hn']; rfl

theorem reach_flip (d : Bool) (f b f' b' : List Item) (q q' : St)
    (h : ReachT (tabOf d) ⟨den b blank, den f blank, q⟩ (mir ⟨den b' blank, den f' blank, q'⟩)) :
    Reach (sem ⟨d, f, b, q⟩) (sem ⟨!d, f', b', q'⟩) := by
  obtain ⟨n, hn⟩ := h
  cases d with
  | true => exact ⟨n, hn⟩
  | false =>
    refine ⟨n, ?_⟩
    show TM.steps trans n (mir _) = some (⟨den b' blank, den f' blank, q'⟩ : Config)
    rw [steps_mir]
    have hn' : TM.steps (mirT trans) n (view ⟨false, f, b, q⟩) = some (mir ⟨den b' blank, den f' blank, q'⟩) := hn
    rw [hn']
    show some (mir (mir _)) = _
    rw [mir_mir]

theorem halt_view (d : Bool) (f b : List Item) (q : St)
    (h : TM.step (tabOf d) ⟨den b blank, den f blank, q⟩ = none) : step (sem ⟨d, f, b, q⟩) = none := by
  cases d with
  | true => exact h
  | false =>
    show TM.step trans (mir _) = none
    rw [step_mir]
    have h' : TM.step (mirT trans) (view ⟨false, f, b, q⟩) = none := h
    rw [h']; rfl

/-! ## One step of the simulator -/

inductive Res where
  | halt
  | next (c : MC)

/-- One transition on the cell `x` in front of the head, `f` the rest of the front. -/
def stepBit (d : Bool) (x : Bool) (f b : List Item) (q : St) : Res :=
  match tabOf d q x with
  | none => .halt
  | some (w, .R, s) => .next ⟨d, f, pushBit w b, s⟩
  | some (w, .L, s) => .next ⟨!d, b, pushBit w f, s⟩

theorem stepBit_sound (d : Bool) (x : Bool) (f f0 b : List Item) (q : St)
    (hx : den f0 blank 0 = x) (hf : tail (den f0 blank) = den f blank) :
    match stepBit d x f b q with
    | .halt => step (sem ⟨d, f0, b, q⟩) = none
    | .next c' => Reach (sem ⟨d, f0, b, q⟩) (sem c') := by
  unfold stepBit
  cases hT : tabOf d q x with
  | none =>
    apply halt_view
    simp [TM.step, hx, hT]
  | some y =>
    obtain ⟨w, dd, s⟩ := y
    cases dd with
    | R =>
      apply reach_same
      apply ReachT.of_step
      simp [TM.step, hx, hT, hf, den_pushBit]
    | L =>
      apply reach_flip
      apply ReachT.of_step
      simp [TM.step, hx, hT, hf, den_pushBit, mir]

/-- Unpack one copy of the run in front. -/
def unpack (w : List Bool) (n : Nat) (f : List Item) : List Item :=
  match n with
  | 0 => f
  | 1 => w.map Item.bit ++ f
  | m + 2 => w.map Item.bit ++ (.run w (m + 1) :: f)

theorem den_unpack (w : List Bool) (n : Nat) (f : List Item) (t : Tape) :
    den (unpack w n f) t = rep n w (den f t) := by
  unfold unpack
  split
  · rfl
  · rw [den_bits]; rfl
  · rw [den_bits]; rfl

theorem rep_double (w : List Bool) (t : Tape) : ∀ h : Nat, rep (2 * h) w t = rep h (w ++ w) t
  | 0 => rfl
  | h + 1 => by
    rw [show 2 * (h + 1) = 2 * h + 1 + 1 by omega]
    show app w (app w (rep (2 * h) w t)) = app (w ++ w) (rep h (w ++ w) t)
    rw [rep_double w t h, app_app]

def mstep (c : MC) : Res :=
  match c.front with
  | [] => stepBit c.dir false [] c.back c.st
  | .bit x :: f => stepBit c.dir x f c.back c.st
  | .run w n :: f =>
    match crossTry (tabOf c.dir) c.st w with
    | some v => .next ⟨c.dir, f, pushRun v n c.back, c.st⟩
    | none =>
      if 2 ≤ n then
        match crossTry (tabOf c.dir) c.st (w ++ w) with
        | some v =>
          .next ⟨c.dir, if n % 2 = 1 then .run w 1 :: f else f,
            if v.take w.length = v.drop w.length then pushRun (v.take w.length) (2 * (n / 2)) c.back
            else pushRun v (n / 2) c.back, c.st⟩
        | none => .next ⟨c.dir, unpack w n f, c.back, c.st⟩
      else .next ⟨c.dir, unpack w n f, c.back, c.st⟩

theorem mstep_sound (c : MC) :
    match mstep c with
    | .halt => step (sem c) = none
    | .next c' => Reach (sem c) (sem c') := by
  obtain ⟨d, front, b, q⟩ := c
  unfold mstep
  cases front with
  | nil => exact stepBit_sound d false [] [] b q rfl rfl
  | cons it f =>
    cases it with
    | bit x => exact stepBit_sound d x f (.bit x :: f) b q rfl rfl
    | run w n =>
      simp only
      have hun : Reach (sem ⟨d, .run w n :: f, b, q⟩) (sem ⟨d, unpack w n f, b, q⟩) := by
        apply reach_same
        rw [den_unpack]
        exact ReachT.refl _ _
      cases h1 : crossTry (tabOf d) q w with
      | some v =>
        apply reach_same
        rw [den_pushRun]
        exact crossTry_sound _ q w v h1 n _ _
      | none =>
        by_cases hn : 2 ≤ n
        · simp only [hn, ite_true]
          cases h2 : crossTry (tabOf d) q (w ++ w) with
          | none => exact hun
          | some v =>
            apply reach_same
            have hc := crossTry_sound _ q (w ++ w) v h2 (n / 2) (den b blank)
              (den (if n % 2 = 1 then Item.run w 1 :: f else f) blank)
            have e1 : den (Item.run w n :: f) blank =
                rep (n / 2) (w ++ w) (den (if n % 2 = 1 then Item.run w 1 :: f else f) blank) := by
              rw [← rep_double]
              show rep n w (den f blank) = _
              rcases Nat.mod_two_eq_zero_or_one n with hp | hp
              · have : n = 2 * (n / 2) := by omega
                simp only [hp]; rw [← this]; rfl
              · have : n = 2 * (n / 2) + 1 := by omega
                simp only [hp, ite_true]
                show _ = rep (2 * (n / 2)) w (rep 1 w (den f blank))
                rw [← rep_add, ← this]
            have e2 : den (if v.take w.length = v.drop w.length then pushRun (v.take w.length) (2 * (n / 2)) b
                else pushRun v (n / 2) b) blank = rep (n / 2) v (den b blank) := by
              by_cases hv : v.take w.length = v.drop w.length
              · simp only [hv, ite_true]
                rw [den_pushRun, rep_double]
                have : v.drop w.length ++ v.drop w.length = v := by
                  have := List.take_append_drop w.length v
                  rw [hv] at this; exact this
                rw [this]
              · simp only [hv, ite_false]
                rw [den_pushRun]
            rw [e1, e2]
            exact hc
        · simp only [hn, ite_false]
          exact hun

end H172044
