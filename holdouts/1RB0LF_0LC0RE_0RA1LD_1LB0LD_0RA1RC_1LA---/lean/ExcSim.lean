import TM.RLE

/-!
# A run-length simulator for excursions, proved for every tape on the left

`TM/RLE.lean` simulates a whole tape that is blank far out on both sides.  An *excursion* (`ResetMap.lean`) is a
run that starts with a few known cells `u` on the left of the head, works only on the tape to the right of them,
and ends when the head steps off the left end of `u`; it has to be proved for **every** tape `L` further left.
This file is the same simulator with the left side ending in an arbitrary tape `L` instead of blank tape:

* `dB L s`: the side `s` (runs, nearest first) in front of the tape `L`; the right side ends in `blank`;
* the moves never read past the end of the left side: `popB` and `peelB` fail there (`popB_some`, `peelB_spec`
  hold for every base tape), and a left step off the end is the *exit* of the excursion;
* moves: a crossing of a run on the right (`xcrossR`) or on the left (`xcrossL`), both by `cross_r` / `cross_l` of
  `TM/Basic.lean` from one bounded run on a finite piece (`bsteps_spec`), or one ordinary step (`xstep`).  Each move
  takes a number of steps that does not depend on `L` (`xmove_spec`);
* `xrun_spec`: if the simulator reaches the exit, then there is one `n` such that for **every** `L` the machine
  goes in `n` steps from the start to `L`'s first cell, with the exit's cells on the right.

As in `RLE.lean`, only the soundness of each move is proved; which move is tried when is unverified search, and
a bad choice can only make the simulator fail.  The checks of `ResetExc.lean` run it by `native_decide`.
-/

namespace TM
namespace EX

variable {Q : Type}

/-! ## Sides in front of any tape -/

/-- The side `s` (runs nearest first) in front of the tape `b`. -/
def dB (b : Tape) : Side → Tape
  | [] => b
  | (w, n) :: s => rep n w (dB b s)

@[simp] theorem dB_nil (b : Tape) : dB b [] = b := rfl
@[simp] theorem dB_cons (b : Tape) (w : List Bool) (n : Nat) (s : Side) :
    dB b ((w, n) :: s) = rep n w (dB b s) := rfl

theorem dB_pushCells (b : Tape) (u : List Bool) (s : Side) : dB b (pushCells u s) = app u (dB b s) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [pushCells, ih]

/-- A run in front, dropped when it is empty. -/
def rz (w : List Bool) (n : Nat) (s : Side) : Side := if n = 0 then s else (w, n) :: s

theorem dB_rz (b : Tape) (w : List Bool) (n : Nat) (s : Side) : dB b (rz w n s) = rep n w (dB b s) := by
  unfold rz; split
  · rename_i h; subst h; rfl
  · rfl

/-- The first cell and the rest, or `none` at the end of the side (the base tape is never read). -/
def popB : Side → Option (Bool × Side)
  | [] => none
  | ([], _) :: s => popB s
  | (_, 0) :: s => popB s
  | (a :: w, n + 1) :: s => some (a, pushCells w (rz (a :: w) n s))

theorem popB_some : ∀ (s : Side) (a : Bool) (s' : Side), popB s = some (a, s') →
    ∀ b, dB b s = cons a (dB b s')
  | [], _, _, h, _ => by simp [popB] at h
  | ([], n) :: s, a, s', h, b => by
    simp only [popB] at h
    simp only [dB_cons, rep_nil_word]
    exact popB_some s a s' h b
  | (_ :: _, 0) :: s, a, s', h, b => by
    simp only [popB] at h
    simp only [dB_cons, rep_zero]
    exact popB_some s a s' h b
  | (c :: w, n + 1) :: s, a, s', h, b => by
    simp only [popB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [dB_cons, rep_succ, dB_pushCells, dB_rz, app_cons]

theorem popB_none : ∀ (s : Side), popB s = none → ∀ b, dB b s = b
  | [], _, _ => rfl
  | ([], n) :: s, h, b => by
    simp only [popB] at h
    simp only [dB_cons, rep_nil_word]
    exact popB_none s h b
  | (_ :: _, 0) :: s, h, b => by
    simp only [popB] at h
    simp only [dB_cons, rep_zero]
    exact popB_none s h b
  | (_ :: _, _ + 1) :: _, h, _ => by simp [popB] at h

/-- The first `j` cells, or `none` if the side has fewer. -/
def peelB : Nat → Side → Option (List Bool × Side)
  | 0, s => some ([], s)
  | j + 1, s =>
    match popB s with
    | none => none
    | some (a, s1) =>
      match peelB j s1 with
      | none => none
      | some (u, s2) => some (a :: u, s2)

theorem peelB_spec : ∀ (j : Nat) (s : Side) (u : List Bool) (s' : Side), peelB j s = some (u, s') →
    ∀ b, dB b s = app u (dB b s')
  | 0, s, u, s', h, b => by simp [peelB] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | j + 1, s, u, s', h, b => by
    simp only [peelB] at h
    cases e : popB s with
    | none => rw [e] at h; cases h
    | some p =>
      obtain ⟨a, s1⟩ := p
      rw [e] at h
      simp only at h
      cases e2 : peelB j s1 with
      | none => rw [e2] at h; cases h
      | some p2 =>
        obtain ⟨u', s2⟩ := p2
        rw [e2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [popB_some s a s1 e b, peelB_spec j s1 u' s2 e2 b]
        rfl

/-- The first `j` cells when they are literal runs `([b], 1)` (so no run is split), else `none`. -/
def peelLB : Nat → Side → Option (List Bool × Side)
  | 0, s => some ([], s)
  | j + 1, ([b], 1) :: s =>
    match peelLB j s with
    | some (u, s') => some (b :: u, s')
    | none => none
  | _ + 1, _ => none

theorem peelLB_spec : ∀ (j : Nat) (s : Side) (u : List Bool) (s' : Side), peelLB j s = some (u, s') →
    ∀ b, dB b s = app u (dB b s')
  | 0, s, u, s', h, b => by simp [peelLB] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | j + 1, ([c], 1) :: s, u, s', h, b => by
    simp only [peelLB] at h
    cases e : peelLB j s with
    | none => rw [e] at h; cases h
    | some p =>
      obtain ⟨u', s''⟩ := p
      rw [e] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [peelLB_spec j s u' s'' e b]
  | j + 1, [], _, _, h, _ => by simp [peelLB] at h
  | j + 1, ([], _) :: _, _, _, h, _ => by simp [peelLB] at h
  | j + 1, ([_], 0) :: _, _, _, h, _ => by simp [peelLB] at h
  | j + 1, ([_], _ + 2) :: _, _, _, h, _ => by simp [peelLB] at h
  | j + 1, (_ :: _ :: _, _) :: _, _, _, h, _ => by simp [peelLB] at h

/-- The first cell of the right side (blank past its end) and the rest. -/
def popR (s : Side) : Bool × Side :=
  match popB s with
  | some p => p
  | none => (false, [])

theorem popR_spec (s : Side) : dB blank s = cons (popR s).1 (dB blank (popR s).2) := by
  unfold popR
  cases e : popB s with
  | some p => obtain ⟨a, s'⟩ := p; exact popB_some s a s' e blank
  | none => rw [popB_none s e blank]; exact cons_false_blank.symm

/-- A run in front, merged with the first run when that is the same word. -/
def rc (w : List Bool) (n : Nat) (s : Side) : Side :=
  match s with
  | (w', m) :: s' => if w' = w then (w, n + m) :: s' else (w, n) :: s
  | [] => [(w, n)]

theorem dB_rc (b : Tape) (w : List Bool) (n : Nat) (s : Side) : dB b (rc w n s) = rep n w (dB b s) := by
  unfold rc
  match s with
  | [] => rfl
  | (w', m) :: s' =>
    simp only
    split
    · rename_i h; subst h; simp [rep_add]
    · rfl

/-- Fold literal cells in front into a run of one of the words `ws` (as `TM.fold`, taking literal cells only). -/
def nrm (ws : List (List Bool)) (s : Side) : Side :=
  match s with
  | (_, 1) :: _ =>
    match ws with
    | [] => s
    | w :: ws' =>
      match peelLB w.length s with
      | some (u, s1) =>
        if u = w then
          match s1 with
          | (w', m) :: r => if w' = w then (w, m + 1) :: r else
              match peelLB w.length s1 with
              | some (u2, s2) => if u2 = w then rc w 2 s2 else nrm ws' s
              | none => nrm ws' s
          | [] => nrm ws' s
        else nrm ws' s
      | none => nrm ws' s
  | _ => s

theorem dB_nrm (b : Tape) (ws : List (List Bool)) (s : Side) : dB b (nrm ws s) = dB b s := by
  induction ws with
  | nil => unfold nrm; split <;> rfl
  | cons w ws ih =>
    unfold nrm
    split
    · rename_i c t
      simp only
      cases e1 : peelLB w.length ((c, 1) :: t) with
      | none => exact ih
      | some p =>
        obtain ⟨u, s1⟩ := p
        simp only
        have h1 := peelLB_spec _ _ _ _ e1 b
        split
        · rename_i hu
          subst hu
          match s1, h1 with
          | [], h1 => exact ih
          | (w', m) :: r, h1 =>
            simp only
            split
            · rename_i hw; subst hw; rw [h1]; simp [rep_succ]
            · cases e2 : peelLB u.length ((w', m) :: r) with
              | none => exact ih
              | some p2 =>
                obtain ⟨u2, s2⟩ := p2
                simp only
                split
                · rename_i hu2
                  subst hu2
                  rw [h1, peelLB_spec _ _ _ _ e2 b, dB_rc]; simp [rep_succ]
                · exact ih
        · exact ih
    · rfl

/-- A list of cells as a right side, folded into runs from the far end. -/
def ofList (ws : List (List Bool)) : List Bool → Side
  | [] => []
  | a :: l => nrm ws (([a], 1) :: ofList ws l)

theorem dB_ofList (b : Tape) (ws : List (List Bool)) : ∀ l, dB b (ofList ws l) = app l (dB b []) := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [ofList, dB_nrm, dB_cons, rep_one, ih]; rfl

/-! ## Configurations and moves -/

/-- A configuration: left side (in front of an unknown tape), right side (in front of blank), state. -/
structure XC (Q : Type) where
  l : Side
  r : Side
  q : Q

/-- The configuration with the tape `L` beyond the left side. -/
def XC.cfg (L : Tape) (c : XC Q) : Cfg Q := ⟨dB L c.l, dB blank c.r, c.q⟩

section
variable [DecidableEq Q] (δ : Q → Bool → Option (Bool × Dir × Q)) (ws : List (List Bool))

/-- Cross a run `w^n` on the right, carrying `j` literal cells of the left side. -/
def xcrossR (j : Nat) (c : XC Q) : Option (XC Q × Nat) :=
  match c.r with
  | (w, n) :: r' =>
    if w.length < 2 then none else
    match peelB j c.l with
    | none => none
    | some (u, l'') =>
      match findR δ (8 * (w.length + u.length) + 16) 0 (u, w, c.q) with
      | none => none
      | some s =>
        match bsteps δ s (u, w, c.q) with
        | some (ll, [], q') =>
          if q' = c.q ∧ ll.take u.length = u then
            some (⟨pushCells u (rc (ll.drop u.length) n l''), r', c.q⟩, n * s)
          else none
        | _ => none
  | [] => none

theorem xcrossR_spec (j : Nat) (c c' : XC Q) (n : Nat) (h : xcrossR δ j c = some (c', n)) (L : Tape) :
    steps δ n (c.cfg L) = some (c'.cfg L) := by
  obtain ⟨l, r, q⟩ := c
  unfold xcrossR at h
  simp only at h
  match r, h with
  | (w, k) :: r', h =>
    simp only at h
    split at h
    · cases h
    cases ep : peelB j l with
    | none => rw [ep] at h; cases h
    | some p =>
      obtain ⟨u, l''⟩ := p
      rw [ep] at h
      simp only at h
      cases ef : findR δ (8 * (w.length + u.length) + 16) 0 (u, w, q) with
      | none => rw [ef] at h; cases h
      | some s =>
        rw [ef] at h
        simp only at h
        cases eb : bsteps δ s (u, w, q) with
        | none => rw [eb] at h; cases h
        | some t =>
          obtain ⟨ll, rr, q'⟩ := t
          rw [eb] at h
          match rr, h with
          | [], h =>
            simp only at h
            split at h
            · rename_i hc
              obtain ⟨hq, hu⟩ := hc
              subst hq
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hll : ll = u ++ ll.drop u.length := by
                conv => lhs; rw [← List.take_append_drop u.length ll]
                rw [hu]
              have h1 : ∀ L R : Tape, steps δ s ⟨app u L, app w R, q'⟩ =
                  some ⟨app u (app (ll.drop u.length) L), R, q'⟩ := by
                intro L R
                have := bsteps_spec δ s eb L R
                rw [hll, ← app_app] at this
                simpa using this
              have h2 := cross_r δ h1 k (dB L l'') (dB blank r')
              simp only [XC.cfg, dB_cons]
              rw [peelB_spec j l u l'' ep L, dB_pushCells, dB_rc]
              exact h2
            · cases h
          | _ :: _, h => cases h

/-- Cross a run `w^n` on the left, carrying `j` literal cells of the right side. -/
def xcrossL (j : Nat) (c : XC Q) : Option (XC Q × Nat) :=
  match c.l with
  | (w, n) :: l' =>
    if w.length < 2 then none else
    match peelB j c.r with
    | none => none
    | some (u, r'') =>
      match findL δ c.q u (8 * (w.length + u.length) + 16) 0 (w, u, c.q) with
      | none => none
      | some s =>
        match bsteps δ s (w, u, c.q) with
        | some ([], rr, q') =>
          if q' = c.q ∧ rr.take u.length = u then
            some (⟨l', pushCells u (rc (rr.drop u.length) n r''), c.q⟩, n * s)
          else none
        | _ => none
  | [] => none

theorem xcrossL_spec (j : Nat) (c c' : XC Q) (n : Nat) (h : xcrossL δ j c = some (c', n)) (L : Tape) :
    steps δ n (c.cfg L) = some (c'.cfg L) := by
  obtain ⟨l, r, q⟩ := c
  unfold xcrossL at h
  simp only at h
  match l, h with
  | (w, k) :: l', h =>
    simp only at h
    split at h
    · cases h
    cases ep : peelB j r with
    | none => rw [ep] at h; cases h
    | some p =>
      obtain ⟨u, r''⟩ := p
      rw [ep] at h
      simp only at h
      cases ef : findL δ q u (8 * (w.length + u.length) + 16) 0 (w, u, q) with
      | none => rw [ef] at h; cases h
      | some s =>
        rw [ef] at h
        simp only at h
        cases eb : bsteps δ s (w, u, q) with
        | none => rw [eb] at h; cases h
        | some t =>
          obtain ⟨ll, rr, q'⟩ := t
          rw [eb] at h
          match ll, h with
          | [], h =>
            simp only at h
            split at h
            · rename_i hc
              obtain ⟨hq, hu⟩ := hc
              subst hq
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hrr : rr = u ++ rr.drop u.length := by
                conv => lhs; rw [← List.take_append_drop u.length rr]
                rw [hu]
              have h1 : ∀ L R : Tape, steps δ s ⟨app w L, app u R, q'⟩ =
                  some ⟨L, app u (app (rr.drop u.length) R), q'⟩ := by
                intro L R
                have := bsteps_spec δ s eb L R
                rw [hrr, ← app_app] at this
                simpa using this
              have h2 := cross_l δ h1 k (dB L l') (dB blank r'')
              simp only [XC.cfg, dB_cons]
              rw [peelB_spec j r u r'' ep blank, dB_pushCells, dB_rc]
              exact h2
            · cases h
          | _ :: _, h => cases h

/-- The result of one move: a configuration after some steps, or the exit (state, written cell, right side):
the head has stepped off the left end of the left side. -/
abbrev Res (Q : Type) := Sum (XC Q × Nat) (Q × Bool × Side)

/-- One ordinary step; `none` on a halt. -/
def xstep (c : XC Q) : Option (Res Q) :=
  match δ c.q (popR c.r).1 with
  | none => none
  | some (w, .R, s) => some (.inl (⟨nrm ws (([w], 1) :: c.l), (popR c.r).2, s⟩, 1))
  | some (w, .L, s) =>
    match popB c.l with
    | none => some (.inr (s, w, (popR c.r).2))
    | some (a, l') => some (.inl (⟨l', nrm ws (([a], 1) :: ([w], 1) :: (popR c.r).2), s⟩, 1))

/-- What a result means, for the tape `L` on the left. -/
def Res.cfg (L : Tape) : Res Q → Cfg Q
  | .inl (c, _) => c.cfg L
  | .inr (s, w, r) => ⟨tail L, cons (L 0) (cons w (dB blank r)), s⟩

/-- The number of steps of a result. -/
def Res.n : Res Q → Nat
  | .inl (_, n) => n
  | .inr _ => 1

omit [DecidableEq Q] in
theorem xstep_spec (c : XC Q) (x : Res Q) (h : xstep δ ws c = some x) (L : Tape) :
    steps δ x.n (c.cfg L) = some (x.cfg L) := by
  obtain ⟨l, r, q⟩ := c
  have hr := popR_spec r
  unfold xstep at h
  simp only at h
  have st : ∀ c', step δ (XC.cfg L ⟨l, r, q⟩) = some c' → steps δ 1 (XC.cfg L ⟨l, r, q⟩) = some c' := by
    intro c' e; simp [steps, e]
  cases et : δ q (popR r).1 with
  | none => rw [et] at h; cases h
  | some t =>
    obtain ⟨w, d, s⟩ := t
    rw [et] at h
    cases d with
    | R =>
      simp only [Option.some.injEq] at h
      subst h
      apply st
      simp only [step, XC.cfg, Res.cfg]
      rw [hr, cons_zero, et]
      simp only [tail_cons, dB_nrm, dB_cons, rep_one, app_cons, app_nil]
    | L =>
      simp only at h
      cases el : popB l with
      | none =>
        rw [el] at h
        simp only [Option.some.injEq] at h
        subst h
        apply st
        simp only [step, XC.cfg, Res.cfg]
        rw [hr, cons_zero, et, popB_none l el L]
        simp only [tail_cons]
      | some p =>
        obtain ⟨a, l'⟩ := p
        rw [el] at h
        simp only [Option.some.injEq] at h
        subst h
        apply st
        simp only [step, XC.cfg, Res.cfg]
        rw [hr, cons_zero, et, popB_some l a l' el L]
        simp only [tail_cons, cons_zero, dB_nrm, dB_cons, rep_one, app_cons, app_nil]

/-- `a`, or else `f ()`. -/
def orX {α : Type} (a : Option α) (f : Unit → Option α) : Option α :=
  match a with
  | some x => some x
  | none => f ()

theorem orX_cases {α : Type} {a : Option α} {f : Unit → Option α} {x : α} (h : orX a f = some x) :
    a = some x ∨ f () = some x := by
  unfold orX at h
  cases a with
  | some y => left; exact h
  | none => right; exact h

/-- A crossing as a result. -/
def asRes (x : Option (XC Q × Nat)) : Option (Res Q) := x.map Sum.inl

/-- One move: a crossing on the right (0 to 3 carried cells), on the left (0 to 3), else one step. -/
def xmove (c : XC Q) : Option (Res Q) :=
  orX (asRes (xcrossR δ 0 c)) fun _ => orX (asRes (xcrossR δ 1 c)) fun _ =>
  orX (asRes (xcrossR δ 2 c)) fun _ => orX (asRes (xcrossR δ 3 c)) fun _ =>
  orX (asRes (xcrossL δ 0 c)) fun _ => orX (asRes (xcrossL δ 1 c)) fun _ =>
  orX (asRes (xcrossL δ 2 c)) fun _ => orX (asRes (xcrossL δ 3 c)) fun _ => xstep δ ws c

theorem asRes_R (j : Nat) (c : XC Q) (x : Res Q) (h : asRes (xcrossR δ j c) = some x) (L : Tape) :
    steps δ x.n (c.cfg L) = some (x.cfg L) := by
  unfold asRes at h
  cases e : xcrossR δ j c with
  | none => rw [e] at h; cases h
  | some p =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨c', n⟩ := p
    exact xcrossR_spec δ j c c' n e L

theorem asRes_L (j : Nat) (c : XC Q) (x : Res Q) (h : asRes (xcrossL δ j c) = some x) (L : Tape) :
    steps δ x.n (c.cfg L) = some (x.cfg L) := by
  unfold asRes at h
  cases e : xcrossL δ j c with
  | none => rw [e] at h; cases h
  | some p =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨c', n⟩ := p
    exact xcrossL_spec δ j c c' n e L

theorem xmove_spec (c : XC Q) (x : Res Q) (h : xmove δ ws c = some x) (L : Tape) :
    steps δ x.n (c.cfg L) = some (x.cfg L) := by
  unfold xmove at h
  rcases orX_cases h with h | h; exact asRes_R δ _ c x h L
  rcases orX_cases h with h | h; exact asRes_R δ _ c x h L
  rcases orX_cases h with h | h; exact asRes_R δ _ c x h L
  rcases orX_cases h with h | h; exact asRes_R δ _ c x h L
  rcases orX_cases h with h | h; exact asRes_L δ _ c x h L
  rcases orX_cases h with h | h; exact asRes_L δ _ c x h L
  rcases orX_cases h with h | h; exact asRes_L δ _ c x h L
  rcases orX_cases h with h | h; exact asRes_L δ _ c x h L
  exact xstep_spec δ ws c x h L

/-- Run to the exit (or fail: a halt, or the fuel runs out). -/
def xrun : Nat → XC Q → Option (Q × Bool × Side)
  | 0, _ => none
  | fuel + 1, c =>
    match xmove δ ws c with
    | none => none
    | some (.inl (c', _)) => xrun fuel c'
    | some (.inr e) => some e

theorem xrun_spec : ∀ (fuel : Nat) (c : XC Q) (s : Q) (w : Bool) (r : Side), xrun δ ws fuel c = some (s, w, r) →
    ∃ n, ∀ L, steps δ n (c.cfg L) = some ⟨tail L, cons (L 0) (cons w (dB blank r)), s⟩
  | 0, _, _, _, _, h => by simp [xrun] at h
  | fuel + 1, c, s, w, r, h => by
    simp only [xrun] at h
    cases e : xmove δ ws c with
    | none => rw [e] at h; cases h
    | some x =>
      rw [e] at h
      match x, h, e with
      | .inl (c', k), h, e =>
        simp only at h
        obtain ⟨m, hm⟩ := xrun_spec fuel c' s w r h
        exact ⟨k + m, fun L => steps_seq δ (xmove_spec δ ws c _ e L) (hm L)⟩
      | .inr e', h, e =>
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨1, fun L => xmove_spec δ ws c _ e L⟩

/-- **An excursion, checked.**  Start with the cells `u` (nearest first) on the left and the right side `T`, in
state `q`; on success, the exit is in state `q'` with the cells `v` (reading order) in front of the returned side. -/
def exc (fuel : Nat) (u : List Bool) (q q' : Q) (v : List Bool) (T : Side) : Option Side :=
  match xrun δ ws fuel ⟨pushCells u [], T, q⟩ with
  | none => none
  | some (s, w, r) =>
    if s = q' then
      match peelB (v.length - 1) r with
      | some (v', r') => if v = w :: v' then some r' else none
      | none => none
    else none

theorem exc_spec (fuel : Nat) (u : List Bool) (q q' : Q) (v : List Bool) (T T' : Side)
    (h : exc δ ws fuel u q q' v T = some T') :
    ∃ n, ∀ L, steps δ n ⟨app u L, dB blank T, q⟩ = some ⟨tail L, cons (L 0) (app v (dB blank T')), q'⟩ := by
  unfold exc at h
  cases e : xrun δ ws fuel ⟨pushCells u [], T, q⟩ with
  | none => rw [e] at h; cases h
  | some x =>
    obtain ⟨s, w, r⟩ := x
    rw [e] at h
    simp only at h
    split at h
    · rename_i hs
      subst hs
      cases ep : peelB (v.length - 1) r with
      | none => rw [ep] at h; cases h
      | some p =>
        obtain ⟨v', r'⟩ := p
        rw [ep] at h
        simp only at h
        split at h
        · rename_i hv
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨n, hn⟩ := xrun_spec δ ws fuel _ s w r e
          refine ⟨n, fun L => ?_⟩
          have := hn L
          simp only [XC.cfg, dB_pushCells, dB_nil] at this
          rw [this, hv, peelB_spec _ r v' _ ep blank]
          rfl
        · cases h
    · cases h

end

end EX
end TM
