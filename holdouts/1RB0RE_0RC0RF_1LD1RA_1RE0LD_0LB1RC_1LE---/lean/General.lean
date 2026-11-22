import Pass
import Collapse

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: every sub-round, as one function

`Collapse.lean` covers the sub-rounds of the regular kind (`W` on the interior and `gstep` on the counter).  Here
every sub-round is covered, small gaps and irregular blocks included, by the *pass machine* of `Pass.lean`:

* a moment is `gcfg bs l us`: the head in C on a 0, the last block `l` on its left, then the blocks `bs` (any sizes,
  nearest first, single 0s between them, blank tape after the last), and on its right the zone gaps `us`;
* the sub-round is the left sweep `start`, then a right sweep `pstep` over a state `PS`: the blocks on the left
  (the first is the *open block*, the 1s next to the head), a phase A, E or C (the machine state), `k` ones and
  then the zone gaps `us` on the right;
* `pstep` is total: each state is one move of `Pass.lean`, or the next moment (C on a 0 after a non-empty open
  block), or a halt (A on 011).

`sub` runs one sub-round: `sub_moment` (the next moment, with the exact number of steps) and `sub_halt` (the machine
halts) are its soundness.  `enc_gcfg` relates `gcfg` to the configurations `enc` of `Collapse.lean`.
-/

namespace H4320

open TM

/-! ## Blocks -/

/-- Blocks of 1s, nearest first, separated by single 0s, then blank tape. -/
def blks : List Nat → Tape
  | [] => blank
  | c :: cs => rep c [true] (cons false (blks cs))

/-- A general moment: the head in C on a 0, last block `l`, the blocks `bs` before it, zone gaps `us`. -/
def gcfg (bs : List Nat) (l : Nat) (us : List Nat) : Config :=
  ⟨rep l [true] (cons false (blks bs)), cons false (zr us), .C⟩

theorem blks_pop (cs : List Nat) : blks cs = rep (cs.headD 0) [true] (cons false (blks cs.tail)) := by
  cases cs with
  | nil => simp only [blks, List.headD, List.tail, rep_zero, cons_false_blank]
  | cons c cs => rfl

theorem ones_succ (n : Nat) (X : Tape) : rep (n + 1) [true] X = cons true (rep n [true] X) := rfl

theorem ones_add (a b : Nat) (X : Tape) : rep (a + b) [true] X = rep a [true] (rep b [true] X) := rep_add a b _ X

theorem ones_three (a : Nat) (X : Tape) : rep (3 * a) [true] X = rep a [true, true, true] X := by
  induction a with
  | zero => rfl
  | succ a ih => rw [show 3 * (a + 1) = 3 + 3 * a by omega, ones_add, ih]; rfl

theorem twos (a : Nat) (cs : List Nat) : rep a [true, true, false] (blks cs) = blks (List.replicate a 2 ++ cs) := by
  induction a with
  | zero => rfl
  | succ a ih => rw [rep_succ, ih, List.replicate_succ, List.cons_append]; rfl

theorem open_add (c n : Nat) (cs : List Nat) :
    rep n [true] (blks (c :: cs)) = blks ((c + n) :: cs) := by
  show rep n [true] (rep c [true] _) = rep (c + n) [true] _
  rw [Nat.add_comm, ones_add]

/-- Three more cells on the block nearest the head. -/
theorem grow3 (cs : List Nat) :
    cons true (cons true (cons true (blks cs))) = blks ((cs.headD 0 + 3) :: cs.tail) := by
  rw [← open_add, blks_pop]; rfl

theorem grow2 (cs : List Nat) : cons true (cons true (blks cs)) = blks ((cs.headD 0 + 2) :: cs.tail) := by
  rw [← open_add, blks_pop]; rfl

theorem zr_succ (u : Nat) (us : List Nat) : zr ((u + 1) :: us) = cons false (zr (u :: us)) := rfl

theorem zr_zero (us : List Nat) : zr (0 :: us) = cons true (zr us) := rfl

/-! ## The pass machine -/

/-- The phases of the right sweep: the machine states A, E, C. -/
inductive Ph where
  | A | E | C
  deriving DecidableEq, Repr

def Ph.st : Ph → St
  | .A => .A
  | .E => .E
  | .C => .C

/-- A state of the right sweep: blocks `lb` on the left (the first is the open block), phase, `k` ones and then the
zone gaps `us` on the right. -/
structure PS where
  lb : List Nat
  ph : Ph
  k : Nat
  us : List Nat
  deriving DecidableEq, Repr

def PS.cfg (s : PS) : Config := ⟨blks s.lb, rep s.k [true] (zr s.us), s.ph.st⟩

/-- The result of one move: the next state after `n` steps, the next moment (blocks, last block, gaps) after `n`
steps, or a halt. -/
inductive Res where
  | next (s : PS) (n : Nat)
  | done (bs : List Nat) (l : Nat) (us : List Nat) (n : Nat)
  | halt
  deriving DecidableEq, Repr

/-- The zone after reading one 0 (a first gap of at least 1, or the end of the zone). -/
def rd : List Nat → List Nat
  | [] => []
  | 0 :: us => 0 :: us
  | (u + 1) :: us => u :: us

/-- C on a 0: the next moment, or (empty open block) the two cells become 11. -/
def cMove (lb us : List Nat) : Res :=
  if lb.headD 0 = 0 then .next ⟨(lb.tail.headD 0 + 2) :: lb.tail.tail, .C, 0, rd us⟩ 3
  else .done lb.tail (lb.headD 0) (rd us) 0

/-- E on a 0: the shift (`eshift`), or (empty open block) the two cells become 11 (`ezero`). -/
def eMove (lb us : List Nat) : Res :=
  if lb.headD 0 = 0 then .next ⟨(lb.tail.headD 0 + 2) :: lb.tail.tail, .C, 0, rd us⟩ 5
  else .next ⟨(lb.tail.headD 0 + 3) :: lb.tail.tail, .A, lb.headD 0 - 1, rd us⟩ (3 * (lb.headD 0 - 1) + 9)

/-- One move of the right sweep. -/
def pstep : PS → Res
  | ⟨lb, .A, k + 3, us⟩ => .next ⟨List.replicate ((k + 3) / 3) 2 ++ lb, .A, (k + 3) % 3, us⟩ (3 * ((k + 3) / 3))
  | ⟨lb, .A, k + 1, us⟩ => .next ⟨0 :: lb, .E, k, us⟩ 1
  | ⟨lb, .E, k + 1, us⟩ => .next ⟨(lb.headD 0 + 1) :: lb.tail, .C, k, us⟩ 1
  | ⟨lb, .C, k + 1, us⟩ => .next ⟨(lb.headD 0 + 1) :: lb.tail, .A, k, us⟩ 1
  | ⟨lb, ph, 0, 0 :: us⟩ => .next ⟨lb, ph, 1, us⟩ 0
  | ⟨lb, .C, 0, us⟩ => cMove lb us
  | ⟨lb, .E, 0, us⟩ => eMove lb us
  | ⟨lb, .A, 0, []⟩ => .next ⟨(lb.headD 0 + 3) :: lb.tail, .C, 0, []⟩ 5
  | ⟨lb, .A, 0, (u + 3) :: us⟩ => .next ⟨(lb.headD 0 + 3) :: lb.tail, .C, 0, u :: us⟩ 5
  | ⟨lb, .A, 0, 2 :: us⟩ => .next ⟨1 :: (lb.headD 0 + 1) :: lb.tail, .A, 0, us⟩ 3
  | ⟨_, .A, 0, 1 :: 0 :: _⟩ => .halt
  | ⟨lb, .A, 0, 1 :: us⟩ =>
    .next ⟨(lb.tail.headD 0 + 3) :: lb.tail.tail, .A, lb.headD 0 + 1, rd us⟩ (3 * lb.headD 0 + 12)

/-! ## Soundness of one move -/

/-- The zone, read one 0: a gap list whose first gap is not 0 (or the end of the zone) starts with a 0. -/
theorem zr_read0 (us : List Nat) (h : us.headD 1 ≠ 0) : zr us = cons false (zr (rd us)) := by
  match us, h with
  | [], _ => simp only [rd, zr, cons_false_blank]
  | (u + 1) :: us, _ => rfl

theorem blks_succ_head (lb : List Nat) : cons true (blks lb) = blks ((lb.headD 0 + 1) :: lb.tail) := by
  rw [blks_pop lb]; rfl

theorem ones_snoc (n : Nat) (X : Tape) : rep n [true] (cons true X) = rep (n + 1) [true] X := rep_app_comm n [true] X

theorem open_zero (lb : List Nat) (h : lb.headD 0 = 0) : blks lb = cons false (blks lb.tail) := by
  rw [blks_pop, h]; rfl

theorem cMove_next (lb us : List Nat) (hu : us.headD 1 ≠ 0) (s' : PS) (n : Nat) (h : cMove lb us = .next s' n) :
    steps n (PS.cfg ⟨lb, .C, 0, us⟩) = some s'.cfg := by
  unfold cMove at h
  split at h
  · rename_i h0
    simp only [Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have r := czero (blks lb.tail) (zr (rd us))
    rw [grow2] at r
    show steps 3 ⟨blks lb, rep 0 [true] (zr us), .C⟩ = _
    rw [open_zero lb h0, rep_zero, zr_read0 us hu]; exact r
  · cases h

theorem cMove_done (lb us : List Nat) (hu : us.headD 1 ≠ 0) (bs : List Nat) (l : Nat) (vs : List Nat) (n : Nat)
    (h : cMove lb us = .done bs l vs n) : steps n (PS.cfg ⟨lb, .C, 0, us⟩) = some (gcfg bs l vs) := by
  unfold cMove at h
  split at h
  · cases h
  · simp only [Res.done.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp only [PS.cfg, gcfg, Ph.st, rep_zero, steps_zero]
    rw [← blks_pop, zr_read0 us hu]

theorem eMove_next (lb us : List Nat) (hu : us.headD 1 ≠ 0) (s' : PS) (n : Nat) (h : eMove lb us = .next s' n) :
    steps n (PS.cfg ⟨lb, .E, 0, us⟩) = some s'.cfg := by
  unfold eMove at h
  split at h
  · rename_i h0
    simp only [Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have r := ezero (blks lb.tail) (zr (rd us))
    rw [grow2] at r
    show steps 5 ⟨blks lb, rep 0 [true] (zr us), .E⟩ = _
    rw [open_zero lb h0, rep_zero, zr_read0 us hu]; exact r
  · rename_i h0
    simp only [Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨o, ho⟩ : ∃ o, lb.headD 0 = o + 1 := ⟨lb.headD 0 - 1, by omega⟩
    have r := eshift o (blks lb.tail) (zr (rd us))
    rw [grow3] at r
    show steps _ ⟨blks lb, rep 0 [true] (zr us), .E⟩ = some ⟨_, rep (lb.headD 0 - 1) [true] _, .A⟩
    rw [blks_pop, ho, rep_zero, zr_read0 us hu, show o + 1 - 1 = o by omega]; exact r

theorem pstep_next (s s' : PS) (n : Nat) (h : pstep s = .next s' n) : steps n s.cfg = some s'.cfg := by
  obtain ⟨lb, ph, k, us⟩ := s
  match ph, k, us, h with
  | .A, k + 3, us, h =>
    simp only [pstep, Res.next.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have e := conv ((k + 3) / 3) (blks lb) (rep ((k + 3) % 3) [true] (zr us))
    rw [← ones_three, ← ones_add, show 3 * ((k + 3) / 3) + (k + 3) % 3 = k + 3 by omega, twos] at e
    exact e
  | .A, 1, us, h =>
    simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact aone _ _
  | .A, 2, us, h =>
    simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact aone _ _
  | .E, k + 1, us, h =>
    simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e := eone (blks lb) (rep k [true] (zr us))
    rw [blks_succ_head] at e
    exact e
  | .C, k + 1, us, h =>
    simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e := cone (blks lb) (rep k [true] (zr us))
    rw [blks_succ_head] at e
    exact e
  | .A, 0, 0 :: us, h => simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | .E, 0, 0 :: us, h => simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | .C, 0, 0 :: us, h => simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | .C, 0, [], h => exact cMove_next lb [] (by simp) s' n h
  | .C, 0, (u + 1) :: us, h => exact cMove_next lb _ (by simp) s' n h
  | .E, 0, [], h => exact eMove_next lb [] (by simp) s' n h
  | .E, 0, (u + 1) :: us, h => exact eMove_next lb _ (by simp) s' n h
  | .A, 0, [], h =>
    simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have r := azzz (blks lb) blank
    rw [grow3, cons_false_blank, cons_false_blank, cons_false_blank] at r
    exact r
  | .A, 0, (u + 3) :: us, h =>
    simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have r := azzz (blks lb) (zr (u :: us))
    rw [grow3] at r
    exact r
  | .A, 0, 2 :: us, h =>
    simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have r := azzo (blks lb) (zr us)
    have e : cons true (cons false (cons true (blks lb))) = blks (1 :: (lb.headD 0 + 1) :: lb.tail) := by
      rw [blks_pop lb]; rfl
    rw [e] at r
    exact r
  | .A, 0, 1 :: 0 :: _, h => simp [pstep] at h
  | .A, 0, [1], h =>
    simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have r := azoz (lb.headD 0) (blks lb.tail) blank
    rw [← blks_pop, grow3] at r
    have e : zr [1] = cons false (cons true (cons false blank)) := by
      simp only [zr, rep_succ, rep_zero, app_cons, app_nil, cons_false_blank]
    rw [ones_snoc] at r
    show steps _ ⟨blks lb, rep 0 [true] (zr [1]), .A⟩ = some ⟨_, rep (lb.headD 0 + 1) [true] blank, .A⟩
    rw [e, rep_zero]; exact r
  | .A, 0, 1 :: (v + 1) :: us, h =>
    simp only [pstep, Res.next.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have r := azoz (lb.headD 0) (blks lb.tail) (zr (v :: us))
    rw [← blks_pop, grow3] at r
    rw [ones_snoc] at r
    exact r

theorem pstep_done (s : PS) (bs : List Nat) (l : Nat) (vs : List Nat) (n : Nat) (h : pstep s = .done bs l vs n) :
    steps n s.cfg = some (gcfg bs l vs) := by
  obtain ⟨lb, ph, k, us⟩ := s
  match ph, k, us, h with
  | .A, k + 3, us, h => simp [pstep] at h
  | .A, 1, us, h => simp [pstep] at h
  | .A, 2, us, h => simp [pstep] at h
  | .E, k + 1, us, h => simp [pstep] at h
  | .C, k + 1, us, h => simp [pstep] at h
  | .A, 0, 0 :: us, h => simp [pstep] at h
  | .E, 0, 0 :: us, h => simp [pstep] at h
  | .C, 0, 0 :: us, h => simp [pstep] at h
  | .C, 0, [], h => exact cMove_done lb [] (by simp) bs l vs n h
  | .C, 0, (u + 1) :: us, h => exact cMove_done lb _ (by simp) bs l vs n h
  | .E, 0, [], h => simp [pstep, eMove] at h; split at h <;> cases h
  | .E, 0, (u + 1) :: us, h => simp [pstep, eMove] at h; split at h <;> cases h
  | .A, 0, [], h => simp [pstep] at h
  | .A, 0, (u + 3) :: us, h => simp [pstep] at h
  | .A, 0, 2 :: us, h => simp [pstep] at h
  | .A, 0, 1 :: 0 :: _, h => simp [pstep] at h
  | .A, 0, [1], h => simp [pstep] at h
  | .A, 0, 1 :: (v + 1) :: us, h => simp [pstep] at h

theorem pstep_halt (s : PS) (h : pstep s = .halt) : Halts trans s.cfg := by
  obtain ⟨lb, ph, k, us⟩ := s
  match ph, k, us, h with
  | .A, k + 3, us, h => simp [pstep] at h
  | .A, 1, us, h => simp [pstep] at h
  | .A, 2, us, h => simp [pstep] at h
  | .E, k + 1, us, h => simp [pstep] at h
  | .C, k + 1, us, h => simp [pstep] at h
  | .A, 0, 0 :: us, h => simp [pstep] at h
  | .E, 0, 0 :: us, h => simp [pstep] at h
  | .C, 0, 0 :: us, h => simp [pstep] at h
  | .C, 0, [], h => simp [pstep, cMove] at h; split at h <;> cases h
  | .C, 0, (u + 1) :: us, h => simp [pstep, cMove] at h; split at h <;> cases h
  | .E, 0, [], h => simp [pstep, eMove] at h; split at h <;> cases h
  | .E, 0, (u + 1) :: us, h => simp [pstep, eMove] at h; split at h <;> cases h
  | .A, 0, [], h => simp [pstep] at h
  | .A, 0, (u + 3) :: us, h => simp [pstep] at h
  | .A, 0, 2 :: us, h => simp [pstep] at h
  | .A, 0, 1 :: 0 :: us, _ =>
    obtain ⟨h1, h2⟩ := a011 (blks lb) (zr us)
    exact ⟨2, _, h1, h2⟩
  | .A, 0, [1], h => simp [pstep] at h
  | .A, 0, 1 :: (v + 1) :: us, h => simp [pstep] at h

/-! ## One sub-round -/

/-- The left sweep, from the moment `gcfg bs l us` (last block and the block before it at least 1). -/
def startPS : List Nat → Nat → List Nat → Option (PS × Nat)
  | (p + 1) :: rest, l + 1, us => some (⟨(rest.headD 0 + 3) :: rest.tail, .A, p + 1, l :: us⟩, l + 3 * p + 15)
  | _, _, _ => none

theorem startPS_sound (bs : List Nat) (l : Nat) (us : List Nat) (s : PS) (n : Nat)
    (h : startPS bs l us = some (s, n)) : steps n (gcfg bs l us) = some s.cfg := by
  match bs, l, h with
  | (p + 1) :: rest, l + 1, h =>
    simp only [startPS, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have r := start l p (blks rest) (zr us)
    rw [grow3] at r
    exact r

/-- What a run of the pass machine ends in: the next moment after `n` steps, a halt, or the end of the fuel. -/
inductive Out where
  | moment (bs : List Nat) (l : Nat) (us : List Nat) (n : Nat)
  | halt
  | stuck
  deriving DecidableEq, Repr

def Out.add (m : Nat) : Out → Out
  | .moment bs l us n => .moment bs l us (m + n)
  | o => o

/-- The right sweep, at most `fuel` moves. -/
def runPass : Nat → PS → Out
  | 0, _ => .stuck
  | f + 1, s =>
    match pstep s with
    | .next s' n => (runPass f s').add n
    | .done bs l us n => .moment bs l us n
    | .halt => .halt

theorem runPass_moment : ∀ (f : Nat) (s : PS) (bs : List Nat) (l : Nat) (us : List Nat) (n : Nat),
    runPass f s = .moment bs l us n → steps n s.cfg = some (gcfg bs l us)
  | 0, _, _, _, _, _, h => by simp [runPass] at h
  | f + 1, s, bs, l, us, n, h => by
    simp only [runPass] at h
    cases e : pstep s with
    | next s' m =>
      rw [e] at h; try dsimp only at h
      cases e2 : runPass f s' with
      | moment bs' l' us' n' =>
        rw [e2] at h; try dsimp only at h
        simp only [Out.add, Out.moment.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact steps_seq trans (pstep_next s s' m e) (runPass_moment f s' _ _ _ _ e2)
      | halt => rw [e2] at h; simp [Out.add] at h
      | stuck => rw [e2] at h; simp [Out.add] at h
    | done bs' l' us' m =>
      rw [e] at h; try dsimp only at h
      simp only [Out.moment.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact pstep_done s _ _ _ _ e
    | halt => rw [e] at h; try dsimp only at h; cases h

theorem halts_of_steps {n : Nat} {c c' : Config} (h : steps n c = some c') (h' : Halts trans c') :
    Halts trans c := by
  obtain ⟨m, d, h1, h2⟩ := h'
  exact ⟨n + m, d, steps_seq trans h h1, h2⟩

theorem runPass_halt : ∀ (f : Nat) (s : PS), runPass f s = .halt → Halts trans s.cfg
  | 0, _, h => by simp [runPass] at h
  | f + 1, s, h => by
    simp only [runPass] at h
    cases e : pstep s with
    | next s' m =>
      rw [e] at h; try dsimp only at h
      cases e2 : runPass f s' with
      | moment => rw [e2] at h; simp [Out.add] at h
      | halt => exact halts_of_steps (pstep_next s s' m e) (runPass_halt f s' e2)
      | stuck => rw [e2] at h; simp [Out.add] at h
    | done => rw [e] at h; try dsimp only at h; cases h
    | halt => exact pstep_halt s e

/-- One sub-round from the moment `gcfg bs l us`. -/
def sub (fuel : Nat) (bs : List Nat) (l : Nat) (us : List Nat) : Out :=
  match startPS bs l us with
  | some (s, n) => (runPass fuel s).add n
  | none => .stuck

theorem sub_moment (fuel : Nat) (bs : List Nat) (l : Nat) (us : List Nat) (bs' : List Nat) (l' : Nat)
    (us' : List Nat) (n : Nat) (h : sub fuel bs l us = .moment bs' l' us' n) :
    steps n (gcfg bs l us) = some (gcfg bs' l' us') := by
  unfold sub at h
  cases e : startPS bs l us with
  | none => rw [e] at h; try dsimp only at h; cases h
  | some p =>
    obtain ⟨s, m⟩ := p
    rw [e] at h; try dsimp only at h
    cases e2 : runPass fuel s with
    | moment bs'' l'' us'' n' =>
      rw [e2] at h; try dsimp only at h
      simp only [Out.add, Out.moment.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact steps_seq trans (startPS_sound bs l us s m e) (runPass_moment fuel s _ _ _ _ e2)
    | halt => rw [e2] at h; simp [Out.add] at h
    | stuck => rw [e2] at h; simp [Out.add] at h

theorem sub_halt (fuel : Nat) (bs : List Nat) (l : Nat) (us : List Nat) (h : sub fuel bs l us = .halt) :
    Halts trans (gcfg bs l us) := by
  unfold sub at h
  cases e : startPS bs l us with
  | none => rw [e] at h; try dsimp only at h; cases h
  | some p =>
    obtain ⟨s, m⟩ := p
    rw [e] at h; try dsimp only at h
    cases e2 : runPass fuel s with
    | moment => rw [e2] at h; simp [Out.add] at h
    | halt => exact halts_of_steps (startPS_sound bs l us s m e) (runPass_halt fuel s e2)
    | stuck => rw [e2] at h; simp [Out.add] at h

/-! ## Many sub-rounds -/

/-- `N` sub-rounds, each with at most `fuel` moves of the right sweep. -/
def subs (fuel : Nat) : Nat → List Nat → Nat → List Nat → Out
  | 0, bs, l, us => .moment bs l us 0
  | N + 1, bs, l, us =>
    match sub fuel bs l us with
    | .moment bs' l' us' n => (subs fuel N bs' l' us').add n
    | o => o

theorem subs_moment (fuel : Nat) : ∀ (N : Nat) (bs : List Nat) (l : Nat) (us : List Nat) (bs' : List Nat)
    (l' : Nat) (us' : List Nat) (n : Nat), subs fuel N bs l us = .moment bs' l' us' n →
    steps n (gcfg bs l us) = some (gcfg bs' l' us')
  | 0, bs, l, us, bs', l', us', n, h => by
    simp only [subs, Out.moment.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  | N + 1, bs, l, us, bs', l', us', n, h => by
    simp only [subs] at h
    cases e : sub fuel bs l us with
    | moment b1 l1 u1 n1 =>
      rw [e] at h; try dsimp only at h
      cases e2 : subs fuel N b1 l1 u1 with
      | moment b2 l2 u2 n2 =>
        rw [e2] at h; try dsimp only at h
        simp only [Out.add, Out.moment.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact steps_seq trans (sub_moment fuel bs l us _ _ _ _ e) (subs_moment fuel N _ _ _ _ _ _ _ e2)
      | halt => rw [e2] at h; simp [Out.add] at h
      | stuck => rw [e2] at h; simp [Out.add] at h
    | halt => rw [e] at h; try dsimp only at h; cases h
    | stuck => rw [e] at h; try dsimp only at h; cases h

theorem subs_halt (fuel : Nat) : ∀ (N : Nat) (bs : List Nat) (l : Nat) (us : List Nat),
    subs fuel N bs l us = .halt → Halts trans (gcfg bs l us)
  | 0, _, _, _, h => by simp [subs] at h
  | N + 1, bs, l, us, h => by
    simp only [subs] at h
    cases e : sub fuel bs l us with
    | moment b1 l1 u1 n1 =>
      rw [e] at h; try dsimp only at h
      cases e2 : subs fuel N b1 l1 u1 with
      | moment => rw [e2] at h; simp [Out.add] at h
      | halt => exact halts_of_steps (sub_moment fuel bs l us _ _ _ _ e) (subs_halt fuel N _ _ _ e2)
      | stuck => rw [e2] at h; simp [Out.add] at h
    | halt => exact sub_halt fuel bs l us e
    | stuck => rw [e] at h; try dsimp only at h; cases h

/-! ## The configurations of `Collapse.lean` -/

/-- The blocks of `enc q D`: the digits as blocks `3 d + 2`, then the first block `3 q`. -/
def encBlocks (q : Nat) (D : List Nat) : List Nat := D.map (fun d => 3 * d + 2) ++ [3 * q]

theorem digs_blks (q : Nat) : ∀ D : List Nat, digs D (base q) = blks (encBlocks q D)
  | [] => by
    simp only [digs, encBlocks, List.map_nil, List.nil_append, blks, base]
    rw [cons_false_blank, ones_three]
  | d :: ds => by
    simp only [digs, encBlocks, List.map_cons, List.cons_append, blks]
    rw [show 3 * d + 2 = 2 + 3 * d by omega, ones_add, ones_three, digs_blks q ds]
    rfl

theorem enc_gcfg (q : Nat) (D : List Nat) (l : Nat) (us : List Nat) :
    enc q D l us = gcfg (encBlocks q D) l us := by
  simp only [enc, gcfg, digs_blks]

end H4320
