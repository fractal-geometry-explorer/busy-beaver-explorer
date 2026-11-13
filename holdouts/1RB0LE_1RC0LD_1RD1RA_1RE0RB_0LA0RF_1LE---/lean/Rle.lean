import Reach

/-!
# The sweeps on run-length coded digits

The digit list of the counter is mostly long runs of one digit (a run of digits 1 fills the right part of the tape).
Here the digits are coded as runs `(d, c)` (`c` copies of the digit `d`), listed **from the right end**, so that a
sweep only touches the runs it changes.  `ev` turns the runs back into the digit list.

`nextR` is one sweep on runs, covering the same cases as `next` in `MacroRun.lean` (every proved sweep: a stop at
an even digit, a stop at the first digit, the carries at a leftmost block `1^3` or `1^(6j+9)`, and the sweep from
the other phase of the right end); it answers `none` in the case that is not proved (a carry at a leftmost block of
even length, where the machine starts a nested run).  `nextR_sound`: when `nextR` answers, the machine makes that
sweep, with that many steps.  `runR` iterates it, `runR_sound` chains the proofs.

Everything here is checked by Lean's kernel; only the evaluation of long runs (in `RunLong.lean`) uses
`native_decide`.
-/

namespace H23154

open TM

/-! ## Runs -/

/-- The digits of runs listed from the right end. -/
def ev : List (Nat × Nat) → List Nat
  | [] => []
  | (d, c) :: rs => ev rs ++ List.replicate c d

/-- Add `c` copies of `d` at the right end, merging with the last run. -/
def push (d c : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => if c = 0 then [] else [(d, c)]
  | (d', c') :: rs => if c = 0 then (d', c') :: rs else if d = d' then (d, c + c') :: rs else (d, c) :: (d', c') :: rs

theorem ev_push (d c : Nat) (rs : List (Nat × Nat)) : ev (push d c rs) = ev rs ++ List.replicate c d := by
  cases rs with
  | nil => by_cases h : c = 0 <;> simp [push, ev, h]
  | cons x rs =>
    obtain ⟨d', c'⟩ := x
    by_cases h : c = 0
    · simp [push, h]
    · by_cases h' : d = d'
      · subst h'; simp [push, h, ev, Nat.add_comm c c']
      · simp [push, h, h', ev]

/-- Take the last digit off. -/
def pop1 : List (Nat × Nat) → Option (Nat × List (Nat × Nat))
  | [] => none
  | (_, 0) :: rs => pop1 rs
  | (d, c + 1) :: rs => some (d, if c = 0 then rs else (d, c) :: rs)

theorem pop1_ev : ∀ (rs : List (Nat × Nat)) (d : Nat) (rs' : List (Nat × Nat)), pop1 rs = some (d, rs') →
    ev rs = ev rs' ++ [d]
  | [], _, _, h => by simp [pop1] at h
  | (_, 0) :: rs, d, rs', h => by simp only [pop1] at h; simpa [ev] using pop1_ev rs d rs' h
  | (e, c + 1) :: rs, d, rs', h => by
    simp only [pop1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    by_cases hc : c = 0
    · subst hc; simp [ev]
    · simp [ev, hc, List.replicate_succ']

theorem pop1_none : ∀ (rs : List (Nat × Nat)), pop1 rs = none → ev rs = []
  | [], _ => rfl
  | (_, 0) :: rs, h => by simp only [pop1] at h; simpa [ev] using pop1_none rs h
  | (_, _ + 1) :: _, h => by simp [pop1] at h

/-- Split off the runs of odd digits at the right end: their `k` (digit `2k+1`) with counts, from the right, and
the rest. -/
def splitOdd : List (Nat × Nat) → List (Nat × Nat) × List (Nat × Nat)
  | [] => ([], [])
  | (d, c) :: rs => if d % 2 = 1 then ((d / 2, c) :: (splitOdd rs).1, (splitOdd rs).2) else ([], (d, c) :: rs)

/-- The `k`s of runs listed from the left. -/
def kxl : List (Nat × Nat) → List Nat
  | [] => []
  | (k, c) :: rs => List.replicate c k ++ kxl rs

theorem kxl_append (xs ys : List (Nat × Nat)) : kxl (xs ++ ys) = kxl xs ++ kxl ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => obtain ⟨k, c⟩ := x; simp [kxl, ih]

theorem odds_append (xs ys : List Nat) : odds (xs ++ ys) = odds xs ++ odds ys := by simp [odds]

theorem splitOdd_ev : ∀ rs : List (Nat × Nat), ev rs = ev (splitOdd rs).2 ++ odds (kxl (splitOdd rs).1.reverse)
  | [] => rfl
  | (d, c) :: rs => by
    by_cases h : d % 2 = 1
    · simp only [splitOdd, h, ite_true, List.reverse_cons, kxl_append, odds_append, ev]
      rw [splitOdd_ev rs, List.append_assoc]
      congr 1
      simp [kxl, odds, List.map_replicate]
      congr 1; omega
    · simp [splitOdd, h, kxl, odds]

theorem splitOdd_rest : ∀ rs : List (Nat × Nat), ∀ d c rest, (splitOdd rs).2 = (d, c) :: rest → d % 2 = 0
  | [], d, c, rest, h => by simp [splitOdd] at h
  | (e, f) :: rs, d, c, rest, h => by
    by_cases he : e % 2 = 1
    · simp only [splitOdd, he, ite_true] at h; exact splitOdd_rest rs d c rest h
    · simp only [splitOdd, he] at h; simp at h; omega

/-- Take the first `k` off runs listed from the left. -/
def popK : List (Nat × Nat) → Option (Nat × List (Nat × Nat))
  | [] => none
  | (_, 0) :: rs => popK rs
  | (k, c + 1) :: rs => some (k, (k, c) :: rs)

theorem popK_kxl : ∀ (rs : List (Nat × Nat)) (k : Nat) (rs' : List (Nat × Nat)), popK rs = some (k, rs') →
    kxl rs = k :: kxl rs'
  | [], _, _, h => by simp [popK] at h
  | (_, 0) :: rs, k, rs', h => by simp only [popK] at h; simpa [kxl] using popK_kxl rs k rs' h
  | (e, c + 1) :: rs, k, rs', h => by
    simp only [popK, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h; subst h1 h2; simp [kxl, List.replicate_succ]

theorem popK_none : ∀ (rs : List (Nat × Nat)), popK rs = none → kxl rs = []
  | [], _ => rfl
  | (_, 0) :: rs, h => by simp only [popK] at h; simpa [kxl] using popK_none rs h
  | (_, _ + 1) :: _, h => by simp [popK] at h

/-! ## Writing the digits of a sweep -/

/-- `stepD` without the repeated appends: the digits after `E`. -/
def stepT : Nat → List Nat → List Nat
  | c, [] => [c + 1]
  | c, k :: ks => (c + 1) :: (List.replicate (2 * k) 0 ++ stepT 0 ks)

theorem stepD_eq : ∀ (ks : List Nat) (E : List Nat) (c : Nat), stepD E c ks = E ++ stepT c ks
  | [], E, c => rfl
  | k :: ks, E, c => by
    show stepD (E ++ [c + 1] ++ List.replicate (2 * k) 0) 0 ks = _
    rw [stepD_eq ks]; simp [stepT]

theorem stepT_ones : ∀ (m : Nat) (ks : List Nat), stepT 0 (List.replicate m 0 ++ ks) =
    List.replicate m 1 ++ stepT 0 ks
  | 0, ks => by simp
  | m + 1, ks => by
    rw [List.replicate_succ, List.cons_append, stepT, stepT_ones m ks]
    simp [List.replicate_succ]

/-- The digits `stepT c` writes for `m` copies of `k`, onto runs `acc`; the state `c` becomes 0 after the first. -/
def emitRun (k : Nat) : Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | _, 0, acc => acc
  | c, m + 1, acc => if k = 0 then push 1 m (push (c + 1) 1 acc) else emitRun k 0 m (push 0 (2 * k) (push (c + 1) 1 acc))

theorem emitRun_ev (k : Nat) : ∀ (m c : Nat) (acc : List (Nat × Nat)) (ks : List Nat),
    ev (emitRun k c (m + 1) acc) ++ stepT 0 ks = ev acc ++ stepT c (List.replicate (m + 1) k ++ ks)
  | m, c, acc, ks => by
    by_cases hk : k = 0
    · subst hk
      have e : stepT c (List.replicate (m + 1) 0 ++ ks) = (c + 1) :: (List.replicate m 1 ++ stepT 0 ks) := by
        rw [List.replicate_succ, List.cons_append, stepT]; simp [stepT_ones]
      simp only [emitRun, ite_true, ev_push, e]
      simp
    · induction m generalizing c acc with
      | zero => simp [emitRun, hk, ev_push, stepT]
      | succ m ih =>
        rw [emitRun, if_neg hk, ih]
        simp only [ev_push, List.replicate_succ, List.cons_append, stepT]
        simp

/-- `stepT c` of the `k`s of runs listed from the left, written onto `acc`. -/
def emitT : Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | c, [], acc => push (c + 1) 1 acc
  | c, (_, 0) :: rs, acc => emitT c rs acc
  | c, (k, m + 1) :: rs, acc => emitT 0 rs (emitRun k c (m + 1) acc)

theorem emitT_ev : ∀ (c : Nat) (rs acc : List (Nat × Nat)), ev (emitT c rs acc) = ev acc ++ stepT c (kxl rs)
  | c, [], acc => by simp [emitT, ev_push, kxl, stepT]
  | c, (_, 0) :: rs, acc => by simp only [emitT, kxl, List.replicate_zero, List.nil_append]; exact emitT_ev c rs acc
  | c, (k, m + 1) :: rs, acc => by
    rw [emitT, emitT_ev 0 rs, emitRun_ev k m c acc (kxl rs)]
    rfl

/-- The cost of the odd digits of runs listed from the left. -/
def costR : List (Nat × Nat) → Nat
  | [] => 0
  | (k, c) :: rs => c * (20 * k + 16) + costR rs

theorem costR_eq : ∀ rs : List (Nat × Nat), lcost (kxl rs) + rcost (kxl rs) = costR rs := by
  intro rs
  rw [cost_sum]
  induction rs with
  | nil => rfl
  | cons x rs ih =>
    obtain ⟨k, c⟩ := x
    simp only [kxl, List.map_append, List.sum_append, List.map_replicate, List.sum_replicate_nat, costR, ih]

theorem lcost_cons (k : Nat) (ks : List Nat) : lcost (k :: ks) = 12 * k + 10 + lcost ks := rfl

/-! ## One sweep on runs -/

/-- A macro state on runs: leftmost block `1^r`, digits as runs from the right end, `true` in the other phase. -/
structure MR where
  r : Nat
  rs : List (Nat × Nat)
  ph : Bool
  deriving DecidableEq, Repr

def MR.cfg (s : MR) : Config := if s.ph then Q (raw s.r) (ev s.rs) else P (raw s.r) (ev s.rs)

/-- One sweep on runs, with its number of steps. -/
def nextR (s : MR) : Option (MR × Nat) :=
  if s.ph then
    match pop1 s.rs with
    | some (1, rest) => some (⟨s.r, push 0 1 (push 2 1 rest), false⟩, 25)
    | _ => none
  else
    let lr := (splitOdd s.rs).1.reverse
    match pop1 (splitOdd s.rs).2 with
    | none =>
      if s.r = 3 then
        match popK lr with
        | some (k, lr') => some (⟨3, emitT 0 lr' (push 0 (2 * k + 2) []), false⟩,
            8 + (12 * k + 10 + costR lr') + (8 * k + 37) + 4)
        | none => none
      else if s.r % 6 = 3 ∧ 9 ≤ s.r then
        some (⟨3, emitT 0 lr (push 0 (2 * ((s.r - 9) / 6) + 3) []), false⟩,
          8 + costR lr + (20 * ((s.r - 9) / 6) + 91) + 4)
      else none
    | some (b, rest) =>
      if b % 2 = 0 then
        match pop1 rest with
        | none =>
          if b = 0 then
            match popK lr with
            | some (k, lr') => some (⟨s.r + 6, emitT 0 lr' (push 0 (2 * k) []), false⟩, 21 + costR lr)
            | none => some (⟨s.r + 6, [], false⟩, 21 + costR lr)
          else some (⟨s.r + 3, emitT 0 lr (push 0 (2 * (b / 2 - 1) + 1) []), false⟩,
            21 + 10 * (2 * (b / 2 - 1) + 2) + costR lr)
        | some (a, rest') =>
          if b = 0 then some (⟨s.r, emitT (a + 1) lr rest', false⟩, 21 + costR lr)
          else some (⟨s.r, emitT 0 lr (push 0 (2 * (b / 2 - 1) + 1) (push (a + 1) 1 rest')), false⟩,
            21 + 10 * (2 * (b / 2 - 1) + 2) + costR lr)
      else none

/-- **Soundness**: when `nextR` answers, the machine makes that sweep. -/
theorem nextR_sound (s s' : MR) (n : Nat) (h : nextR s = some (s', n)) : steps n s.cfg = some s'.cfg := by
  obtain ⟨r, rs, ph⟩ := s
  cases ph with
  | true =>
    simp only [nextR, ite_true] at h
    split at h
    · rename_i rest hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h; subst h1 h2
      have e := pop1_ev rs 1 rest hp
      simp only [MR.cfg, ite_true, Bool.false_eq_true, ite_false, e, ev_push]
      have := phase2_sweep (raw r) (ev rest)
      simpa using this
    · cases h
  | false =>
    simp only [nextR, Bool.false_eq_true, ite_false] at h
    have hsplit := splitOdd_ev rs
    generalize hlr : (splitOdd rs).1.reverse = lr at h hsplit
    generalize hrest0 : (splitOdd rs).2 = rest0 at h hsplit
    split at h
    · -- every digit is odd
      rename_i hp
      have e0 := pop1_none rest0 hp
      rw [e0, List.nil_append] at hsplit
      split at h
      · rename_i hr3
        subst hr3
        split at h
        · rename_i k lr' hk
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h; subst h1 h2
          have ek := popK_kxl lr k lr' hk
          rw [ek] at hsplit
          simp only [MR.cfg, Bool.false_eq_true, ite_false, hsplit]
          rw [emitT_ev, ev_push, ← costR_eq]
          have := carry3_sweep k (kxl lr')
          rw [stepD_eq] at this
          simp only [ev, List.nil_append] at this ⊢
          refine steps_congr trans ?_ this
          simp [lcost_cons]; omega
        · cases h
      · split at h
        · rename_i hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h; subst h1 h2
          simp only [MR.cfg, Bool.false_eq_true, ite_false, hsplit]
          rw [emitT_ev, ev_push, ← costR_eq]
          have := carry9_sweep ((r - 9) / 6) (kxl lr)
          rw [stepD_eq, show 6 * ((r - 9) / 6) + 9 = r by omega] at this
          simp only [ev, List.nil_append] at this ⊢
          refine steps_congr trans ?_ this
          omega
        · cases h
    · rename_i b rest hp
      have e1 := pop1_ev rest0 b rest hp
      split at h
      · rename_i hb
        split at h
        · -- the stop digit is the first digit
          rename_i hp2
          have e2 := pop1_none rest hp2
          rw [e1, e2, List.nil_append] at hsplit
          split at h
          · rename_i hb0
            subst hb0
            split at h
            · rename_i k lr' hk
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨h1, h2⟩ := h; subst h1 h2
              have ek := popK_kxl lr k lr' hk
              simp only [MR.cfg, Bool.false_eq_true, ite_false, hsplit]
              rw [emitT_ev, ev_push, ← costR_eq, ek]
              have := raw_zero r (k :: kxl lr')
              simp only [rawD, stepD_eq] at this
              simp [ev] at this ⊢
              exact steps_congr trans (by omega) this
            · rename_i hk
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨h1, h2⟩ := h; subst h1 h2
              have ek := popK_none lr hk
              simp only [MR.cfg, Bool.false_eq_true, ite_false, hsplit]
              rw [← costR_eq, ek]
              have := raw_zero r []
              simp [ev, rawD] at this ⊢
              exact steps_congr trans (by omega) this
          · rename_i hb0
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h; subst h1 h2
            simp only [MR.cfg, Bool.false_eq_true, ite_false, hsplit]
            rw [emitT_ev, ev_push, ← costR_eq]
            have := raw_even r (b / 2 - 1) (kxl lr)
            rw [stepD_eq, show 2 * (b / 2 - 1) + 2 = b by omega] at this
            simp [ev] at this ⊢
            exact steps_congr trans (by omega) this
        · rename_i a rest' hp2
          have e2 := pop1_ev rest a rest' hp2
          rw [e1, e2] at hsplit
          split at h
          · rename_i hb0
            subst hb0
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h; subst h1 h2
            simp only [MR.cfg, Bool.false_eq_true, ite_false, hsplit]
            rw [emitT_ev, ← costR_eq]
            have := sweep_zero (raw r) (ev rest') a (kxl lr)
            rw [stepD_eq] at this
            simp at this ⊢
            exact steps_congr trans (by omega) this
          · rename_i hb0
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h; subst h1 h2
            simp only [MR.cfg, Bool.false_eq_true, ite_false, hsplit]
            rw [emitT_ev, ev_push, ev_push, ← costR_eq]
            have := sweep_even (raw r) (ev rest') a (b / 2 - 1) (kxl lr)
            rw [stepD_eq, show 2 * (b / 2 - 1) + 2 = b by omega] at this
            simp at this ⊢
            exact steps_congr trans (by omega) this
      · cases h

/-- `k` sweeps on runs, adding up the steps. -/
def runR : Nat → MR → Nat → Option (MR × Nat)
  | 0, s, t => some (s, t)
  | k + 1, s, t =>
    match nextR s with
    | none => none
    | some (s', n) => runR k s' (t + n)

theorem runR_sound : ∀ (k : Nat) (s : MR) (t : Nat) (s' : MR) (t' : Nat), runR k s t = some (s', t') →
    steps t init = some s.cfg → steps t' init = some s'.cfg
  | 0, s, t, s', t', h, h0 => by simp [runR] at h; obtain ⟨h1, h2⟩ := h; subst h1 h2; exact h0
  | k + 1, s, t, s', t', h, h0 => by
    simp only [runR] at h
    split at h
    · cases h
    · rename_i s1 n hn
      exact runR_sound k s1 (t + n) s' t' h (steps_seq trans h0 (nextR_sound s s1 n hn))

end H23154
