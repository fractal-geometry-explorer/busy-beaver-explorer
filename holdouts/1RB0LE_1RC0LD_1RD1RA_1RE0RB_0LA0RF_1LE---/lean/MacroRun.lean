import Reach

/-!
# The sweeps as a program, run from the first sweep configuration

`next` computes one sweep on the digit level (the leftmost block `1^r`, the digits, the phase of the right end),
covering every case proved in `Sweep.lean` and `Carry.lean`; it answers `none` only for a carry that reaches a
leftmost block whose length is not 3 or `6j+9` (in the run: an even length, where the machine starts a nested run
of inner sweeps that is not formalized).  `next_sound`: whenever `next` answers, the machine really goes from the
one configuration to the other in the stated number of steps.  `run` iterates it.

The common sweeps use `stepT`, a linear-time form of `stepD` (`stepD_eq`), so that a sweep costs time linear in the
number of digits.  Evaluated by compiled code (`native_decide`), `run` goes 19,971 sweeps from the configuration
reached after 5,512 steps (sweep 29, `reach_D0`), without a gap, up to step 1,595,848,115 (sweep 20,000): no halt in
that many steps (`no_halt_1595848115`), and the sweep model of the README is exact all along.
-/

namespace H23154

open TM

/-- A macro state: leftmost block `1^r`, digits, `true` when the right end is in its other phase. -/
structure MS where
  r : Nat
  ds : List Nat
  ph : Bool
  deriving DecidableEq, Repr

def MS.cfg (s : MS) : Config := if s.ph then Q (raw s.r) s.ds else P (raw s.r) s.ds

/-- Scan the digits from the right (given reversed): `inl ks` if all are odd, else `inr (prefix, stop digit, ks)`. -/
def scan : List Nat → List Nat → Sum (List Nat) (List Nat × Nat × List Nat)
  | [], acc => .inl acc
  | d :: rest, acc => if d % 2 = 1 then scan rest (d / 2 :: acc) else .inr (rest.reverse, d, acc)

theorem odds_cons (k : Nat) (ks : List Nat) : odds (k :: ks) = (2 * k + 1) :: odds ks := rfl

theorem scan_inl : ∀ (rev acc ks : List Nat), scan rev acc = .inl ks → rev.reverse ++ odds acc = odds ks
  | [], acc, ks, h => by simp [scan] at h; subst h; simp
  | d :: rest, acc, ks, h => by
    simp only [scan] at h
    split at h
    · have := scan_inl rest (d / 2 :: acc) ks h
      rw [← this, odds_cons, show 2 * (d / 2) + 1 = d by omega]; simp
    · cases h

theorem scan_inr : ∀ (rev acc pre ks : List Nat) (b : Nat), scan rev acc = .inr (pre, b, ks) →
    rev.reverse ++ odds acc = pre ++ [b] ++ odds ks ∧ b % 2 = 0
  | [], acc, pre, ks, b, h => by simp [scan] at h
  | d :: rest, acc, pre, ks, b, h => by
    simp only [scan] at h
    split at h
    · have := scan_inr rest (d / 2 :: acc) pre ks b h
      rw [← this.1, odds_cons, show 2 * (d / 2) + 1 = d by omega]; exact ⟨by simp, this.2⟩
    · simp at h; obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3
      exact ⟨by simp, by omega⟩

/-- `stepD` without the repeated appends (linear time): the digits after `E`. -/
def stepT : Nat → List Nat → List Nat
  | c, [] => [c + 1]
  | c, k :: ks => (c + 1) :: (List.replicate (2 * k) 0 ++ stepT 0 ks)

theorem stepD_eq : ∀ (ks : List Nat) (E : List Nat) (c : Nat), stepD E c ks = E ++ stepT c ks
  | [], E, c => rfl
  | k :: ks, E, c => by
    show stepD (E ++ [c + 1] ++ List.replicate (2 * k) 0) 0 ks = _
    rw [stepD_eq ks]; simp [stepT]

/-- One sweep on the digit level, with its number of steps. -/
def next (s : MS) : Option (MS × Nat) :=
  if s.ph then
    match s.ds.reverse with
    | 1 :: rest => some (⟨s.r, rest.reverse ++ [2, 0], false⟩, 25)
    | _ => none
  else
    match scan s.ds.reverse [] with
    | .inl ks =>
      if s.r = 3 then
        match ks with
        | k :: ks' => some (⟨3, stepD (List.replicate (2 * k + 2) 0) 0 ks', false⟩,
            8 + lcost (k :: ks') + (8 * k + 37) + rcost ks' + 4)
        | [] => none
      else if s.r % 6 = 3 ∧ 9 ≤ s.r then
        some (⟨3, stepD (List.replicate (2 * ((s.r - 9) / 6) + 3) 0) 0 ks, false⟩,
          8 + lcost ks + (20 * ((s.r - 9) / 6) + 91) + rcost ks + 4)
      else none
    | .inr (pre, b, ks) =>
      match pre.reverse with
      | [] =>
        if b = 0 then some (⟨s.r + 6, rawD ks, false⟩, 21 + lcost ks + rcost ks)
        else some (⟨s.r + 3, stepD (List.replicate (2 * (b / 2 - 1) + 1) 0) 0 ks, false⟩,
          21 + 10 * (2 * (b / 2 - 1) + 2) + lcost ks + rcost ks)
      | a :: yr =>
        if b = 0 then some (⟨s.r, (yr.reverse ++ stepT (a + 1) ks), false⟩, 21 + lcost ks + rcost ks)
        else some (⟨s.r, (yr.reverse ++ [a + 1] ++ List.replicate (2 * (b / 2 - 1) + 1) 0 ++ stepT 0 ks), false⟩,
          21 + 10 * (2 * (b / 2 - 1) + 2) + lcost ks + rcost ks)

theorem rev_split {l : List Nat} {a : Nat} {yr : List Nat} (h : l.reverse = a :: yr) : l = yr.reverse ++ [a] := by
  rw [← List.reverse_reverse l, h]; simp

/-- **Soundness**: when `next` answers, the machine makes that sweep. -/
theorem next_sound (s s' : MS) (n : Nat) (h : next s = some (s', n)) : steps n s.cfg = some s'.cfg := by
  obtain ⟨r, ds, ph⟩ := s
  cases ph with
  | true =>
    simp only [next, ite_true] at h
    split at h
    · rename_i rest hr
      simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2
      have e : ds = rest.reverse ++ [1] := rev_split hr
      subst e
      exact phase2_sweep (raw r) rest.reverse
    · cases h
  | false =>
    simp only [next, Bool.false_eq_true, ite_false] at h
    split at h
    · rename_i ks hs
      have hd := scan_inl ds.reverse [] ks hs
      simp [odds] at hd
      split at h
      · rename_i hr3
        subst hr3
        split at h
        · rename_i k ks'
          simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2
          show steps _ (P (raw 3) ds) = some (P (raw 3) _)
          rw [show ds = odds (k :: ks') by simpa [odds] using hd]
          exact carry3_sweep k ks'
        · cases h
      · split at h
        · rename_i hr
          simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2
          show steps _ (P (raw r) ds) = some (P (raw 3) _)
          rw [show ds = odds ks by simpa [odds] using hd,
            show r = 6 * ((r - 9) / 6) + 9 by omega]
          rw [show (6 * ((r - 9) / 6) + 9 - 9) / 6 = (r - 9) / 6 by omega]
          exact carry9_sweep ((r - 9) / 6) ks
        · cases h
    · rename_i pre b ks hs
      have hd := scan_inr ds.reverse [] pre ks b hs
      simp [odds] at hd
      obtain ⟨hd, hb⟩ := hd
      split at h
      · rename_i hp
        have hp' : pre = [] := by simpa using hp
        subst hp'
        split at h
        · rename_i hb0
          subst hb0
          simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2
          show steps _ (P (raw r) ds) = some (P (raw (r + 6)) _)
          rw [show ds = [0] ++ odds ks by simpa [odds] using hd]
          exact raw_zero r ks
        · rename_i hb0
          simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2
          show steps _ (P (raw r) ds) = some (P (raw (r + 3)) _)
          rw [show ds = [2 * (b / 2 - 1) + 2] ++ odds ks by
            rw [show 2 * (b / 2 - 1) + 2 = b by omega]; simpa [odds] using hd]
          exact raw_even r (b / 2 - 1) ks
      · rename_i a yr hp
        have hp' := rev_split hp
        subst hp'
        split at h
        · rename_i hb0
          subst hb0
          simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2
          show steps _ (P (raw r) ds) = some (P (raw r) _)
          rw [show ds = yr.reverse ++ [a, 0] ++ odds ks by simpa [odds] using hd]
          rw [← stepD_eq]
          exact sweep_zero (raw r) yr.reverse a ks
        · rename_i hb0
          simp at h; obtain ⟨h1, h2⟩ := h; subst h1 h2
          show steps _ (P (raw r) ds) = some (P (raw r) _)
          rw [show ds = yr.reverse ++ [a, 2 * (b / 2 - 1) + 2] ++ odds ks by
            rw [show 2 * (b / 2 - 1) + 2 = b by omega]; simpa [odds] using hd]
          have := sweep_even (raw r) yr.reverse a (b / 2 - 1) ks
          rw [stepD_eq] at this
          simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
          exact this

/-- `k` sweeps, adding up the steps. -/
def run : Nat → MS → Nat → Option (MS × Nat)
  | 0, s, t => some (s, t)
  | k + 1, s, t =>
    match next s with
    | none => none
    | some (s', n) => run k s' (t + n)

theorem run_sound : ∀ (k : Nat) (s : MS) (t : Nat) (s' : MS) (t' : Nat), run k s t = some (s', t') →
    steps t init = some s.cfg → steps t' init = some s'.cfg
  | 0, s, t, s', t', h, h0 => by simp [run] at h; obtain ⟨h1, h2⟩ := h; subst h1 h2; exact h0
  | k + 1, s, t, s', t', h, h0 => by
    simp only [run] at h
    split at h
    · cases h
    · rename_i s1 n hn
      exact run_sound k s1 (t + n) s' t' h (steps_seq trans h0 (next_sound s s1 n hn))

/-- The first sweep configuration, as a macro state. -/
def s0 : MS := ⟨3, D0, true⟩

theorem run_value : ((run 19971 s0 5512).map (·.2)) = some 1595848115 := by native_decide

/-- **No halt in the first 1,595,848,115 steps**, by 19,971 proved sweeps. -/
theorem no_halt_1595848115 : ∃ c, steps 1595848115 init = some c := by
  have h := run_value
  cases e : run 19971 s0 5512 with
  | none => rw [e] at h; cases h
  | some x =>
    rw [e] at h
    simp at h
    obtain ⟨s', t'⟩ := x
    simp at h
    subst h
    exact ⟨_, run_sound 19971 s0 5512 s' _ e reach_D0⟩

end H23154
