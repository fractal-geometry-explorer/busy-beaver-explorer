import Bits

/-!
# 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA: the zone orbit, an exact reduction that drops the block of words

A state `(n, Z, rest)` of the **zone orbit** stands for the turn configuration `RT (blkFrom 1 n ++ Z) rest`: the
reversed word is the block of words `blk (n + 1)` (`Xor.lean`; on the tape the `111110` words at the right end)
followed by the rest of the word `Z`, which holds the leftmost zone and everything else.  Only the number `n` is
kept for the block.  One step (`cstep`):

* at the right end (`rest = []`) with a `00` in the word, the sweep of `pat n :: Z` (`zone_step`: the block does not
  matter beyond `n mod 3`), the block growing by one letter;
* otherwise (a reset at the left end, or a turn inside the word) the pass machine `mstep` on the whole word, and
  the block of the result is split off again (`cpr`).

`cstep_sound`, `cstep_halt`: each step is a run of the machine.  **`halts_iff_zone`: the machine halts from blank
tape if and only if the zone orbit halts.**  Everything is checked by Lean's kernel.
-/

namespace H73071

open TM XS

/-- Split off the longest block prefix (phase `s`), counting its letters on top of `k`.  Tail-recursive. -/
def cpr : Nat → Nat → List Bool → Nat × List Bool
  | s, k, a :: t => if a = pat s then cpr (s + 1) (k + 1) t else (k, a :: t)
  | _, k, [] => (k, [])

theorem cpr_sound : ∀ (l : List Bool) (s k : Nat), ∃ j, (cpr s k l).1 = k + j ∧ blkFrom s j ++ (cpr s k l).2 = l
  | [], s, k => ⟨0, rfl, rfl⟩
  | a :: t, s, k => by
    unfold cpr
    split
    · next h =>
      obtain ⟨j, h1, h2⟩ := cpr_sound t (s + 1) (k + 1)
      refine ⟨j + 1, by rw [h1]; omega, ?_⟩
      show pat s :: (blkFrom (s + 1) j ++ _) = _
      rw [h2, h]
    · exact ⟨0, rfl, rfl⟩

/-- One step of the zone orbit: `(steps, n', Z', rest')`, or `none` for a halt. -/
def cstep (n : Nat) (Z rest : List Bool) : Option (Nat × Nat × List Bool × List Bool) :=
  match rest, swr (pat n :: Z) with
  | [], .ok d X => some (4 * (n + d) + 12, n + 1, X, [])
  | [], .halt => none
  | _, _ =>
    match mstep (blkFrom 1 n ++ Z) rest with
    | .go k o r => some (k, (cpr 1 0 o).1, (cpr 1 0 o).2, r)
    | .halt _ => none

theorem word_eq (n : Nat) (Z : List Bool) : true :: (blkFrom 1 n ++ Z) = blk (n + 1) ++ Z := rfl

theorem fallback_sound {n : Nat} {Z rest : List Bool} {k n' : Nat} {Z' r' : List Bool}
    (h : (match mstep (blkFrom 1 n ++ Z) rest with
      | .go k o r => some (k, (cpr 1 0 o).1, (cpr 1 0 o).2, r)
      | .halt _ => none) = some (k, n', Z', r')) :
    steps k (RT (blkFrom 1 n ++ Z) rest) = some (RT (blkFrom 1 n' ++ Z') r') ∧ 1 ≤ k := by
  have hs := mstep_sound (blkFrom 1 n ++ Z) rest
  cases hm : mstep (blkFrom 1 n ++ Z) rest with
  | halt _ => rw [hm] at h; cases h
  | go k0 o r =>
    rw [hm] at h hs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨j, h1, h2⟩ := cpr_sound o 1 0
    refine ⟨?_, mstep_pos hm⟩
    rw [h1, Nat.zero_add, h2]; exact hs

theorem fallback_halt {n : Nat} {Z rest : List Bool}
    (h : (match mstep (blkFrom 1 n ++ Z) rest with
      | .go k o r => some (k, (cpr 1 0 o).1, (cpr 1 0 o).2, r)
      | .halt _ => none) = none) :
    ∃ m c', steps m (RT (blkFrom 1 n ++ Z) rest) = some c' ∧ step c' = none := by
  have hs := mstep_sound (blkFrom 1 n ++ Z) rest
  cases hm : mstep (blkFrom 1 n ++ Z) rest with
  | go _ _ _ => rw [hm] at h; cases h
  | halt m => rw [hm] at hs; exact ⟨m, hs⟩

theorem cstep_sound {n : Nat} {Z rest : List Bool} {k n' : Nat} {Z' r' : List Bool}
    (h : cstep n Z rest = some (k, n', Z', r')) :
    steps k (RT (blkFrom 1 n ++ Z) rest) = some (RT (blkFrom 1 n' ++ Z') r') ∧ 1 ≤ k := by
  unfold cstep at h
  split at h
  · next d X hsw =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    have h1 : swr (true :: (blkFrom 1 n ++ Z)) = .ok (d + n) (blkFrom 2 n ++ X) := by
      rw [word_eq, zone_step, hsw]; simp [SW.pre, blkFrom_length]
    have hs := mstep_sound (blkFrom 1 n ++ Z) []
    rw [mstep_ok _ _ _ h1] at hs
    refine ⟨?_, by omega⟩
    rw [show 4 * (n + d) + 12 = 4 * (d + n) + 12 by omega]
    exact hs
  · cases h
  · exact fallback_sound h

theorem cstep_halt {n : Nat} {Z rest : List Bool} (h : cstep n Z rest = none) :
    ∃ m c', steps m (RT (blkFrom 1 n ++ Z) rest) = some c' ∧ step c' = none := by
  unfold cstep at h
  split at h
  · cases h
  · next hsw =>
    have h1 : swr (true :: (blkFrom 1 n ++ Z)) = .halt := by rw [word_eq, zone_step, hsw]; rfl
    obtain ⟨m, hm⟩ := mstep_halt _ h1
    have hs := mstep_sound (blkFrom 1 n ++ Z) []
    rw [hm] at hs; exact ⟨m, hs⟩
  · exact fallback_halt h

/-! ## The orbit -/

/-- The zone orbit from blank tape, with the step count: `(t, n, Z, rest)`. -/
def corb : Nat → Option (Nat × Nat × List Bool × List Bool)
  | 0 => some (2, 0, [], [])
  | k + 1 =>
    match corb k with
    | none => none
    | some (t, n, Z, r) =>
      match cstep n Z r with
      | none => none
      | some (k', n', Z', r') => some (t + k', n', Z', r')

theorem corb_sound : ∀ (k t n : Nat) (Z r : List Bool), corb k = some (t, n, Z, r) →
    steps t init = some (RT (blkFrom 1 n ++ Z) r) ∧ k ≤ t
  | 0, t, n, Z, r, h => by
    simp only [corb, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨init_RT, by omega⟩
  | k + 1, t, n, Z, r, h => by
    simp only [corb] at h
    cases hp : corb k with
    | none => rw [hp] at h; cases h
    | some p =>
      obtain ⟨t0, n0, Z0, r0⟩ := p
      rw [hp] at h
      simp only at h
      cases hc : cstep n0 Z0 r0 with
      | none => rw [hc] at h; cases h
      | some q =>
        obtain ⟨k', n', Z', r'⟩ := q
        rw [hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        obtain ⟨ht, hk⟩ := corb_sound k t0 n0 Z0 r0 hp
        obtain ⟨hs, hpos⟩ := cstep_sound hc
        exact ⟨steps_seq trans ht hs, by omega⟩

/-- The zone orbit halts at step `k`. -/
def CHaltsAt (k : Nat) : Prop := ∃ t n Z r, corb k = some (t, n, Z, r) ∧ cstep n Z r = none

theorem corb_some (hN : ∀ k, ¬ CHaltsAt k) : ∀ k, ∃ t n Z r, corb k = some (t, n, Z, r)
  | 0 => ⟨2, 0, [], [], rfl⟩
  | k + 1 => by
    obtain ⟨t, n, Z, r, h⟩ := corb_some hN k
    cases hc : cstep n Z r with
    | none => exact absurd ⟨t, n, Z, r, h, hc⟩ (hN k)
    | some q =>
      obtain ⟨k', n', Z', r'⟩ := q
      exact ⟨t + k', n', Z', r', by simp only [corb, h, hc]⟩

/-- **The reduction.** The machine halts from blank tape iff the zone orbit halts. -/
theorem halts_iff_zone : HaltsFromBlank ↔ ∃ k, CHaltsAt k := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hN
    have hN' : ∀ k, ¬ CHaltsAt k := fun k hk => hN ⟨k, hk⟩
    refine not_halts_of_forall trans (forall_of_unbounded trans (fun m => ∃ c, steps m init = some c) ?_ ?_) hH
    · intro k
      obtain ⟨t, n, Z, r, h⟩ := corb_some hN' k
      obtain ⟨ht, hk⟩ := corb_sound k t n Z r h
      exact ⟨t, hk, _, ht⟩
    · intro m hm; exact hm
  · rintro ⟨k, t, n, Z, r, h1, h2⟩
    have ht := (corb_sound k t n Z r h1).1
    obtain ⟨m, c', h3, h4⟩ := cstep_halt h2
    exact ⟨t + m, c', steps_seq trans ht h3, h4⟩

/-! ## A tail-recursive runner for compiled evaluation -/

def crun : Nat → Nat × Nat × List Bool × List Bool → Option (Nat × Nat × List Bool × List Bool)
  | 0, s => some s
  | k + 1, (t, n, Z, r) =>
    match cstep n Z r with
    | none => none
    | some (k', n', Z', r') => crun k (t + k', n', Z', r')

theorem corb_none : ∀ (j k : Nat), corb j = none → corb (j + k) = none
  | _, 0, h => h
  | j, k + 1, h => by
    show (match corb (j + k) with
      | none => none
      | some (t, n, Z, r) => _) = none
    rw [corb_none j k h]

theorem corb_crun : ∀ (k j : Nat) (s : Nat × Nat × List Bool × List Bool), corb j = some s →
    corb (j + k) = crun k s
  | 0, _, _, h => h
  | k + 1, j, (t, n, Z, r), h => by
    have e : corb (j + 1) = (match cstep n Z r with
        | none => none
        | some (k', n', Z', r') => some (t + k', n', Z', r')) := by
      show (match corb j with
        | none => none
        | some (t, n, Z, r) => _) = _
      rw [h]
    rw [show j + (k + 1) = (j + 1) + k by omega]
    show _ = (match cstep n Z r with
      | none => none
      | some (k', n', Z', r') => crun k (t + k', n', Z', r'))
    cases hc : cstep n Z r with
    | none => rw [hc] at e; exact corb_none (j + 1) k e
    | some q =>
      obtain ⟨k', n', Z', r'⟩ := q
      rw [hc] at e
      exact corb_crun k (j + 1) _ e

theorem corb_eq_crun (k : Nat) : corb k = crun k (2, 0, [], []) := by
  have := corb_crun k 0 (2, 0, [], []) rfl
  rwa [Nat.zero_add] at this

end H73071
