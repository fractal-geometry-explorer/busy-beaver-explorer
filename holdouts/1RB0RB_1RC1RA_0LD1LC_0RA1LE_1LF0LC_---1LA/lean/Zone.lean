import Bits

/-!
# 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA: the zone orbit, an exact reduction that drops the block of words

A state `.rt n Z` of the **zone orbit** stands for the turn configuration `RT (blkFrom 1 n ++ Z)`: the reversed
word is the block of words `blk (n + 1)` (`Xor.lean`; on the tape the `111110` words at the right end) followed by
the rest of the word `Z`, which holds the leftmost zone and everything else.  Only the number `n` is kept for the
block.  A state `.raw c` is a configuration on lists, as in `Sweep.lean`.  One step (`cstep`):

* with a `00` in the word, the sweep of `pat n :: Z` (`zone_step`: the block does not matter beyond `n mod 3`), the
  block growing by one letter;
* otherwise (a reset at the left end) the macro machine `mstep` on the whole word, and the block of the result is
  split off again (`cpr`).

`cstep_sound`, `cstep_halt`: each step is a run of the machine.  **`halts_iff_zone`: the machine halts from blank
tape if and only if the zone orbit halts.**  Everything is checked by Lean's kernel.
-/

namespace H25821

open TM hiding run
open XS

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

/-- A state of the zone orbit. -/
inductive CS where
  | rt (n : Nat) (Z : List Bool)
  | raw (c : FCfg St)

def CS.cfg : CS → Config
  | .rt n Z => RT (blkFrom 1 n ++ Z)
  | .raw c => c.toCfg

/-- Back from a state of the macro machine. -/
def ofMS : MS → CS
  | .rt o => .rt (cpr 1 0 o).1 (cpr 1 0 o).2
  | .raw c => .raw c

theorem ofMS_cfg (s : MS) : (ofMS s).cfg = s.cfg := by
  cases s with
  | rt o =>
    obtain ⟨j, h1, h2⟩ := cpr_sound o 1 0
    show RT (blkFrom 1 (cpr 1 0 o).1 ++ (cpr 1 0 o).2) = RT o
    rw [h1, Nat.zero_add, h2]
  | raw c => rfl

def CS.toMS : CS → MS
  | .rt n Z => .rt (blkFrom 1 n ++ Z)
  | .raw c => .raw c

theorem CS.toMS_cfg (s : CS) : s.toMS.cfg = s.cfg := by cases s <;> rfl

def fallback (s : CS) : Option (Nat × CS) :=
  match mstep s.toMS with
  | .go k s' => some (k, ofMS s')
  | .halt _ => none

/-- One step of the zone orbit: `(steps, state')`, or `none` for a halt. -/
def cstep : CS → Option (Nat × CS)
  | .rt n Z =>
    match swr (pat n :: Z) with
    | .ok d X => some (4 * (n + d) + 14, .rt (n + 1) X)
    | .halt => none
    | .reset => fallback (.rt n Z)
  | .raw c => fallback (.raw c)

theorem word_eq (n : Nat) (Z : List Bool) : true :: (blkFrom 1 n ++ Z) = blk (n + 1) ++ Z := rfl

theorem fallback_sound {s s' : CS} {k : Nat} (h : fallback s = some (k, s')) :
    steps k s.cfg = some s'.cfg ∧ 1 ≤ k := by
  unfold fallback at h
  have hs := mstep_sound s.toMS
  cases hm : mstep s.toMS with
  | halt _ => rw [hm] at h; cases h
  | go k0 s0 =>
    rw [hm] at h hs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, mstep_pos hm⟩
    rw [ofMS_cfg, ← CS.toMS_cfg]; exact hs

theorem fallback_halt {s : CS} (h : fallback s = none) : ∃ m c', steps m s.cfg = some c' ∧ step c' = none := by
  unfold fallback at h
  have hs := mstep_sound s.toMS
  cases hm : mstep s.toMS with
  | go _ _ => rw [hm] at h; cases h
  | halt m => rw [hm, CS.toMS_cfg] at hs; exact ⟨m, hs⟩

theorem cstep_sound {s s' : CS} {k : Nat} (h : cstep s = some (k, s')) : steps k s.cfg = some s'.cfg ∧ 1 ≤ k := by
  cases s with
  | raw c => exact fallback_sound h
  | rt n Z =>
    simp only [cstep] at h
    split at h
    · next d X hsw =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 : swr (true :: (blkFrom 1 n ++ Z)) = .ok (d + n) (blkFrom 2 n ++ X) := by
        rw [word_eq, zone_step, hsw]; simp [SW.pre, blkFrom_length]
      have hs := mstep_sound (.rt (blkFrom 1 n ++ Z))
      rw [mstep_ok _ _ _ h1] at hs
      refine ⟨?_, by omega⟩
      rw [show 4 * (n + d) + 14 = 4 * (d + n) + 14 by omega]
      exact hs
    · cases h
    · exact fallback_sound h

theorem cstep_halt {s : CS} (h : cstep s = none) : ∃ m c', steps m s.cfg = some c' ∧ step c' = none := by
  cases s with
  | raw c => exact fallback_halt h
  | rt n Z =>
    simp only [cstep] at h
    split at h
    · cases h
    · next hsw =>
      have h1 : swr (true :: (blkFrom 1 n ++ Z)) = .halt := by rw [word_eq, zone_step, hsw]; rfl
      obtain ⟨m, hm⟩ := mstep_halt _ h1
      have hs := mstep_sound (.rt (blkFrom 1 n ++ Z))
      rw [hm] at hs; exact ⟨m, hs⟩
    · exact fallback_halt h

/-! ## The orbit -/

/-- The zone orbit from blank tape, with the step count. -/
def corb : Nat → Option (Nat × CS)
  | 0 => some (3, .rt 0 [])
  | k + 1 =>
    match corb k with
    | none => none
    | some (t, s) =>
      match cstep s with
      | none => none
      | some (k', s') => some (t + k', s')

theorem corb_sound : ∀ (k t : Nat) (s : CS), corb k = some (t, s) → steps t init = some s.cfg ∧ k ≤ t
  | 0, t, s, h => by
    simp only [corb, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨init_RT, by omega⟩
  | k + 1, t, s, h => by
    simp only [corb] at h
    cases hp : corb k with
    | none => rw [hp] at h; cases h
    | some p =>
      obtain ⟨t0, s0⟩ := p
      rw [hp] at h
      simp only at h
      cases hc : cstep s0 with
      | none => rw [hc] at h; cases h
      | some q =>
        obtain ⟨k', s'⟩ := q
        rw [hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ht, hk⟩ := corb_sound k t0 s0 hp
        obtain ⟨hs, hpos⟩ := cstep_sound hc
        exact ⟨steps_seq trans ht hs, by omega⟩

/-- The zone orbit halts at step `k`. -/
def CHaltsAt (k : Nat) : Prop := ∃ t s, corb k = some (t, s) ∧ cstep s = none

theorem corb_some (hN : ∀ k, ¬ CHaltsAt k) : ∀ k, ∃ t s, corb k = some (t, s)
  | 0 => ⟨3, .rt 0 [], rfl⟩
  | k + 1 => by
    obtain ⟨t, s, h⟩ := corb_some hN k
    cases hc : cstep s with
    | none => exact absurd ⟨t, s, h, hc⟩ (hN k)
    | some q =>
      obtain ⟨k', s'⟩ := q
      exact ⟨t + k', s', by simp only [corb, h, hc]⟩

/-- **The reduction.** The machine halts from blank tape iff the zone orbit halts. -/
theorem halts_iff_zone : HaltsFromBlank ↔ ∃ k, CHaltsAt k := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hN
    have hN' : ∀ k, ¬ CHaltsAt k := fun k hk => hN ⟨k, hk⟩
    refine not_halts_of_forall trans (forall_of_unbounded trans (fun m => ∃ c, steps m init = some c) ?_ ?_) hH
    · intro k
      obtain ⟨t, s, h⟩ := corb_some hN' k
      obtain ⟨ht, hk⟩ := corb_sound k t s h
      exact ⟨t, hk, _, ht⟩
    · intro m hm; exact hm
  · rintro ⟨k, t, s, h1, h2⟩
    have ht := (corb_sound k t s h1).1
    obtain ⟨m, c', h3, h4⟩ := cstep_halt h2
    exact ⟨t + m, c', steps_seq trans ht h3, h4⟩

/-! ## A tail-recursive runner for compiled evaluation -/

def crun : Nat → Nat × CS → Option (Nat × CS)
  | 0, p => some p
  | k + 1, (t, s) =>
    match cstep s with
    | none => none
    | some (k', s') => crun k (t + k', s')

theorem corb_none : ∀ (j k : Nat), corb j = none → corb (j + k) = none
  | _, 0, h => h
  | j, k + 1, h => by
    show (match corb (j + k) with
      | none => none
      | some (t, s) => _) = none
    rw [corb_none j k h]

theorem corb_crun : ∀ (k j : Nat) (p : Nat × CS), corb j = some p → corb (j + k) = crun k p
  | 0, _, _, h => h
  | k + 1, j, (t, s), h => by
    have e : corb (j + 1) = (match cstep s with
        | none => none
        | some (k', s') => some (t + k', s')) := by
      show (match corb j with
        | none => none
        | some (t, s) => _) = _
      rw [h]
    rw [show j + (k + 1) = (j + 1) + k by omega]
    show _ = (match cstep s with
      | none => none
      | some (k', s') => crun k (t + k', s'))
    cases hc : cstep s with
    | none => rw [hc] at e; exact corb_none (j + 1) k e
    | some q =>
      obtain ⟨k', s'⟩ := q
      rw [hc] at e
      exact corb_crun k (j + 1) _ e

theorem corb_eq_crun (k : Nat) : corb k = crun k (3, .rt 0 []) := by
  have := corb_crun k 0 (3, .rt 0 []) rfl
  rwa [Nat.zero_add] at this

end H25821
