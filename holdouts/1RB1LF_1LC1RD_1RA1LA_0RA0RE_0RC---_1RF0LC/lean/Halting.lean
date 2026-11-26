import Reduction

/-!
# Halting configurations of the wall-stack form

The counter-stack model (`Stack.lean`, `Model.lean`) has no halting rule: it only says what the machine does while
no count fails.  Here: when a count does fail, the machine can halt.

Write `K(k) = b^k 1^3 b 1` (`b = 110`), an open counter.

* `halting_wall`: from `1 K(24) K(7) K(1) A> 0 b^N 1` the machine halts, for **every odd `N ≥ 252`**.  (An odd
  signal reaches all three counters; the bottom one grows from 24 to 36 and takes the 12 from the middle one, which
  would become `10 - 12 = -2`; the top one would become `1 - 3 = -2` too.)  The bound 252 is the working room of the
  zone simulator; direct runs halt for every odd `N` from 21 to 139.
* `stepMap_halting_wall`: in terms of `Reduction.lean`, the step map answers `halt` on this wall for those `N`:
  it is a halting step of the map whose orbit `halts_iff` is about.
* `halting_small`: `1 K(18) K(5) A> 0 b^2 1` halts after 3,263 steps (a block too small for its wall).

None of these configurations is known to be reachable from blank tape.  What they show: the hypothesis of
`not_halts_of_model` (no count fails) cannot be dropped, and a set of walls that contains them cannot be closed
under the machine without a halt.

Observed, not proved here (`py/failhalt.py`): among the walls `1 K(a) K(c) K(e)` with all three counts odd-passing,
`a < 150`, `c < 60`, `e < 16`, on which the model fails (31,016 walls), the step with odd `N` halts exactly when
both new upper counts would be `-2` (14 walls: `a = 18 i + 24` or `18 i + 25`, `c = 6 i + 7`, `e = 2 i + 1`).
-/

namespace H3292

open TM TM.Zone

/-- What part 1 of a step leaves: the junction `(x, y, L)`, computed from the wall alone. -/
def jun (W : List Bool) : Option (Nat × Nat × List Bool) :=
  match arun trans rulesR rulesL (fun c => (decodeJ c).isSome) (fuel W.length)
      (ini1 W (W.length + 2) (W.length + 14)) with
  | .next c1 => decodeJ c1
  | _ => none

/-- If part 3 of the step halts in the zone simulator, the step map answers `halt`, for every `N` with room. -/
theorem stepMap_halt {W : List Bool} {N x y : Nat} {L : List Bool}
    (hj : jun W = some (x, y, L)) (hN : W.length + 2 + (W.length + 14) ≤ N)
    (hY : L.length + 14 + (L.length + 14) ≤ y + 3 * ((N - (W.length + 2 + (W.length + 14)) + x) / 2) + 1)
    (hh : arun trans rulesR rulesL (fun c => (decodeS c).isSome) (fuel L.length)
      (ini2 ((N - (W.length + 2 + (W.length + 14)) + x) % 2) L (L.length + 14)) = .halt) :
    stepMap (W, N) = .halt := by
  unfold jun at hj
  unfold stepMap
  simp only
  rw [if_neg (by omega)]
  split at hj
  · next c1 hr1 =>
    rw [hr1]
    simp only
    rw [hj]
    simp only
    rw [if_neg (by omega), hh]
  · cases hj

/-- The wall `1 K(24) K(7) K(1)`, listed from the head leftwards. -/
def wallH : List Bool :=
  [true, false, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true,
  false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true,
  true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true,
  false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true,
  true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false,
  true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true,
  false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true]

theorem wallH_length : wallH.length = 118 := by decide +kernel

/-- The left part of the junction that part 1 builds on `wallH`. -/
def junL : List Bool :=
  match jun wallH with
  | some (_, _, L) => L
  | none => []

theorem junL_length : junL.length = 117 := by decide +kernel

theorem jun_wallH : jun wallH = some (247, 12, junL) := by decide +kernel

theorem part3_halts : arun trans rulesR rulesL (fun c => (decodeS c).isSome) (fuel junL.length)
    (ini2 0 junL (junL.length + 14)) = .halt := by decide +kernel

/-- The step map answers `halt` on the wall `1 K(24) K(7) K(1)` for every odd `N ≥ 252`. -/
theorem stepMap_halting_wall (N : Nat) (hN : 252 ≤ N) (ho : N % 2 = 1) : stepMap (wallH, N) = .halt := by
  have hl := wallH_length
  have hL := junL_length
  have e : (N - (wallH.length + 2 + (wallH.length + 14)) + 247) % 2 = 0 := by omega
  refine stepMap_halt jun_wallH (by omega) (by omega) ?_
  rw [e]
  exact part3_halts

/-- **From `1 K(24) K(7) K(1) A> 0 b^N 1` the machine halts, for every odd `N ≥ 252`.** -/
theorem halting_wall (N : Nat) (hN : 252 ≤ N) (ho : N % 2 = 1) : Halts trans (S wallH N) :=
  step_halt (p := (wallH, N)) (stepMap_halting_wall N hN ho)

/-- The wall `1 K(18) K(5)`, listed from the head leftwards. -/
def wallS : List Bool :=
  [true, false, true, true, true, true, true, false, true, true, false, true, true, false, true, true, false,
  true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true,
  true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false,
  true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true,
  false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true]

/-- **`1 K(18) K(5) A> 0 b^2 1` halts** (after 3,263 steps). -/
theorem halting_small : Halts trans (S wallS 2) := by
  have h : ∃ c', TM.fsteps trans 3263 ⟨wallS, false :: (repl true true false 2 ++ [true]), .A⟩ = some c' ∧
      TM.fstep trans c' = none := by
    decide +kernel
  obtain ⟨c', h1, h2⟩ := h
  have e := repl_spec true true false [true] blank 2
  have hs : S wallS 2 = (⟨wallS, false :: (repl true true false 2 ++ [true]), .A⟩ : FCfg St).toCfg := by
    simp only [FCfg.toCfg, S, app_cons, e]
    rfl
  rw [hs]
  refine ⟨3263, c'.toCfg, ?_, ?_⟩
  · rw [FCfg.steps_eq, h1]; rfl
  · rw [FCfg.step_eq, h2]; rfl

end H3292
