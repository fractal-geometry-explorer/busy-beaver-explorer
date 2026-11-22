import Stack

/-!
# Closed empty counters stay in one pile at the bottom

For `mstep` (the counter-stack step of `py/stackmodel.py`, proved to be the machine's step in `Stack.lean` wherever
`stepRes` answers; walls are listed top first).  `good ws`: every `K'(0)` (`.c 0`) and every `K(0)` (`.o 0`) has
only `K'(0)`s below it.  So a good wall is `X ++ K'(0)^a` with no `K'(0)` in `X` and `K(0)` at most as the last
item of `X`.

* `mstep_good`: a step keeps the wall good, unless the step itself makes a `K(0)` somewhere other than directly on
  the pile (`okO`, which fails only when a rebuilt count `3k/2 + om` is exactly 0).
* `good_c0`: on a good wall an odd signal on `K'(0)` always has `1 K'(0)^a` below it, which is the case
  `res` of `Stack.lean` covers (`allC0`).  So the case `res` leaves open ("an odd signal on `K'(0)` under other
  items") needs a rebuilt count 0 first, and the only gap left in the stack rules is a count going to 0 or below.
* `good_iter`: along any sequence of signals, as long as no step makes a count 0 away from the pile, every wall
  is good.
-/

namespace H3292

/-- Every `K'(0)` and every `K(0)` has only `K'(0)`s below it. -/
def good : List It → Bool
  | [] => true
  | .c 0 :: ws => allC0 ws
  | .o 0 :: ws => allC0 ws
  | .o (_ + 1) :: ws => good ws
  | .c (_ + 1) :: ws => good ws

/-- Every `K(0)` has only `K'(0)`s below it (what a step must not break: a rebuilt count 0 away from the pile). -/
def okO : List It → Bool
  | [] => true
  | .o 0 :: ws => allC0 ws
  | _ :: ws => okO ws

theorem allC0_good : ∀ ws : List It, allC0 ws = true → good ws = true
  | [], _ => rfl
  | .c 0 :: ws, h => by simp only [allC0] at h; simp only [good, h]
  | .c (_ + 1) :: _, h => by simp [allC0] at h
  | .o _ :: _, h => by simp [allC0] at h

theorem good_tail : ∀ (i : It) (ws : List It), good (i :: ws) = true → good ws = true
  | .c 0, ws, h => allC0_good ws (by simpa [good] using h)
  | .o 0, ws, h => allC0_good ws (by simpa [good] using h)
  | .o (_ + 1), ws, h => by simpa [good] using h
  | .c (_ + 1), ws, h => by simpa [good] using h

/-- **A step keeps the pile at the bottom**, unless it makes a `K(0)` away from the pile. -/
theorem mstep_good : ∀ (ws : List It) (s : Bool) (ws' : List It) (om orr : Int),
    good ws = true → mstep ws s = some (ws', om, orr) → okO ws' = true → good ws' = true
  | [], false, ws', om, orr, _, h, _ => by
    simp only [mstep, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
  | [], true, ws', om, orr, _, h, _ => by
    simp only [mstep, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
  | .o k :: V, false, ws', om, orr, hg, h, _ => by
    simp only [mstep, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    cases k with
    | zero => simpa [good] using hg
    | succ k => simpa [good] using hg
  | .o k :: V, true, ws', om, orr, hg, h, ho => by
    have hV := good_tail _ V hg
    simp only [mstep] at h
    cases e : mstep V (k % 2 == 1) with
    | none => rw [e] at h; cases h
    | some r =>
      obtain ⟨V', om', orr'⟩ := r
      rw [e] at h
      simp only at h
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1] at ho ⊢
        cases hn : (((3 * k / 2 : Nat) : Int) + om').toNat with
        | zero => rw [hn] at ho; simpa [okO, good] using ho
        | succ n =>
          rw [hn] at ho
          simp only [okO, good] at ho ⊢
          exact mstep_good V (k % 2 == 1) V' om' orr' hV e ho
  | .c 0 :: V, true, ws', om, orr, hg, h, _ => by
    simp only [mstep, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    simpa [good, allC0] using hg
  | .c 0 :: V, false, ws', om, orr, hg, h, ho => by
    have hV := good_tail _ V hg
    simp only [mstep] at h
    split at h
    · cases h
    · next V' om' orr' e =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1] at ho ⊢
      exact mstep_good V _ V' om' orr' hV e ho
  | .c (j + 1) :: V, s, ws', om, orr, hg, h, ho => by
    have hV := good_tail _ V hg
    simp only [mstep] at h
    split at h
    · cases h
    · next V' om' orr' e =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1] at ho ⊢
      exact mstep_good V _ V' om' orr' hV e ho

/-- On a good wall an odd signal on `K'(0)` has only `K'(0)`s below it: the case `res` covers. -/
theorem good_c0 (ws : List It) (h : good (.c 0 :: ws) = true) : allC0 ws = true := by
  simpa [good] using h

/-- Walls along a sequence of signals (`none` once a step fails). -/
def mrun : List It → List Bool → Option (List It)
  | ws, [] => some ws
  | ws, s :: ss => (mstep ws s).bind fun r => mrun r.1 ss

/-- **Along any sequence of signals** from a good wall, every wall reached is good, as long as no step has made a
`K(0)` away from the pile. -/
theorem good_iter : ∀ (ws : List It) (ss : List Bool) (ws' : List It), good ws = true →
    mrun ws ss = some ws' →
    (∀ (n : Nat) (w : List It), n ≤ ss.length → mrun ws (ss.take n) = some w → okO w = true) →
    good ws' = true
  | ws, [], ws', hg, h, _ => by simp only [mrun, Option.some.injEq] at h; rw [← h]; exact hg
  | ws, s :: ss, ws', hg, h, hok => by
    simp only [mrun] at h
    cases e : mstep ws s with
    | none => rw [e] at h; cases h
    | some r =>
      obtain ⟨w1, om, orr⟩ := r
      rw [e] at h
      simp only [Option.bind_some] at h
      have h1 : okO w1 = true := hok 1 w1 (by simp) (by simp [mrun, e])
      have g1 := mstep_good ws s w1 om orr hg e h1
      refine good_iter w1 ss ws' g1 h ?_
      intro n w hn hw
      exact hok (n + 1) w (by simp; omega) (by simp [mrun, e, hw])

/-- The empty wall (`1`) is good. -/
theorem good_nil : good [] = true := rfl

end H3292
