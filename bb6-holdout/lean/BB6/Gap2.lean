import BB6.Pkt2

/-!
# The wall and end events of the gap phase at the level of positions

* `ev_gap_end`: the gap at g has only a stripe (of odd length 2k + 1) to its right, up to the width W = g + 4 + 2k:
  k + 1 wall bounces off the blank end, then GAP→blank end.  A packet starts at g + 2k + 1, the new end marker sits
  at g + 2k + 5 and the width becomes W + 3.
* `ev_gap_wall_marker`: the gap at g meets a wall at g + 4 + 2k (2k + 1 stripe cells between) and the shift finds a
  marker at p = g + 6 + 2k + 2j followed by a stripe cell: gap and wall vanish and a gap opens at p.
* `ev_gap_wall_wall`: the shift finds a wall at g + 6 + 2k + 2j − 1 ... (2j − 1 stripe cells after the first wall):
  it becomes a block, and a packet heads left from g + 2k + 1.
* `ev_gap_wall_block`: the shift finds a block at g + 6 + 2k + 2j: it becomes a wall two cells further right, and a
  packet heads left.
* `ev_gap_wall_blank`: the shift reaches the blank end (W = g + 6 + 2k + 2j): an end marker forms at W + 1 and the
  width becomes W + 3; a packet heads left.
* `ev_gap_wall_endmarker`: the shift uses up the end marker at W − 2 = g + 6 + 2k + 2j: the new end marker sits at
  W + 1, the width becomes W + 3; a packet heads left.

The two bookkeeping lemmas `buildL_eq` and `build_eq` write the tape on either side of a point as one stripe of an
explicit length followed by a fixed rest, uniformly in where the point is moved to.
-/

namespace BB6

/-- The first mark of `msR` starts after `q`, or there is none and the width is beyond `q`. -/
def strictAfter (q W : Nat) : List Mark → Prop
  | [] => q < W
  | m :: _ => q < m.p

theorem strictAfter_startsAt {q W : Nat} {msR : List Mark} (h : strictAfter q W msR) : startsAt (q + 1) W msR := by
  cases msR <;> simp only [strictAfter, startsAt] at h ⊢ <;> omega

/-- Left of `g` (which has a stripe cell before it) the tape is a stripe of n + 1 cells and then a fixed rest, for
either value of the cell at the point and for every point `g + m`. -/
theorem buildL_eq (msL : List Mark) (g : Nat) (hb : stripeBefore g msL) :
    ∃ n rest, ∀ b m, buildL b (g + m) msL = stripe (!b) (n + 1 + m) rest := by
  cases msL with
  | nil =>
    simp only [stripeBefore] at hb
    refine ⟨g - 1, blank, fun b m => ?_⟩
    have e : g + m = g - 1 + 1 + m := by omega
    show stripe (!b) (g + m) blank = _
    rw [e]
  | cons m0 ms =>
    simp only [stripeBefore] at hb
    refine ⟨g - (m0.p + mlen m0.t) - 1, app (mcells m0.t).reverse (buildL (mval m0.t) m0.p ms), fun b m => ?_⟩
    have e : g + m - (m0.p + mlen m0.t) = g - (m0.p + mlen m0.t) - 1 + 1 + m := by omega
    show stripe (!b) (g + m - (m0.p + mlen m0.t)) _ = _
    rw [e]

/-- Right of `q` (where nothing starts) the tape is a stripe of ℓ cells and then a fixed rest, for either value of
the cell before the point and for every point `q − m` with m ≤ q. -/
theorem build_eq (msR : List Mark) (q W : Nat) (h : startsAt q W msR) :
    ∃ ℓ s, ∀ b m, m ≤ q → build b (q - m) msR W = stripe (!b) (ℓ + m) s := by
  cases msR with
  | nil =>
    simp only [startsAt] at h
    refine ⟨W - q, blank, fun b m hm => ?_⟩
    have e : W - (q - m) = W - q + m := by omega
    show stripe (!b) (W - (q - m)) blank = _
    rw [e]
  | cons m0 ms =>
    simp only [startsAt] at h
    refine ⟨m0.p - q, app (mcells m0.t) (build (mval m0.t) (m0.p + mlen m0.t) ms W), fun b m hm => ?_⟩
    have e : m0.p - (q - m) = m0.p - q + m := by omega
    show stripe (!b) (m0.p - (q - m)) _ = _
    rw [e]

theorem stripe_true_five (m : Nat) (s : Tape) :
    stripe true (m + 5) s = cons true (cons false (cons true (cons false (cons true (stripe false m s))))) := rfl

theorem stripe_true_odd (k : Nat) (s : Tape) : stripe true (2 * k + 1) s = rep k [true, false] (cons true s) := by
  rw [stripe_two_add]; rfl

theorem stripe_false_odd (k : Nat) (s : Tape) : stripe false (2 * k + 1) s = rep k [false, true] (cons false s) := by
  rw [stripe_two_add]; rfl

/-- The gap meets nothing: only a stripe of 2k + 1 cells to its right, then blank (W = g + 4 + 2k). -/
theorem ev_gap_end (msL : List Mark) (g k : Nat) (hb : stripeBefore g msL) :
    steps (wallbounceSteps (k + 1) 0 + 13) (midCfg msL g [] (g + 4 + 2 * k))
      = some (pktCfg msL (g + 2 * k + 1) [⟨.M, g + 2 * k + 5⟩] (g + 4 + 2 * k + 3)) := by
  obtain ⟨n, rest, hL⟩ := buildL_eq msL g hb
  have hstart : midCfg msL g [] (g + 4 + 2 * k)
      = ⟨cons false (cons false (buildL false (g + 0) msL)), cons false (stripe true (g + 4 + 2 * k - (g + 3)) blank), .E⟩ := rfl
  have hLp : buildL true (g + 2 * k + 1) msL = stripe false (n + 1 + (2 * k + 1)) rest := by
    have h := hL true (2 * k + 1)
    have e : g + 2 * k + 1 = g + (2 * k + 1) := by omega
    rw [e]; simpa using h
  have hend : pktCfg msL (g + 2 * k + 1) [⟨.M, g + 2 * k + 5⟩] (g + 4 + 2 * k + 3)
      = ⟨buildL true (g + 2 * k + 1) msL,
         cons true (cons true (stripe true (g + 2 * k + 5 - (g + 2 * k + 1 + 2))
           (cons true (cons true (stripe false (g + 4 + 2 * k + 3 - (g + 2 * k + 5 + 2)) blank))))), .A⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 2 * k + 5 - (g + 2 * k + 1 + 2) = 2 := by omega
  have e₃ : g + 4 + 2 * k + 3 - (g + 2 * k + 5 + 2) = 0 := by omega
  have e₄ : n + 1 + (2 * k + 1) = 2 * (k + 1) + n := by omega
  conv at hstart => rhs; rw [hL, e₁, stripe_true_odd, Bool.not_false, Nat.add_zero, stripe_succ, Bool.not_true]
  conv at hend => rhs; rw [hLp, e₂, e₃, stripe_zero, e₄, stripe_two_add, Bool.not_false]
  rw [hstart, hend]
  have h := gap_blank_end (k + 1) (stripe false n rest)
  rw [← rep_cons2 k true false blank, cons_false_blank] at h
  exact h

/-- The gap meets a wall at g + 4 + 2k; the shift finds a marker at p = g + 6 + 2k + 2j followed by a stripe cell:
gap and wall vanish, and a gap opens at p. -/
theorem ev_gap_wall_marker (msL msR : List Mark) (g k j W : Nat) (hb : stripeBefore g msL)
    (ha : strictAfter (g + 6 + 2 * k + 2 * j + 2) W msR) :
    steps (wallbounceSteps (k + 1) 0 + (2 * j + 8))
        (midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.M, g + 6 + 2 * k + 2 * j⟩ :: msR) W)
      = some (midCfg msL (g + 6 + 2 * k + 2 * j) msR W) := by
  obtain ⟨n, rest, hL⟩ := buildL_eq msL g hb
  obtain ⟨ℓ, s, hR⟩ := build_eq msR (g + 6 + 2 * k + 2 * j + 2 + 1) W (strictAfter_startsAt ha)
  have hstart : midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.M, g + 6 + 2 * k + 2 * j⟩ :: msR) W
      = ⟨cons false (cons false (buildL false (g + 0) msL)),
         cons false (stripe true (g + 4 + 2 * k - (g + 3)) (cons false (cons false
           (stripe true (g + 6 + 2 * k + 2 * j - (g + 4 + 2 * k + 2)) (cons true (cons true
             (build true (g + 6 + 2 * k + 2 * j + 2 + 1 - 1) msR W))))))), .E⟩ := rfl
  have hLp : buildL false (g + 6 + 2 * k + 2 * j) msL = stripe true (n + 1 + (6 + 2 * k + 2 * j)) rest := by
    have h := hL false (6 + 2 * k + 2 * j)
    have e : g + 6 + 2 * k + 2 * j = g + (6 + 2 * k + 2 * j) := by omega
    rw [e]; simpa using h
  have hend : midCfg msL (g + 6 + 2 * k + 2 * j) msR W
      = ⟨cons false (cons false (buildL false (g + 6 + 2 * k + 2 * j) msL)),
         cons false (build false (g + 6 + 2 * k + 2 * j + 2 + 1 - 0) msR W), .E⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 6 + 2 * k + 2 * j - (g + 4 + 2 * k + 2) = 2 * j := by omega
  have e₃ : n + 1 + (6 + 2 * k + 2 * j) = 2 * j + (2 * (k + 1) + n) + 5 := by omega
  conv at hstart => rhs; rw [hL, Nat.add_zero, Bool.not_false, e₁, stripe_true_odd, e₂, stripe_even, Bool.not_true,
    hR true 1 (by omega), Bool.not_true, stripe_succ false ℓ s, Bool.not_false]
  conv at hend => rhs; rw [hLp, e₃, stripe_true_five, stripe_two_add, Bool.not_false, stripe_two_add, Bool.not_false,
    hR false 0 (by omega), Nat.add_zero, Bool.not_false]
  rw [hstart, hend]
  have h := gap_wall_marker (k + 1) j (stripe false n rest) (stripe true ℓ s)
  rw [← rep_cons2 k true false] at h
  exact h

/-- The gap meets a wall at g + 4 + 2k; the shift finds a second wall at g + 7 + 2k + 2j (2j + 1 stripe cells after
the first) followed by a stripe cell: the second wall becomes a block and a packet heads left from g + 2k + 1. -/
theorem ev_gap_wall_wall (msL msR : List Mark) (g k j W : Nat) (hb : stripeBefore g msL)
    (ha : strictAfter (g + 7 + 2 * k + 2 * j + 2) W msR) :
    steps (wallbounceSteps (k + 1) 0 + (6 * (j + 1) + 13))
        (midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.W, g + 7 + 2 * k + 2 * j⟩ :: msR) W)
      = some (pktCfg msL (g + 2 * k + 1) (⟨.B, g + 7 + 2 * k + 2 * j⟩ :: msR) W) := by
  obtain ⟨n, rest, hL⟩ := buildL_eq msL g hb
  obtain ⟨ℓ, s, hR⟩ := build_eq msR (g + 7 + 2 * k + 2 * j + 2 + 1) W (strictAfter_startsAt ha)
  have hL0 : buildL false (g + 0) msL = stripe true (n + 1) rest := by
    have h := hL false 0; rw [Nat.add_zero (n + 1), Bool.not_false] at h; exact h
  have hLp : buildL true (g + 2 * k + 1) msL = stripe false (n + 1 + (2 * k + 1)) rest := by
    have h := hL true (2 * k + 1)
    have e : g + 2 * k + 1 = g + (2 * k + 1) := by omega
    rw [e]; simpa using h
  have hR0 : build true (g + 7 + 2 * k + 2 * j + 3) msR W = stripe false ℓ s := by
    have h := hR true 0 (by omega)
    have e : g + 7 + 2 * k + 2 * j + 2 + 1 - 0 = g + 7 + 2 * k + 2 * j + 3 := by omega
    rw [e, Nat.add_zero ℓ, Bool.not_true] at h; exact h
  have hR1 : build false (g + 7 + 2 * k + 2 * j + 2) msR W = cons true (stripe false ℓ s) := by
    have h := hR false 1 (by omega)
    have e : g + 7 + 2 * k + 2 * j + 2 + 1 - 1 = g + 7 + 2 * k + 2 * j + 2 := by omega
    rw [e, Bool.not_false, stripe_succ true ℓ s, Bool.not_true] at h; exact h
  have hstart : midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.W, g + 7 + 2 * k + 2 * j⟩ :: msR) W
      = ⟨cons false (cons false (buildL false (g + 0) msL)),
         cons false (stripe true (g + 4 + 2 * k - (g + 3)) (cons false (cons false
           (stripe true (g + 7 + 2 * k + 2 * j - (g + 4 + 2 * k + 2)) (cons false (cons false
             (build false (g + 7 + 2 * k + 2 * j + 2) msR W))))))), .E⟩ := rfl
  have hend : pktCfg msL (g + 2 * k + 1) (⟨.B, g + 7 + 2 * k + 2 * j⟩ :: msR) W
      = ⟨buildL true (g + 2 * k + 1) msL,
         cons true (cons true (stripe true (g + 7 + 2 * k + 2 * j - (g + 2 * k + 1 + 2)) (cons true (cons true (cons true
           (build true (g + 7 + 2 * k + 2 * j + 3) msR W)))))), .A⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 7 + 2 * k + 2 * j - (g + 4 + 2 * k + 2) = 2 * j + 1 := by omega
  have e₃ : g + 7 + 2 * k + 2 * j - (g + 2 * k + 1 + 2) = 2 * (j + 2) := by omega
  have e₄ : n + 1 + (2 * k + 1) = 2 * (k + 1) + n := by omega
  conv at hstart => rhs; rw [hL0, e₁, stripe_true_odd, e₂, stripe_true_odd, hR1]
  conv at hend => rhs; rw [hLp, e₄, stripe_two_add, Bool.not_false, e₃, stripe_even, Bool.not_true, hR0]
  rw [hstart, hend]
  have h := gap_wall_wall (k + 1) (j + 1) (stripe false n rest) (stripe false ℓ s)
  rw [← rep_cons2 k true false, ← rep_cons2 j true false (cons false (cons true (stripe false ℓ s))),
    rep_cons2 (j + 1) true false (cons true (cons true (cons true (stripe false ℓ s))))] at h
  exact h

/-- The gap meets a wall at g + 4 + 2k; the shift finds a block at g + 6 + 2k + 2j followed by a stripe cell: the
block becomes a wall two cells further right and a packet heads left from g + 2k + 1. -/
theorem ev_gap_wall_block (msL msR : List Mark) (g k j W : Nat) (hb : stripeBefore g msL)
    (ha : strictAfter (g + 6 + 2 * k + 2 * j + 3) W msR) :
    steps (wallbounceSteps (k + 1) 0 + (6 * j + 19))
        (midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.B, g + 6 + 2 * k + 2 * j⟩ :: msR) W)
      = some (pktCfg msL (g + 2 * k + 1) (⟨.W, g + 6 + 2 * k + 2 * j + 2⟩ :: msR) W) := by
  obtain ⟨n, rest, hL⟩ := buildL_eq msL g hb
  obtain ⟨ℓ, s, hR⟩ := build_eq msR (g + 6 + 2 * k + 2 * j + 3 + 1) W (strictAfter_startsAt ha)
  have hL0 : buildL false (g + 0) msL = stripe true (n + 1) rest := by
    have h := hL false 0; rw [Nat.add_zero (n + 1), Bool.not_false] at h; exact h
  have hLp : buildL true (g + 2 * k + 1) msL = stripe false (n + 1 + (2 * k + 1)) rest := by
    have h := hL true (2 * k + 1)
    have e : g + 2 * k + 1 = g + (2 * k + 1) := by omega
    rw [e]; simpa using h
  have hR0 : build false (g + 6 + 2 * k + 2 * j + 2 + 2) msR W = stripe true ℓ s := by
    have h := hR false 0 (by omega)
    have e : g + 6 + 2 * k + 2 * j + 3 + 1 - 0 = g + 6 + 2 * k + 2 * j + 2 + 2 := by omega
    rw [e, Nat.add_zero ℓ, Bool.not_false] at h; exact h
  have hR1 : build true (g + 6 + 2 * k + 2 * j + 3) msR W = cons false (stripe true ℓ s) := by
    have h := hR true 1 (by omega)
    have e : g + 6 + 2 * k + 2 * j + 3 + 1 - 1 = g + 6 + 2 * k + 2 * j + 3 := by omega
    rw [e, Bool.not_true, stripe_succ false ℓ s, Bool.not_false] at h; exact h
  have hstart : midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.B, g + 6 + 2 * k + 2 * j⟩ :: msR) W
      = ⟨cons false (cons false (buildL false (g + 0) msL)),
         cons false (stripe true (g + 4 + 2 * k - (g + 3)) (cons false (cons false
           (stripe true (g + 6 + 2 * k + 2 * j - (g + 4 + 2 * k + 2)) (cons true (cons true (cons true
             (build true (g + 6 + 2 * k + 2 * j + 3) msR W)))))))), .E⟩ := rfl
  have hend : pktCfg msL (g + 2 * k + 1) (⟨.W, g + 6 + 2 * k + 2 * j + 2⟩ :: msR) W
      = ⟨buildL true (g + 2 * k + 1) msL,
         cons true (cons true (stripe true (g + 6 + 2 * k + 2 * j + 2 - (g + 2 * k + 1 + 2)) (cons false (cons false
           (build false (g + 6 + 2 * k + 2 * j + 2 + 2) msR W))))), .A⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 6 + 2 * k + 2 * j - (g + 4 + 2 * k + 2) = 2 * j := by omega
  have e₃ : g + 6 + 2 * k + 2 * j + 2 - (g + 2 * k + 1 + 2) = 2 * j + 5 := by omega
  have e₄ : n + 1 + (2 * k + 1) = 2 * (k + 1) + n := by omega
  have h5 : stripe true 5 (cons false (cons false (stripe true ℓ s)))
      = cons true (cons false (cons true (cons false (cons true (cons false (cons false (stripe true ℓ s))))))) := rfl
  conv at hstart => rhs; rw [hL0, e₁, stripe_true_odd, e₂, stripe_even, Bool.not_true, hR1]
  conv at hend => rhs; rw [hLp, e₄, stripe_two_add, Bool.not_false, e₃, stripe_two_add, Bool.not_true, hR0, h5]
  rw [hstart, hend]
  have h := gap_wall_block (k + 1) j (stripe false n rest) (stripe true ℓ s)
  rw [← rep_cons2 k true false] at h
  exact h

/-- The gap meets a wall at g + 4 + 2k with only a stripe of 2j + 1 cells beyond it (W = g + 7 + 2k + 2j): the shift
reaches blank tape; an end marker forms at W and the width becomes W + 2; a packet heads left from g + 2k + 1. -/
theorem ev_gap_wall_blank (msL : List Mark) (g k j : Nat) (hb : stripeBefore g msL) :
    steps (wallbounceSteps (k + 1) 0 + (6 * (j + 1) + 13))
        (midCfg msL g [⟨.W, g + 4 + 2 * k⟩] (g + 7 + 2 * k + 2 * j))
      = some (pktCfg msL (g + 2 * k + 1) [⟨.M, g + 7 + 2 * k + 2 * j⟩] (g + 7 + 2 * k + 2 * j + 2)) := by
  obtain ⟨n, rest, hL⟩ := buildL_eq msL g hb
  have hL0 : buildL false (g + 0) msL = stripe true (n + 1) rest := by
    have h := hL false 0; rw [Nat.add_zero (n + 1), Bool.not_false] at h; exact h
  have hLp : buildL true (g + 2 * k + 1) msL = stripe false (n + 1 + (2 * k + 1)) rest := by
    have h := hL true (2 * k + 1)
    have e : g + 2 * k + 1 = g + (2 * k + 1) := by omega
    rw [e]; simpa using h
  have hstart : midCfg msL g [⟨.W, g + 4 + 2 * k⟩] (g + 7 + 2 * k + 2 * j)
      = ⟨cons false (cons false (buildL false (g + 0) msL)),
         cons false (stripe true (g + 4 + 2 * k - (g + 3)) (cons false (cons false
           (stripe true (g + 7 + 2 * k + 2 * j - (g + 4 + 2 * k + 2)) blank)))), .E⟩ := rfl
  have hend : pktCfg msL (g + 2 * k + 1) [⟨.M, g + 7 + 2 * k + 2 * j⟩] (g + 7 + 2 * k + 2 * j + 2)
      = ⟨buildL true (g + 2 * k + 1) msL,
         cons true (cons true (stripe true (g + 7 + 2 * k + 2 * j - (g + 2 * k + 1 + 2)) (cons true (cons true
           (stripe false (g + 7 + 2 * k + 2 * j + 2 - (g + 7 + 2 * k + 2 * j + 2)) blank))))), .A⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 7 + 2 * k + 2 * j - (g + 4 + 2 * k + 2) = 2 * j + 1 := by omega
  have e₃ : g + 7 + 2 * k + 2 * j - (g + 2 * k + 1 + 2) = 2 * (j + 2) := by omega
  have e₄ : n + 1 + (2 * k + 1) = 2 * (k + 1) + n := by omega
  conv at hstart => rhs; rw [hL0, e₁, stripe_true_odd, e₂, stripe_true_odd]
  conv at hend => rhs; rw [hLp, e₄, stripe_two_add, Bool.not_false, e₃, stripe_even, Bool.not_true,
    Nat.sub_self (g + 7 + 2 * k + 2 * j + 2), stripe_zero]
  rw [hstart, hend]
  have h := gap_wall_blank (k + 1) (j + 1) (stripe false n rest)
  rw [← rep_cons2 k true false, ← rep_cons2 j true false blank, cons_false_blank,
    rep_cons2 (j + 1) true false (cons true (cons true blank))] at h
  exact h

/-- The gap meets a wall at g + 4 + 2k; the shift uses up the end marker at W − 2 = g + 6 + 2k + 2j: a new end
marker forms at W + 1, the width becomes W + 3, and a packet heads left from g + 2k + 1. -/
theorem ev_gap_wall_endmarker (msL : List Mark) (g k j : Nat) (hb : stripeBefore g msL) :
    steps (wallbounceSteps (k + 1) 0 + (6 * j + 29))
        (midCfg msL g [⟨.W, g + 4 + 2 * k⟩, ⟨.M, g + 6 + 2 * k + 2 * j⟩] (g + 6 + 2 * k + 2 * j + 2))
      = some (pktCfg msL (g + 2 * k + 1) [⟨.M, g + 6 + 2 * k + 2 * j + 3⟩] (g + 6 + 2 * k + 2 * j + 5)) := by
  obtain ⟨n, rest, hL⟩ := buildL_eq msL g hb
  have hL0 : buildL false (g + 0) msL = stripe true (n + 1) rest := by
    have h := hL false 0; rw [Nat.add_zero (n + 1), Bool.not_false] at h; exact h
  have hLp : buildL true (g + 2 * k + 1) msL = stripe false (n + 1 + (2 * k + 1)) rest := by
    have h := hL true (2 * k + 1)
    have e : g + 2 * k + 1 = g + (2 * k + 1) := by omega
    rw [e]; simpa using h
  have hstart : midCfg msL g [⟨.W, g + 4 + 2 * k⟩, ⟨.M, g + 6 + 2 * k + 2 * j⟩] (g + 6 + 2 * k + 2 * j + 2)
      = ⟨cons false (cons false (buildL false (g + 0) msL)),
         cons false (stripe true (g + 4 + 2 * k - (g + 3)) (cons false (cons false
           (stripe true (g + 6 + 2 * k + 2 * j - (g + 4 + 2 * k + 2)) (cons true (cons true
             (stripe false (g + 6 + 2 * k + 2 * j + 2 - (g + 6 + 2 * k + 2 * j + 2)) blank))))))), .E⟩ := rfl
  have hend : pktCfg msL (g + 2 * k + 1) [⟨.M, g + 6 + 2 * k + 2 * j + 3⟩] (g + 6 + 2 * k + 2 * j + 5)
      = ⟨buildL true (g + 2 * k + 1) msL,
         cons true (cons true (stripe true (g + 6 + 2 * k + 2 * j + 3 - (g + 2 * k + 1 + 2)) (cons true (cons true
           (stripe false (g + 6 + 2 * k + 2 * j + 5 - (g + 6 + 2 * k + 2 * j + 3 + 2)) blank))))), .A⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 6 + 2 * k + 2 * j - (g + 4 + 2 * k + 2) = 2 * j := by omega
  have e₃ : g + 6 + 2 * k + 2 * j + 3 - (g + 2 * k + 1 + 2) = 2 * (j + 3) := by omega
  have e₄ : n + 1 + (2 * k + 1) = 2 * (k + 1) + n := by omega
  have e₅ : g + 6 + 2 * k + 2 * j + 5 - (g + 6 + 2 * k + 2 * j + 3 + 2) = 0 := by omega
  conv at hstart => rhs; rw [hL0, e₁, stripe_true_odd, e₂, stripe_even, Bool.not_true,
    Nat.sub_self (g + 6 + 2 * k + 2 * j + 2), stripe_zero]
  conv at hend => rhs; rw [hLp, e₄, stripe_two_add, Bool.not_false, e₃, stripe_even, Bool.not_true, e₅, stripe_zero]
  rw [hstart, hend]
  have h := gap_wall_endmarker (k + 1) j (stripe false n rest)
  rw [← rep_cons2 k true false,
    rep_cons2 j true false (cons true (cons false (cons true (cons false (cons true (cons true blank)))))),
    rep_cons2 (j + 1) true false (cons true (cons false (cons true (cons true blank)))),
    rep_cons2 (j + 2) true false (cons true (cons true blank))] at h
  exact h

end BB6
