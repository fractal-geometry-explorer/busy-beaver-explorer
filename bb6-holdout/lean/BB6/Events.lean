import BB6.Contact

/-!
# The events of the round, under the general contact conditions

The same statements as `ev_*` in `Mid`, `Gap2`, `Blk` and `Pkt2`, with the hypothesis on the cell before the gap
weakened from "a stripe cell" to "reads 1" (`oneBefore`: a 1-mark may touch the gap), the hypothesis on the cell
after a marker met by the gap weakened to "reads 0" (`zeroAfter`: a 0-mark may touch the marker), and the cell before
a block that stops a packet weakened to "reads 0" (`zeroBefore`).  These are exactly the configurations the mark
model (`Model.event`, `Model.packetBack`) treats as covered; the round theorem uses these versions.

The one place where touching matters for the statement itself is the swap and merge with k = 0 (a meeting at
distance 0 or 2): the new marker at g − 1 would overlap a mark touching g, so these two need a stripe cell before
the gap unless k ≥ 1 — which is also when the model's overlap check lets them through.
-/

namespace BB6

/-- The packet's (or new gap's) left tape at g + 2k − 1, for k ≥ 1 or a stripe cell before g. -/
theorem buildL_shift_gen (msL : List Mark) (g k : Nat) (L' : Tape) (hb : oneBefore g msL)
    (hk : 1 ≤ k ∨ stripeBefore g msL) (hL : buildL false g msL = cons true L') :
    buildL true (g + 2 * k - 1) msL = rep k [false, true] L' := by
  cases k with
  | zero =>
    have hs : stripeBefore g msL := by
      rcases hk with hk | hk
      · omega
      · exact hk
    have h := buildL_succ msL false (g - 1) (stripeBefore_endsBy' hs)
    have e : g - 1 + 1 = g := by cases msL <;> simp only [stripeBefore] at hs <;> omega
    rw [e, hL, Bool.not_false] at h
    simpa [rep] using (cons_tail_eq h).symm
  | succ k =>
    have e : g + 2 * (k + 1) - 1 = g + (2 * k + 1) := by omega
    rw [e]
    exact buildL_odd_shift msL g k L' (oneBefore_endsBy hb) hL

/-- The swap event, general contact. -/
theorem ev_swap' (msL msR : List Mark) (g k W : Nat) (hL : oneBefore g msL) (hk : 1 ≤ k ∨ stripeBefore g msL)
    (hR : zeroAfter (g + 3 + 4 * k) W msR) :
    steps (bounceSteps k 0 + 21) (midCfg msL g (⟨.M, g + 3 + 4 * k⟩ :: msR) W)
      = some (midCfg (⟨.M, g + 2 * k - 1⟩ :: msL) (g + 2 * k + 1) msR W) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hL
  have hL2 := buildL_shift_gen msL g k L' hL hk hL1
  obtain ⟨R', hR1⟩ := zeroAfter_tail hR
  have hR2 := build_odd_shift msR (g + 3 + 4 * k) W k R' (zeroAfter_startsAt hR) hR1 (by omega)
  have hstart : midCfg msL g (⟨.M, g + 3 + 4 * k⟩ :: msR) W
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 3 + 4 * k - (g + 3)) (cons true (cons true (build true (g + 3 + 4 * k + 2) msR W)))), .E⟩ := rfl
  have hend : midCfg (⟨.M, g + 2 * k - 1⟩ :: msL) (g + 2 * k + 1) msR W
      = ⟨cons false (cons false (stripe true (g + 2 * k + 1 - (g + 2 * k - 1 + 2)) (cons true (cons true (buildL true (g + 2 * k - 1) msL))))),
         cons false (build false (g + 2 * k + 1 + 3) msR W), .E⟩ := rfl
  have e₁ : g + 3 + 4 * k - (g + 3) = 2 * (2 * k) := by omega
  have e₂ : g + 2 * k + 1 - (g + 2 * k - 1 + 2) = 0 := by omega
  have e₃ : g + 2 * k + 1 + 3 = g + 3 + 4 * k + 2 - (2 * k + 1) := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_even, Bool.not_true, hR1]
  conv at hend => rhs; rw [e₂, stripe_zero, hL2, e₃, hR2]
  rw [hstart, hend]
  exact gap_marker_swap k L' R'

/-- The merge event, general contact. -/
theorem ev_merge' (msL msR : List Mark) (g k W : Nat) (hL : oneBefore g msL) (hk : 1 ≤ k ∨ stripeBefore g msL)
    (hR : zeroAfter (g + 3 + 4 * k + 2) W msR) :
    steps (bounceSteps k 1 + 31) (midCfg msL g (⟨.M, g + 3 + 4 * k + 2⟩ :: msR) W)
      = some (pktCfg msL (g + 2 * k - 1) (⟨.W, g + 2 * k + 4⟩ :: msR) W) := by
  have hg := oneBefore_pos hL
  obtain ⟨L', hL1⟩ := oneBefore_tail hL
  have hL2 := buildL_shift_gen msL g k L' hL hk hL1
  obtain ⟨R', hR1⟩ := zeroAfter_tail hR
  have hR2 := build_odd_shift msR (g + 3 + 4 * k + 2) W k R' (zeroAfter_startsAt hR) hR1 (by omega)
  have hstart : midCfg msL g (⟨.M, g + 3 + 4 * k + 2⟩ :: msR) W
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 3 + 4 * k + 2 - (g + 3)) (cons true (cons true (build true (g + 3 + 4 * k + 2 + 2) msR W)))), .E⟩ := rfl
  have hend : pktCfg msL (g + 2 * k - 1) (⟨.W, g + 2 * k + 4⟩ :: msR) W
      = ⟨buildL true (g + 2 * k - 1) msL,
         cons true (cons true (stripe true (g + 2 * k + 4 - (g + 2 * k - 1 + 2)) (cons false (cons false (build false (g + 2 * k + 4 + 2) msR W))))), .A⟩ := rfl
  have e₁ : g + 3 + 4 * k + 2 - (g + 3) = 2 * (2 * k + 1) := by omega
  have e₂ : g + 2 * k + 4 - (g + 2 * k - 1 + 2) = 3 := by omega
  have e₃ : g + 2 * k + 4 + 2 = g + 3 + 4 * k + 2 + 2 - (2 * k + 1) := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_even, Bool.not_true, hR1]
  conv at hend => rhs; rw [e₂, hL2, e₃, hR2]
  rw [hstart, hend]
  exact gap_marker_merge k L' R'

/-- The packet's left tape after the gap's k + 1 wall bounces. -/
theorem buildL_pkt (msL : List Mark) (g k : Nat) (L' : Tape) (hb : oneBefore g msL) (hL : buildL false g msL = cons true L') :
    buildL true (g + 2 * k + 1) msL = rep (k + 1) [false, true] L' := by
  have e : g + 2 * k + 1 = g + (2 * k + 1) := by omega
  rw [e]
  exact buildL_odd_shift msL g k L' (oneBefore_endsBy hb) hL

/-- The gap meets nothing, general contact. -/
theorem ev_gap_end' (msL : List Mark) (g k : Nat) (hb : oneBefore g msL) :
    steps (wallbounceSteps (k + 1) 0 + 13) (midCfg msL g [] (g + 4 + 2 * k))
      = some (pktCfg msL (g + 2 * k + 1) [⟨.M, g + 2 * k + 5⟩] (g + 4 + 2 * k + 3)) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hb
  have hL2 := buildL_pkt msL g k L' hb hL1
  have hstart : midCfg msL g [] (g + 4 + 2 * k)
      = ⟨cons false (cons false (buildL false g msL)), cons false (stripe true (g + 4 + 2 * k - (g + 3)) blank), .E⟩ := rfl
  have hend : pktCfg msL (g + 2 * k + 1) [⟨.M, g + 2 * k + 5⟩] (g + 4 + 2 * k + 3)
      = ⟨buildL true (g + 2 * k + 1) msL,
         cons true (cons true (stripe true (g + 2 * k + 5 - (g + 2 * k + 1 + 2))
           (cons true (cons true (stripe false (g + 4 + 2 * k + 3 - (g + 2 * k + 5 + 2)) blank))))), .A⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 2 * k + 5 - (g + 2 * k + 1 + 2) = 2 := by omega
  have e₃ : g + 4 + 2 * k + 3 - (g + 2 * k + 5 + 2) = 0 := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_true_odd]
  conv at hend => rhs; rw [hL2, e₂, e₃, stripe_zero]
  rw [hstart, hend]
  have h := gap_blank_end (k + 1) L'
  rw [← rep_cons2 k true false blank, cons_false_blank] at h
  exact h

/-- Gap meets wall, shift meets marker; general contact before the gap. -/
theorem ev_gap_wall_marker' (msL msR : List Mark) (g k j W : Nat) (hb : oneBefore g msL)
    (hf : freeAt (g + 6 + 2 * k + 2 * j + 2) W msR) :
    steps (wallbounceSteps (k + 1) 0 + (2 * j + 8))
        (midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.M, g + 6 + 2 * k + 2 * j⟩ :: msR) W)
      = some (midCfg msL (g + 6 + 2 * k + 2 * j) msR W) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hb
  have hL2 : buildL false (g + 6 + 2 * k + 2 * j) msL
      = cons true (cons false (cons true (cons false (cons true (rep (j + (k + 1)) [false, true] L'))))) := by
    have e : g + 6 + 2 * k + 2 * j = g + (2 * (j + (k + 1)) + 4) := by omega
    rw [e, buildL_add msL false g _ (oneBefore_endsBy hb), if_pos (by omega), Bool.not_false, hL1, stripe_five_rep]
  have hR := build_free msR (g + 6 + 2 * k + 2 * j + 2) W hf
  have hstart : midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.M, g + 6 + 2 * k + 2 * j⟩ :: msR) W
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 4 + 2 * k - (g + 3)) (cons false (cons false
           (stripe true (g + 6 + 2 * k + 2 * j - (g + 4 + 2 * k + 2)) (cons true (cons true
             (build true (g + 6 + 2 * k + 2 * j + 2) msR W))))))), .E⟩ := rfl
  have hend : midCfg msL (g + 6 + 2 * k + 2 * j) msR W
      = ⟨cons false (cons false (buildL false (g + 6 + 2 * k + 2 * j) msL)),
         cons false (build false (g + 6 + 2 * k + 2 * j + 2 + 1) msR W), .E⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 6 + 2 * k + 2 * j - (g + 4 + 2 * k + 2) = 2 * j := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_true_odd, e₂, stripe_even, Bool.not_true, hR]
  conv at hend => rhs; rw [hL2]
  rw [hstart, hend]
  have h := gap_wall_marker (k + 1) j L' (build false (g + 6 + 2 * k + 2 * j + 2 + 1) msR W)
  rw [← rep_cons2 k true false, ← rep_add] at h
  exact h

/-- Gap meets wall, shift meets a second wall; general contact before the gap. -/
theorem ev_gap_wall_wall' (msL msR : List Mark) (g k j W : Nat) (hb : oneBefore g msL)
    (ha : strictAfter (g + 7 + 2 * k + 2 * j + 2) W msR) :
    steps (wallbounceSteps (k + 1) 0 + (6 * (j + 1) + 13))
        (midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.W, g + 7 + 2 * k + 2 * j⟩ :: msR) W)
      = some (pktCfg msL (g + 2 * k + 1) (⟨.B, g + 7 + 2 * k + 2 * j⟩ :: msR) W) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hb
  have hL2 := buildL_pkt msL g k L' hb hL1
  have hR := build_step msR false (g + 7 + 2 * k + 2 * j + 2) W ha
  rw [Bool.not_false] at hR
  have hstart : midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.W, g + 7 + 2 * k + 2 * j⟩ :: msR) W
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 4 + 2 * k - (g + 3)) (cons false (cons false
           (stripe true (g + 7 + 2 * k + 2 * j - (g + 4 + 2 * k + 2)) (cons false (cons false
             (build false (g + 7 + 2 * k + 2 * j + 2) msR W))))))), .E⟩ := rfl
  have hend : pktCfg msL (g + 2 * k + 1) (⟨.B, g + 7 + 2 * k + 2 * j⟩ :: msR) W
      = ⟨buildL true (g + 2 * k + 1) msL,
         cons true (cons true (stripe true (g + 7 + 2 * k + 2 * j - (g + 2 * k + 1 + 2)) (cons true (cons true (cons true
           (build true (g + 7 + 2 * k + 2 * j + 2 + 1) msR W)))))), .A⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 7 + 2 * k + 2 * j - (g + 4 + 2 * k + 2) = 2 * j + 1 := by omega
  have e₃ : g + 7 + 2 * k + 2 * j - (g + 2 * k + 1 + 2) = 2 * (j + 2) := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_true_odd, e₂, stripe_true_odd, hR]
  conv at hend => rhs; rw [hL2, e₃, stripe_even, Bool.not_true]
  rw [hstart, hend]
  have h := gap_wall_wall (k + 1) (j + 1) L' (build true (g + 7 + 2 * k + 2 * j + 2 + 1) msR W)
  rw [← rep_cons2 k true false,
    ← rep_cons2 j true false (cons false (cons true (build true (g + 7 + 2 * k + 2 * j + 2 + 1) msR W))),
    rep_cons2 (j + 1) true false (cons true (cons true (cons true (build true (g + 7 + 2 * k + 2 * j + 2 + 1) msR W))))] at h
  exact h

/-- Gap meets wall, shift meets a block; general contact before the gap. -/
theorem ev_gap_wall_block' (msL msR : List Mark) (g k j W : Nat) (hb : oneBefore g msL)
    (ha : strictAfter (g + 6 + 2 * k + 2 * j + 3) W msR) :
    steps (wallbounceSteps (k + 1) 0 + (6 * j + 19))
        (midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.B, g + 6 + 2 * k + 2 * j⟩ :: msR) W)
      = some (pktCfg msL (g + 2 * k + 1) (⟨.W, g + 6 + 2 * k + 2 * j + 2⟩ :: msR) W) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hb
  have hL2 := buildL_pkt msL g k L' hb hL1
  have hR := build_step msR true (g + 6 + 2 * k + 2 * j + 3) W ha
  rw [Bool.not_true] at hR
  have hstart : midCfg msL g (⟨.W, g + 4 + 2 * k⟩ :: ⟨.B, g + 6 + 2 * k + 2 * j⟩ :: msR) W
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 4 + 2 * k - (g + 3)) (cons false (cons false
           (stripe true (g + 6 + 2 * k + 2 * j - (g + 4 + 2 * k + 2)) (cons true (cons true (cons true
             (build true (g + 6 + 2 * k + 2 * j + 3) msR W)))))))), .E⟩ := rfl
  have hend : pktCfg msL (g + 2 * k + 1) (⟨.W, g + 6 + 2 * k + 2 * j + 2⟩ :: msR) W
      = ⟨buildL true (g + 2 * k + 1) msL,
         cons true (cons true (stripe true (g + 6 + 2 * k + 2 * j + 2 - (g + 2 * k + 1 + 2)) (cons false (cons false
           (build false (g + 6 + 2 * k + 2 * j + 3 + 1) msR W))))), .A⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 6 + 2 * k + 2 * j - (g + 4 + 2 * k + 2) = 2 * j := by omega
  have e₃ : g + 6 + 2 * k + 2 * j + 2 - (g + 2 * k + 1 + 2) = 2 * j + 5 := by omega
  have h5 : stripe true 5 (cons false (cons false (build false (g + 6 + 2 * k + 2 * j + 3 + 1) msR W)))
      = cons true (cons false (cons true (cons false (cons true (cons false (cons false
          (build false (g + 6 + 2 * k + 2 * j + 3 + 1) msR W))))))) := rfl
  conv at hstart => rhs; rw [hL1, e₁, stripe_true_odd, e₂, stripe_even, Bool.not_true, hR]
  conv at hend => rhs; rw [hL2, e₃, stripe_two_add, Bool.not_true, h5]
  rw [hstart, hend]
  have h := gap_wall_block (k + 1) j L' (build false (g + 6 + 2 * k + 2 * j + 3 + 1) msR W)
  rw [← rep_cons2 k true false] at h
  exact h

/-- Gap meets wall, shift reaches blank tape; general contact before the gap. -/
theorem ev_gap_wall_blank' (msL : List Mark) (g k j : Nat) (hb : oneBefore g msL) :
    steps (wallbounceSteps (k + 1) 0 + (6 * (j + 1) + 13))
        (midCfg msL g [⟨.W, g + 4 + 2 * k⟩] (g + 7 + 2 * k + 2 * j))
      = some (pktCfg msL (g + 2 * k + 1) [⟨.M, g + 7 + 2 * k + 2 * j⟩] (g + 7 + 2 * k + 2 * j + 2)) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hb
  have hL2 := buildL_pkt msL g k L' hb hL1
  have hstart : midCfg msL g [⟨.W, g + 4 + 2 * k⟩] (g + 7 + 2 * k + 2 * j)
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 4 + 2 * k - (g + 3)) (cons false (cons false
           (stripe true (g + 7 + 2 * k + 2 * j - (g + 4 + 2 * k + 2)) blank)))), .E⟩ := rfl
  have hend : pktCfg msL (g + 2 * k + 1) [⟨.M, g + 7 + 2 * k + 2 * j⟩] (g + 7 + 2 * k + 2 * j + 2)
      = ⟨buildL true (g + 2 * k + 1) msL,
         cons true (cons true (stripe true (g + 7 + 2 * k + 2 * j - (g + 2 * k + 1 + 2)) (cons true (cons true
           (stripe false (g + 7 + 2 * k + 2 * j + 2 - (g + 7 + 2 * k + 2 * j + 2)) blank))))), .A⟩ := rfl
  have e₁ : g + 4 + 2 * k - (g + 3) = 2 * k + 1 := by omega
  have e₂ : g + 7 + 2 * k + 2 * j - (g + 4 + 2 * k + 2) = 2 * j + 1 := by omega
  have e₃ : g + 7 + 2 * k + 2 * j - (g + 2 * k + 1 + 2) = 2 * (j + 2) := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_true_odd, e₂, stripe_true_odd]
  conv at hend => rhs; rw [hL2, e₃, stripe_even, Bool.not_true, Nat.sub_self (g + 7 + 2 * k + 2 * j + 2), stripe_zero]
  rw [hstart, hend]
  have h := gap_wall_blank (k + 1) (j + 1) L'
  rw [← rep_cons2 k true false, ← rep_cons2 j true false blank, cons_false_blank,
    rep_cons2 (j + 1) true false (cons true (cons true blank))] at h
  exact h

/-- Gap meets wall, shift uses up the end marker; general contact before the gap. -/
theorem ev_gap_wall_endmarker' (msL : List Mark) (g k j : Nat) (hb : oneBefore g msL) :
    steps (wallbounceSteps (k + 1) 0 + (6 * j + 29))
        (midCfg msL g [⟨.W, g + 4 + 2 * k⟩, ⟨.M, g + 6 + 2 * k + 2 * j⟩] (g + 6 + 2 * k + 2 * j + 2))
      = some (pktCfg msL (g + 2 * k + 1) [⟨.M, g + 6 + 2 * k + 2 * j + 3⟩] (g + 6 + 2 * k + 2 * j + 5)) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hb
  have hL2 := buildL_pkt msL g k L' hb hL1
  have hstart : midCfg msL g [⟨.W, g + 4 + 2 * k⟩, ⟨.M, g + 6 + 2 * k + 2 * j⟩] (g + 6 + 2 * k + 2 * j + 2)
      = ⟨cons false (cons false (buildL false g msL)),
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
  have e₅ : g + 6 + 2 * k + 2 * j + 5 - (g + 6 + 2 * k + 2 * j + 3 + 2) = 0 := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_true_odd, e₂, stripe_even, Bool.not_true,
    Nat.sub_self (g + 6 + 2 * k + 2 * j + 2), stripe_zero]
  conv at hend => rhs; rw [hL2, e₃, stripe_even, Bool.not_true, e₅, stripe_zero]
  rw [hstart, hend]
  have h := gap_wall_endmarker (k + 1) j L'
  rw [← rep_cons2 k true false,
    rep_cons2 j true false (cons true (cons false (cons true (cons false (cons true (cons true blank)))))),
    rep_cons2 (j + 1) true false (cons true (cons false (cons true (cons true blank)))),
    rep_cons2 (j + 2) true false (cons true (cons true blank))] at h
  exact h

/-- Gap meets block, shift meets marker; general contact before the gap. -/
theorem ev_gap_block_marker' (msL msR : List Mark) (g m j W : Nat) (hb : oneBefore g msL)
    (hf : freeAt (g + 9 + 2 * m + 2 * j + 2) W msR) :
    steps (2 * j + 2 * (m + 1) + 9)
        (midCfg msL g (⟨.B, g + 5 + 2 * m⟩ :: ⟨.M, g + 9 + 2 * m + 2 * j⟩ :: msR) W)
      = some (midCfg (⟨.W, g + 4 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 9 + 2 * m + 2 * j) msR W) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hb
  have hR := build_free msR (g + 9 + 2 * m + 2 * j + 2) W hf
  have hstart : midCfg msL g (⟨.B, g + 5 + 2 * m⟩ :: ⟨.M, g + 9 + 2 * m + 2 * j⟩ :: msR) W
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 5 + 2 * m - (g + 3)) (cons true (cons true (cons true
           (stripe false (g + 9 + 2 * m + 2 * j - (g + 5 + 2 * m + 3)) (cons true (cons true
             (build true (g + 9 + 2 * m + 2 * j + 2) msR W)))))))), .E⟩ := rfl
  have hend : midCfg (⟨.W, g + 4 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 9 + 2 * m + 2 * j) msR W
      = ⟨cons false (cons false (stripe true (g + 9 + 2 * m + 2 * j - (g + 4 + 2 * m + 2)) (cons false (cons false
           (stripe true (g + 4 + 2 * m - (g + 3)) (cons false (cons false (cons false (buildL false g msL))))))))),
         cons false (build false (g + 9 + 2 * m + 2 * j + 2 + 1) msR W), .E⟩ := rfl
  have e₁ : g + 5 + 2 * m - (g + 3) = 2 * (m + 1) := by omega
  have e₂ : g + 9 + 2 * m + 2 * j - (g + 5 + 2 * m + 3) = 2 * j + 1 := by omega
  have e₃ : g + 9 + 2 * m + 2 * j - (g + 4 + 2 * m + 2) = 2 * (j + 1) + 1 := by omega
  have e₄ : g + 4 + 2 * m - (g + 3) = 2 * m + 1 := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_even, Bool.not_true, e₂, stripe_false_odd', hR]
  conv at hend => rhs; rw [e₃, stripe_true_odd, e₄, stripe_true_odd, hL1,
    rep_cons2 m true false (cons false (cons false (cons true L'))),
    rep_cons2 (j + 1) true false (cons false (rep (m + 1) [true, false] (cons false (cons false (cons true L')))))]
  rw [hstart, hend]
  have h := block_to_marker j (m + 1) L' (build false (g + 9 + 2 * m + 2 * j + 2 + 1) msR W)
  rw [rep_two j (cons false (rep (m + 1) [true, false] (cons false (cons false (cons true L')))))] at h
  exact h

/-- Gap meets block, shift meets wall; general contact before the gap. -/
theorem ev_gap_block_wall' (msL msR : List Mark) (g m j W : Nat) (hb : oneBefore g msL)
    (ha : strictAfter (g + 8 + 2 * m + 2 * j + 2) W msR) :
    steps (6 * j + 2 * (m + 1) + 17)
        (midCfg msL g (⟨.B, g + 5 + 2 * m⟩ :: ⟨.W, g + 8 + 2 * m + 2 * j⟩ :: msR) W)
      = some (midCfg (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m) (⟨.B, g + 8 + 2 * m + 2 * j⟩ :: msR) W) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hb
  have hR := build_step msR false (g + 8 + 2 * m + 2 * j + 2) W ha
  rw [Bool.not_false] at hR
  have hstart : midCfg msL g (⟨.B, g + 5 + 2 * m⟩ :: ⟨.W, g + 8 + 2 * m + 2 * j⟩ :: msR) W
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 5 + 2 * m - (g + 3)) (cons true (cons true (cons true
           (stripe false (g + 8 + 2 * m + 2 * j - (g + 5 + 2 * m + 3)) (cons false (cons false
             (build false (g + 8 + 2 * m + 2 * j + 2) msR W)))))))), .E⟩ := rfl
  have hend : midCfg (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m) (⟨.B, g + 8 + 2 * m + 2 * j⟩ :: msR) W
      = ⟨cons false (cons false (buildL false (g + 5 + 2 * m) (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL))),
         cons false (stripe true (g + 8 + 2 * m + 2 * j - (g + 5 + 2 * m + 3)) (cons true (cons true (cons true
           (build true (g + 8 + 2 * m + 2 * j + 2 + 1) msR W))))), .E⟩ := rfl
  have e₁ : g + 5 + 2 * m - (g + 3) = 2 * (m + 1) := by omega
  have e₂ : g + 8 + 2 * m + 2 * j - (g + 5 + 2 * m + 3) = 2 * j := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_even, Bool.not_true, e₂, stripe_even, Bool.not_false, hR]
  conv at hend => rhs; rw [buildL_woken msL g m L' hL1, e₂, stripe_even, Bool.not_true]
  rw [hstart, hend]
  have h := block_to_wall j (m + 1) L' (build true (g + 8 + 2 * m + 2 * j + 2 + 1) msR W)
  rw [rep_shift' false true j (cons false (cons true (build true (g + 8 + 2 * m + 2 * j + 2 + 1) msR W)))] at h
  exact h

/-- Gap meets block, shift meets a second block; general contact before the gap. -/
theorem ev_gap_block_block' (msL msR : List Mark) (g m j W : Nat) (hb : oneBefore g msL)
    (hf : freeAt (g + 9 + 2 * m + 2 * j + 3) W msR) :
    steps (6 * j + 2 * (m + 1) + 23)
        (midCfg msL g (⟨.B, g + 5 + 2 * m⟩ :: ⟨.B, g + 9 + 2 * m + 2 * j⟩ :: msR) W)
      = some (midCfg (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m) (⟨.W, g + 9 + 2 * m + 2 * j + 2⟩ :: msR) W) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hb
  have hR := build_free msR (g + 9 + 2 * m + 2 * j + 3) W hf
  have hstart : midCfg msL g (⟨.B, g + 5 + 2 * m⟩ :: ⟨.B, g + 9 + 2 * m + 2 * j⟩ :: msR) W
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 5 + 2 * m - (g + 3)) (cons true (cons true (cons true
           (stripe false (g + 9 + 2 * m + 2 * j - (g + 5 + 2 * m + 3)) (cons true (cons true (cons true
             (build true (g + 9 + 2 * m + 2 * j + 3) msR W))))))))), .E⟩ := rfl
  have hend : midCfg (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m) (⟨.W, g + 9 + 2 * m + 2 * j + 2⟩ :: msR) W
      = ⟨cons false (cons false (buildL false (g + 5 + 2 * m) (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL))),
         cons false (stripe true (g + 9 + 2 * m + 2 * j + 2 - (g + 5 + 2 * m + 3)) (cons false (cons false
           (build false (g + 9 + 2 * m + 2 * j + 3 + 1) msR W)))), .E⟩ := rfl
  have e₁ : g + 5 + 2 * m - (g + 3) = 2 * (m + 1) := by omega
  have e₂ : g + 9 + 2 * m + 2 * j - (g + 5 + 2 * m + 3) = 2 * j + 1 := by omega
  have e₃ : g + 9 + 2 * m + 2 * j + 2 - (g + 5 + 2 * m + 3) = 2 * (j + 1) + 1 := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_even, Bool.not_true, e₂, stripe_false_odd', hR]
  conv at hend => rhs; rw [buildL_woken msL g m L' hL1, e₃, stripe_true_odd]
  rw [hstart, hend]
  have h := block_to_block j (m + 1) L' (build false (g + 9 + 2 * m + 2 * j + 3 + 1) msR W)
  rw [rep_cons2 j true false (cons true (cons false (cons false (build false (g + 9 + 2 * m + 2 * j + 3 + 1) msR W))))] at h
  exact h

/-- Gap meets block, shift reaches blank tape; general contact before the gap. -/
theorem ev_gap_block_blank' (msL : List Mark) (g m j : Nat) (hb : oneBefore g msL) :
    steps (6 * j + 2 * (m + 1) + 17) (midCfg msL g [⟨.B, g + 5 + 2 * m⟩] (g + 8 + 2 * m + 2 * j))
      = some (midCfg (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m) [⟨.M, g + 8 + 2 * m + 2 * j⟩]
          (g + 10 + 2 * m + 2 * j)) := by
  obtain ⟨L', hL1⟩ := oneBefore_tail hb
  have hstart : midCfg msL g [⟨.B, g + 5 + 2 * m⟩] (g + 8 + 2 * m + 2 * j)
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 5 + 2 * m - (g + 3)) (cons true (cons true (cons true
           (stripe false (g + 8 + 2 * m + 2 * j - (g + 5 + 2 * m + 3)) blank))))), .E⟩ := rfl
  have hend : midCfg (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m) [⟨.M, g + 8 + 2 * m + 2 * j⟩]
          (g + 10 + 2 * m + 2 * j)
      = ⟨cons false (cons false (buildL false (g + 5 + 2 * m) (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL))),
         cons false (stripe true (g + 8 + 2 * m + 2 * j - (g + 5 + 2 * m + 3)) (cons true (cons true
           (stripe false (g + 10 + 2 * m + 2 * j - (g + 8 + 2 * m + 2 * j + 2)) blank)))), .E⟩ := rfl
  have e₁ : g + 5 + 2 * m - (g + 3) = 2 * (m + 1) := by omega
  have e₂ : g + 8 + 2 * m + 2 * j - (g + 5 + 2 * m + 3) = 2 * j := by omega
  have e₃ : g + 10 + 2 * m + 2 * j - (g + 8 + 2 * m + 2 * j + 2) = 0 := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_even, Bool.not_true, e₂, stripe_even, Bool.not_false]
  conv at hend => rhs; rw [buildL_woken msL g m L' hL1, e₂, stripe_even, Bool.not_true, e₃, stripe_zero]
  rw [hstart, hend]
  have h := block_to_blank j (m + 1) L'
  rw [rep_shift' false true j blank, cons_false_blank] at h
  exact h

/-- The packet reaches a block; general contact before the block (a 0-mark may touch it). -/
theorem ev_pkt_block' (msL msR : List Mark) (r j W : Nat) (hb : zeroBefore r msL) :
    steps (4 * (j + 1) + 4 + 1) (pktCfg (⟨.B, r⟩ :: msL) (r + 3 + (2 * j + 1)) msR W) = none := by
  obtain ⟨L', hL⟩ := zeroBefore_tail hb
  have hstart : pktCfg (⟨.B, r⟩ :: msL) (r + 3 + (2 * j + 1)) msR W
      = ⟨stripe false (r + 3 + (2 * j + 1) - (r + 3)) (cons true (cons true (cons true (buildL true r msL)))),
         cons true (cons true (build false (r + 3 + (2 * j + 1) + 2) msR W)), .A⟩ := rfl
  have e₁ : r + 3 + (2 * j + 1) - (r + 3) = 2 * j + 1 := by omega
  conv at hstart => rhs; rw [e₁, stripe_two_add, Bool.not_false, stripe_succ, Bool.not_false, stripe_zero, hL,
    rep_cons2 j false true]
  rw [hstart]
  have h₁ := carry (j + 1) (cons true (cons true (cons false L'))) (build false (r + 3 + (2 * j + 1) + 2) msR W)
  obtain ⟨h₂, h₃⟩ := packet_to_block L' (rep (j + 1) [true, false] (build false (r + 3 + (2 * j + 1) + 2) msR W))
  have h := steps_halt (steps_seq h₁ h₂) h₃ 0
  simpa using h

end BB6
