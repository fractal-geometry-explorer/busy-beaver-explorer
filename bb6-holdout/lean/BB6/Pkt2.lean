import BB6.Pkt

/-!
# The packet phase, continued: the packet stops

* at a wall (`ev_pkt_wall`): the wall becomes a marker one cell left and a gap wakes one cell right;
* at the left end (`ev_pkt_leftend`): a new round, every position shifted by 2;
* at the left end with a marker on cell 0 (`ev_pkt_leftend_marker`): the marker becomes the wall `W 5`, shift by 4;
* at a block (`ev_pkt_block`): the machine halts.
-/

namespace BB6

/-- Shift every mark right by `s`. -/
def shiftMarks (s : Nat) (ms : List Mark) : List Mark := ms.map (fun m => ⟨m.t, m.p + s⟩)

theorem build_shiftMarks (ms : List Mark) (b : Bool) (q W s : Nat) :
    build b (q + s) (shiftMarks s ms) (W + s) = build b q ms W := by
  induction ms generalizing b q with
  | nil =>
    show stripe (!b) (W + s - (q + s)) blank = stripe (!b) (W - q) blank
    rw [Nat.add_sub_add_right]
  | cons m ms ih =>
    show stripe (!b) (m.p + s - (q + s)) (app (mcells m.t) (build (mval m.t) (m.p + s + mlen m.t) (shiftMarks s ms) (W + s)))
      = stripe (!b) (m.p - q) (app (mcells m.t) (build (mval m.t) (m.p + mlen m.t) ms W))
    have e : m.p + s + mlen m.t = m.p + mlen m.t + s := by omega
    rw [Nat.add_sub_add_right, e, ih]

/-- The packet reaches a wall at `w`, 2j stripe cells to its left, with a stripe cell before the wall: the wall
becomes a marker at w − 1 and the gap wakes at w + 1; 4j + 7 steps. -/
theorem ev_pkt_wall (msL msR : List Mark) (w j W : Nat) (hb : stripeBefore w msL) (hs : startsAt (w + 2 + 2 * j + 2) W msR) :
    steps (4 * j + 7) (pktCfg (⟨.W, w⟩ :: msL) (w + 2 + 2 * j) msR W)
      = some (midCfg (⟨.M, w - 1⟩ :: msL) (w + 1) msR W) := by
  have hw : 1 ≤ w := by cases msL <;> simp only [stripeBefore] at hb <;> omega
  obtain ⟨L', hL1, hL2⟩ := buildL_shift msL w hb 0
  have hL2' : buildL true (w - 1) msL = L' := by simpa using hL2
  have hstart : pktCfg (⟨.W, w⟩ :: msL) (w + 2 + 2 * j) msR W
      = ⟨stripe false (w + 2 + 2 * j - (w + 2)) (cons false (cons false (buildL false w msL))),
         cons true (cons true (build false (w + 2 + 2 * j + 2) msR W)), .A⟩ := rfl
  have hend : midCfg (⟨.M, w - 1⟩ :: msL) (w + 1) msR W
      = ⟨cons false (cons false (stripe true (w + 1 - (w - 1 + 2)) (cons true (cons true (buildL true (w - 1) msL))))),
         cons false (build false (w + 1 + 3) msR W), .E⟩ := rfl
  have e₁ : w + 2 + 2 * j - (w + 2) = 2 * j := by omega
  have e₂ : w + 1 - (w - 1 + 2) = 0 := by omega
  have e₃ : w + 1 + 3 = w + 2 + 2 * j + 2 - 2 * j := by omega
  have heven := build_even msR false (w + 2 + 2 * j + 2) W j hs (by omega)
  rw [Bool.not_false] at heven
  conv at hstart => rhs; rw [e₁, stripe_even, Bool.not_false, hL1]
  conv at hend => rhs; rw [e₂, stripe_zero, hL2', e₃, heven]
  rw [hstart, hend]
  have h₁ := carry j (cons false (cons false (cons true L'))) (build false (w + 2 + 2 * j + 2) msR W)
  have h₂ := packet_to_wall L' (rep j [true, false] (build false (w + 2 + 2 * j + 2) msR W))
  exact steps_seq h₁ h₂

/-- The packet reaches the left end: the packet at 2j with nothing but stripe to its left.  A new round starts, every
mark 2 cells further right and the width 2 larger; 4j + 7 steps. -/
theorem ev_pkt_leftend (msR : List Mark) (j W : Nat) (hs : startsAt (2 * j + 2) W msR) :
    steps (4 * j + 7) (pktCfg [] (2 * j) msR W) = some (roundStart (shiftMarks 2 msR) (W + 2)) := by
  have hstart : pktCfg [] (2 * j) msR W
      = ⟨stripe false (2 * j) blank, cons true (cons true (build false (2 * j + 2) msR W)), .A⟩ := rfl
  have hend : roundStart (shiftMarks 2 msR) (W + 2)
      = ⟨cons false (cons false (cons true blank)), cons false (build false (2 + 2) (shiftMarks 2 msR) (W + 2)), .E⟩ := rfl
  have heven := build_even msR false (2 * j + 2) W j hs (by omega)
  rw [Bool.not_false] at heven
  have e : 2 * j + 2 - 2 * j = 2 := by omega
  rw [e] at heven
  conv at hstart => rhs; rw [stripe_even, Bool.not_false]
  conv at hend => rhs; rw [build_shiftMarks msR false 2 W 2, heven]
  rw [hstart, hend]
  have h₁ := carry j blank (build false (2 * j + 2) msR W)
  have h₂ := packet_to_leftend (rep j [true, false] (build false (2 * j + 2) msR W))
  exact steps_seq h₁ h₂

/-- The packet reaches the left end with a marker on cells 0, 1 and 2j + 1 stripe cells between: the marker becomes
the wall at 5 of the new round, every other mark moves 4 cells right, the width grows by 4; 4(j + 1) + 18 steps. -/
theorem ev_pkt_leftend_marker (msR : List Mark) (j W : Nat) (hs : startsAt (2 + (2 * j + 1) + 2) W msR) :
    steps (4 * (j + 1) + 18) (pktCfg [⟨.M, 0⟩] (2 + (2 * j + 1)) msR W)
      = some (roundStart (⟨.W, 5⟩ :: shiftMarks 4 msR) (W + 4)) := by
  have hstart : pktCfg [⟨.M, 0⟩] (2 + (2 * j + 1)) msR W
      = ⟨stripe false (2 + (2 * j + 1) - 2) (cons true (cons true (stripe false 0 blank))),
         cons true (cons true (build false (2 + (2 * j + 1) + 2) msR W)), .A⟩ := rfl
  have hend : roundStart (⟨.W, 5⟩ :: shiftMarks 4 msR) (W + 4)
      = ⟨cons false (cons false (cons true blank)),
         cons false (stripe true (5 - 4) (cons false (cons false (build false (5 + 2) (shiftMarks 4 msR) (W + 4))))), .E⟩ := rfl
  have heven := build_even msR false (2 + (2 * j + 1) + 2) W (j + 1) hs (by omega)
  rw [Bool.not_false] at heven
  have e₁ : 2 + (2 * j + 1) - 2 = 2 * j + 1 := by omega
  have e₂ : 2 + (2 * j + 1) + 2 - 2 * (j + 1) = 3 := by omega
  rw [e₂] at heven
  have e₃ : 5 + 2 = 3 + 4 := by omega
  conv at hstart => rhs; rw [e₁, stripe_two_add, Bool.not_false, stripe_succ, Bool.not_false, stripe_zero, stripe_zero,
    rep_cons2 j false true]
  conv at hend => rhs; rw [e₃, build_shiftMarks msR false 3 W 4, heven]
  rw [hstart, hend]
  have h₁ := carry (j + 1) (cons true blank) (build false (2 + (2 * j + 1) + 2) msR W)
  have h₂ := packet_to_leftend_marker (rep (j + 1) [true, false] (build false (2 + (2 * j + 1) + 2) msR W))
  have h := steps_seq h₁ h₂
  exact h

/-- The packet reaches a block at `r`, 2j + 1 stripe cells to its left, with a stripe cell before the block: the
machine halts after 4(j + 1) + 4 more steps. -/
theorem ev_pkt_block (msL msR : List Mark) (r j W : Nat) (hb : stripeBefore r msL) :
    steps (4 * (j + 1) + 4 + 1) (pktCfg (⟨.B, r⟩ :: msL) (r + 3 + (2 * j + 1)) msR W) = none := by
  have hr : 1 ≤ r := by cases msL <;> simp only [stripeBefore] at hb <;> omega
  -- the cell before the block is a 0: the stripe before a 1-mark ends with 0
  have hL : ∃ L', buildL true r msL = cons false L' := by
    cases msL with
    | nil =>
      simp only [stripeBefore] at hb
      obtain ⟨n, hn⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
      subst hn
      exact ⟨stripe true n blank, rfl⟩
    | cons m ms =>
      simp only [stripeBefore] at hb
      obtain ⟨n, hn⟩ : ∃ n, r - (m.p + mlen m.t) = n + 1 := ⟨r - (m.p + mlen m.t) - 1, by omega⟩
      refine ⟨stripe true n (app (mcells m.t).reverse (buildL (mval m.t) m.p ms)), ?_⟩
      show stripe (!true) (r - (m.p + mlen m.t)) _ = _
      rw [hn]
      rfl
  obtain ⟨L', hL⟩ := hL
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
