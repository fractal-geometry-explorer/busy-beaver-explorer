import BB6.Mid

/-!
# The packet phase at the level of positions

A packet at `x` (`pktCfg msL x msR W`) travels left: over a stripe by CARRY, across a marker by PACKET→marker, and
stops at the first mark that is not a marker — a sleeping gap (PACKET→gap: the gap wakes two cells to the right), a
wall (PACKET→wall: the wall becomes a marker with a gap after it), or the left end (a new round).

Two more facts about the tape builder: moving the start point of `build` left by an even number of cells prepends
that many stripe cells as repeats of a pair (`build_even`), and by an odd number flips the parity and prepends one
cell and repeats (`build_odd`).
-/

namespace BB6

/-- The tape from `q` on is a stripe up to the first mark (or to the width): nothing starts before `q`. -/
def startsAt (q W : Nat) : List Mark → Prop
  | [] => q ≤ W
  | m :: _ => q ≤ m.p

theorem build_even (msR : List Mark) (b : Bool) (q W j : Nat) (h : startsAt q W msR) (hq : 2 * j ≤ q) :
    build b (q - 2 * j) msR W = rep j [!b, b] (build b q msR W) := by
  cases msR with
  | nil =>
    simp only [startsAt] at h
    have e : W - (q - 2 * j) = 2 * j + (W - q) := by omega
    show stripe (!b) (W - (q - 2 * j)) blank = _
    rw [e, stripe_two_add, Bool.not_not]
    rfl
  | cons m ms =>
    simp only [startsAt] at h
    have e : m.p - (q - 2 * j) = 2 * j + (m.p - q) := by omega
    show stripe (!b) (m.p - (q - 2 * j)) _ = _
    rw [e, stripe_two_add, Bool.not_not]
    rfl

theorem build_odd (msR : List Mark) (b : Bool) (q W j : Nat) (h : startsAt q W msR) (hq : 2 * j + 1 ≤ q) :
    build (!b) (q - (2 * j + 1)) msR W = cons b (rep j [!b, b] (build b q msR W)) := by
  cases msR with
  | nil =>
    simp only [startsAt] at h
    have e : W - (q - (2 * j + 1)) = (2 * j + (W - q)) + 1 := by omega
    show stripe (!!b) (W - (q - (2 * j + 1))) blank = _
    rw [e, stripe_succ, Bool.not_not, stripe_two_add, Bool.not_not]
    rfl
  | cons m ms =>
    simp only [startsAt] at h
    have e : m.p - (q - (2 * j + 1)) = (2 * j + (m.p - q)) + 1 := by omega
    show stripe (!!b) (m.p - (q - (2 * j + 1))) _ = _
    rw [e, stripe_succ, Bool.not_not, stripe_two_add, Bool.not_not]
    rfl

/-- At least two stripe cells before `y` (a marker there is preceded by an even, nonempty stripe). -/
def stripeBefore2 (y : Nat) : List Mark → Prop
  | [] => 2 ≤ y
  | m :: _ => m.p + mlen m.t + 2 ≤ y

theorem buildL_two (msL : List Mark) (y : Nat) (h : stripeBefore2 y msL) :
    buildL true y msL = cons false (cons true (buildL true (y - 2) msL)) := by
  cases msL with
  | nil =>
    simp only [stripeBefore2] at h
    have e : y = (y - 2) + 1 + 1 := by omega
    show stripe (!true) y blank = _
    conv => lhs; rw [e]
    rfl
  | cons m ms =>
    simp only [stripeBefore2] at h
    have e : y - (m.p + mlen m.t) = (y - 2 - (m.p + mlen m.t)) + 1 + 1 := by omega
    show stripe (!true) (y - (m.p + mlen m.t)) _ = _
    rw [e]
    rfl

/-- The packet crosses a marker at `y`, 2j + 1 stripe cells to its left: the marker stays, the packet moves to
y − 2; 4(j + 1) + 5 steps. -/
theorem ev_pkt_marker (msL msR : List Mark) (y j W : Nat) (hb : stripeBefore2 y msL)
    (hs : startsAt (y + 2 + (2 * j + 1) + 2) W msR) :
    steps (4 * (j + 1) + 5) (pktCfg (⟨.M, y⟩ :: msL) (y + 2 + (2 * j + 1)) msR W)
      = some (pktCfg msL (y - 2) (⟨.M, y⟩ :: msR) W) := by
  have hstart : pktCfg (⟨.M, y⟩ :: msL) (y + 2 + (2 * j + 1)) msR W
      = ⟨stripe false (y + 2 + (2 * j + 1) - (y + 2)) (cons true (cons true (buildL true y msL))),
         cons true (cons true (build false (y + 2 + (2 * j + 1) + 2) msR W)), .A⟩ := rfl
  have hend : pktCfg msL (y - 2) (⟨.M, y⟩ :: msR) W
      = ⟨buildL true (y - 2) msL,
         cons true (cons true (stripe true (y - (y - 2 + 2)) (cons true (cons true (build true (y + 2) msR W))))), .A⟩ := rfl
  have hy : 2 ≤ y := by cases msL <;> simp only [stripeBefore2] at hb <;> omega
  have e₁ : y + 2 + (2 * j + 1) - (y + 2) = 2 * j + 1 := by omega
  have e₂ : y - (y - 2 + 2) = 0 := by omega
  have e₃ : y + 2 = y + 2 + (2 * j + 1) + 2 - (2 * j + 3) := by omega
  have hodd := build_odd msR false (y + 2 + (2 * j + 1) + 2) W (j + 1) hs (by omega)
  rw [Bool.not_false] at hodd
  have e₄ : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
  rw [e₄] at hodd
  conv at hstart => rhs; rw [e₁, stripe_two_add, Bool.not_false, stripe_succ, Bool.not_false, stripe_zero,
    rep_cons2 j false true, buildL_two msL y hb]
  conv at hend => rhs; rw [e₂, stripe_zero, e₃, hodd]
  rw [hstart, hend]
  have h₁ := carry (j + 1) (cons true (cons false (cons true (buildL true (y - 2) msL)))) (build false (y + 2 + (2 * j + 1) + 2) msR W)
  have h₂ := packet_to_marker (buildL true (y - 2) msL) (rep (j + 1) [true, false] (build false (y + 2 + (2 * j + 1) + 2) msR W))
  exact steps_seq h₁ h₂

/-- The marks left of `g` end at or before `g`. -/
def endsBy (g : Nat) : List Mark → Prop
  | [] => True
  | m :: _ => m.p + mlen m.t ≤ g

/-- The stripe left of a point grows by two cells when the point moves right by two (same value at the point). -/
theorem buildL_add_two (msL : List Mark) (b : Bool) (g : Nat) (h : endsBy g msL) :
    buildL b (g + 2) msL = cons (!b) (cons b (buildL b g msL)) := by
  cases msL with
  | nil =>
    show stripe (!b) (g + 1 + 1) blank = _
    rw [stripe_succ, stripe_succ, Bool.not_not]
    rfl
  | cons m ms =>
    simp only [endsBy] at h
    have e : g + 2 - (m.p + mlen m.t) = (g - (m.p + mlen m.t)) + 1 + 1 := by omega
    show stripe (!b) (g + 2 - (m.p + mlen m.t)) _ = _
    rw [e, stripe_succ, stripe_succ, Bool.not_not]
    rfl

/-- The packet reaches a sleeping gap at `g`, 2j stripe cells to its left: the gap wakes at g + 2 with the head on
its last cell; 4j + 7 steps. -/
theorem ev_pkt_gap (msL msR : List Mark) (g j W : Nat) (hb : endsBy g msL) (hs : startsAt (g + 3 + 2 * j + 2) W msR) :
    steps (4 * j + 7) (pktCfg (⟨.G, g⟩ :: msL) (g + 3 + 2 * j) msR W)
      = some (midCfg msL (g + 2) msR W) := by
  have hstart : pktCfg (⟨.G, g⟩ :: msL) (g + 3 + 2 * j) msR W
      = ⟨stripe false (g + 3 + 2 * j - (g + 3)) (cons false (cons false (cons false (buildL false g msL)))),
         cons true (cons true (build false (g + 3 + 2 * j + 2) msR W)), .A⟩ := rfl
  have hend : midCfg msL (g + 2) msR W
      = ⟨cons false (cons false (buildL false (g + 2) msL)), cons false (build false (g + 2 + 3) msR W), .E⟩ := rfl
  have e₁ : g + 3 + 2 * j - (g + 3) = 2 * j := by omega
  have e₂ : g + 2 + 3 = g + 3 + 2 * j + 2 - 2 * j := by omega
  have heven := build_even msR false (g + 3 + 2 * j + 2) W j hs (by omega)
  rw [Bool.not_false] at heven
  have hL := buildL_add_two msL false g hb
  rw [Bool.not_false] at hL
  conv at hstart => rhs; rw [e₁, stripe_even, Bool.not_false]
  conv at hend => rhs; rw [hL, e₂, heven]
  rw [hstart, hend]
  have h₁ := carry j (cons false (cons false (cons false (buildL false g msL)))) (build false (g + 3 + 2 * j + 2) msR W)
  have h₂ := packet_to_gap (buildL false g msL) (rep j [true, false] (build false (g + 3 + 2 * j + 2) msR W))
  exact steps_seq h₁ h₂

end BB6
