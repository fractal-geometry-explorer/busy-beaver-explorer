import BB6.Events

/-!
# The packet phase as a whole

A packet travelling left crosses markers and stops at the first mark that is not a marker, or at the left end.
`pktBack msL x msR W` is the mark model's answer (the zipper form of `Model.packetBack`), and `pktBack_run` is the
theorem that the machine, started in `pktCfg msL x msR W`, reaches the configuration that answer denotes.

Crossing a marker at `y` goes through a configuration that no mark state denotes: after the carry the packet sits
on the marker's second cell, `pktCfgM msL y msR W`.  From there the PACKET→marker rule moves it to y − 2 — onto the
last cell of a 1-mark one stripe cell before the marker, if there is one, which is again such a configuration.  So
the crossing is handled by `pktLand`, which reads the mark before the marker and either lands the packet in a proper
`pktCfg` (two or more stripe cells before the marker), continues into the next marker, halts at a block, or
finishes the round at the left-end marker.

Well-formedness of the two sides of a configuration, `leftOK p v msL` (the marks left of a point `p` whose cell reads
`v`, nearest first) and `rightOK q u W msR` (the marks from `q` on, the cell before `q` reading `u`, up to the width
`W`), records the order of the marks and the parity of every stripe — including the width's: the cell W − 1 is a 1.
-/

namespace BB6

/-- The marks left of `p`, nearest first, when the cell at `p` reads `v`: each mark ends at or before the point
after it, with a stripe of the right parity between (odd between cells of equal value, even otherwise), and the
leftmost stripe reaches cell 0 with a 1 there. -/
def leftOK (p : Nat) (v : Bool) : List Mark → Prop
  | [] => (p % 2 = 1 ↔ v = false)
  | m :: ms => m.p + mlen m.t ≤ p ∧ ((p - (m.p + mlen m.t)) % 2 = 1 ↔ v = mval m.t) ∧ leftOK m.p (mval m.t) ms

/-- The marks from `q` on, when the cell q − 1 reads `u`: each starts at or after the point before it, with a stripe
of the right parity between, and the last stripe ends with a 1 at W − 1. -/
def rightOK (q : Nat) (u : Bool) (W : Nat) : List Mark → Prop
  | [] => q ≤ W ∧ ((W - q) % 2 = 1 ↔ u = false)
  | m :: ms => q ≤ m.p ∧ ((m.p - q) % 2 = 1 ↔ u = mval m.t) ∧ rightOK (m.p + mlen m.t) (mval m.t) W ms

theorem rightOK_startsAt {q : Nat} {u : Bool} {W : Nat} {msR : List Mark} (h : rightOK q u W msR) : startsAt q W msR := by
  cases msR <;> simp only [rightOK, startsAt] at h ⊢ <;> omega

theorem rightOK_freeAt {q : Nat} {u : Bool} {W : Nat} {msR : List Mark} (h : rightOK (q + 1) u W msR) : freeAt q W msR := by
  cases msR <;> simp only [rightOK, freeAt] at h ⊢ <;> omega

/-- One cell to the left, the cell before it read the other way. -/
theorem rightOK_pred {q : Nat} {u : Bool} {W : Nat} {msR : List Mark} (h : rightOK (q + 1) u W msR) :
    rightOK q (!u) W msR := by
  cases msR with
  | nil =>
    simp only [rightOK] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨by omega, ?_⟩
    cases u <;> simp at h2 ⊢ <;> omega
  | cons m ms =>
    simp only [rightOK] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by omega, ?_, h3⟩
    cases u <;> cases hv : mval m.t <;> simp [hv] at h2 ⊢ <;> omega

/-- Two cells to the left. -/
theorem rightOK_pred2 {q : Nat} {u : Bool} {W : Nat} {msR : List Mark} (h : rightOK (q + 2) u W msR) :
    rightOK q u W msR := by
  have := rightOK_pred (rightOK_pred h)
  simpa using this

/-- One cell to the right, when that cell is a stripe cell (strictly before the next mark). -/
theorem rightOK_succ {q : Nat} {u : Bool} {W : Nat} {msR : List Mark} (h : rightOK q u W msR)
    (hs : strictAfter q W msR) : rightOK (q + 1) (!u) W msR := by
  cases msR with
  | nil =>
    simp only [rightOK, strictAfter] at h hs ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨by omega, ?_⟩
    cases u <;> simp at h2 ⊢ <;> omega
  | cons m ms =>
    simp only [rightOK, strictAfter] at h hs ⊢
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by omega, ?_, h3⟩
    cases u <;> cases hv : mval m.t <;> simp [hv] at h2 ⊢ <;> omega

theorem leftOK_endsBy {p : Nat} {v : Bool} {msL : List Mark} (h : leftOK p v msL) : endsBy p msL := by
  cases msL <;> simp only [leftOK, endsBy] at h ⊢; exact h.1

/-- One cell to the right (the cell at p being a stripe cell). -/
theorem leftOK_succ {p : Nat} {v : Bool} {msL : List Mark} (h : leftOK p v msL) : leftOK (p + 1) (!v) msL := by
  cases msL with
  | nil =>
    simp only [leftOK] at h ⊢
    cases v <;> simp at h ⊢ <;> omega
  | cons m ms =>
    simp only [leftOK] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by omega, ?_, h3⟩
    cases v <;> cases hv : mval m.t <;> simp [hv] at h2 ⊢ <;> omega

/-- One cell to the left, when that cell is a stripe cell (the first mark ends before p). -/
theorem leftOK_pred {p : Nat} {v : Bool} {msL : List Mark} (h : leftOK (p + 1) v msL) (hs : endsBy p msL) :
    leftOK p (!v) msL := by
  cases msL with
  | nil =>
    simp only [leftOK] at h ⊢
    cases v <;> simp at h ⊢ <;> omega
  | cons m ms =>
    simp only [leftOK, endsBy] at h hs ⊢
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by omega, ?_, h3⟩
    cases v <;> cases hv : mval m.t <;> simp [hv] at h2 ⊢ <;> omega

theorem leftOK_add2 {p : Nat} {v : Bool} {msL : List Mark} (h : leftOK p v msL) : leftOK (p + 2) v msL := by
  have := leftOK_succ (leftOK_succ h)
  simpa using this

/-- The configuration after the packet has carried up to the marker at `y`: the marker's first cell, the packet on
the marker's second cell and the one after. -/
def pktCfgM (msL : List Mark) (y : Nat) (msR : List Mark) (W : Nat) : Cfg :=
  ⟨cons true (buildL true y msL), cons true (cons true (build false (y + 3) msR W)), .A⟩

/-- Carrying up to the marker at y from y + 3 + 2j. -/
theorem pkt_carry (msL msR : List Mark) (y j W : Nat) (hs : startsAt (y + 5 + 2 * j) W msR) :
    steps (4 * (j + 1)) (pktCfg (⟨.M, y⟩ :: msL) (y + 3 + 2 * j) msR W) = some (pktCfgM msL y msR W) := by
  have hstart : pktCfg (⟨.M, y⟩ :: msL) (y + 3 + 2 * j) msR W
      = ⟨stripe false (y + 3 + 2 * j - (y + 2)) (cons true (cons true (buildL true y msL))),
         cons true (cons true (build false (y + 3 + 2 * j + 2) msR W)), .A⟩ := rfl
  have e₁ : y + 3 + 2 * j - (y + 2) = 2 * j + 1 := by omega
  have e₃ : y + 3 + 2 * j + 2 = y + 5 + 2 * j := by omega
  have e₂ : y + 3 = y + 5 + 2 * j - 2 * (j + 1) := by omega
  have heven := build_even msR false (y + 5 + 2 * j) W (j + 1) hs (by omega)
  rw [Bool.not_false] at heven
  have hend : pktCfgM msL y msR W
      = ⟨cons true (buildL true y msL), cons true (cons true (build false (y + 3) msR W)), .A⟩ := rfl
  conv at hstart => rhs; rw [e₁, stripe_false_odd, rep_cons2 j false true (cons true (buildL true y msL)), e₃]
  conv at hend => rhs; rw [e₂, heven]
  rw [hstart, hend]
  exact carry (j + 1) (cons true (buildL true y msL)) (build false (y + 5 + 2 * j) msR W)

/-- The standard landing: two or more stripe cells before the marker; the packet lands at y − 2. -/
theorem pkt_land_std (msL msR : List Mark) (y W : Nat) (hb : stripeBefore2 y msL) (hf : freeAt (y + 2) W msR) :
    steps 5 (pktCfgM msL y msR W) = some (pktCfg msL (y - 2) (⟨.M, y⟩ :: msR) W) := by
  have hstart : pktCfgM msL y msR W
      = ⟨cons true (buildL true y msL), cons true (cons true (build false (y + 3) msR W)), .A⟩ := rfl
  have hend : pktCfg msL (y - 2) (⟨.M, y⟩ :: msR) W
      = ⟨buildL true (y - 2) msL, cons true (cons true (stripe true (y - (y - 2 + 2)) (cons true (cons true
          (build true (y + 2) msR W))))), .A⟩ := rfl
  have hy : 2 ≤ y := by cases msL <;> simp only [stripeBefore2] at hb <;> omega
  have e : y - (y - 2 + 2) = 0 := by omega
  conv at hstart => rhs; rw [buildL_two msL y hb]
  conv at hend => rhs; rw [e, stripe_zero, build_free msR (y + 2) W hf]
  rw [hstart, hend]
  exact packet_to_marker (buildL true (y - 2) msL) (build false (y + 2 + 1) msR W)

/-- The marker sits one stripe cell after another marker: the packet lands on that marker's second cell. -/
theorem pkt_land_next (msL msR : List Mark) (y' W : Nat) (hf : freeAt (y' + 3 + 2) W msR) :
    steps 5 (pktCfgM (⟨.M, y'⟩ :: msL) (y' + 3) msR W) = some (pktCfgM msL y' (⟨.M, y' + 3⟩ :: msR) W) := by
  have hstart : pktCfgM (⟨.M, y'⟩ :: msL) (y' + 3) msR W
      = ⟨cons true (stripe false (y' + 3 - (y' + 2)) (cons true (cons true (buildL true y' msL)))),
         cons true (cons true (build false (y' + 3 + 3) msR W)), .A⟩ := rfl
  have hend : pktCfgM msL y' (⟨.M, y' + 3⟩ :: msR) W
      = ⟨cons true (buildL true y' msL), cons true (cons true (stripe true (y' + 3 - (y' + 3)) (cons true (cons true
          (build true (y' + 3 + 2) msR W))))), .A⟩ := rfl
  have e : y' + 3 - (y' + 2) = 1 := by omega
  conv at hstart => rhs; rw [e, stripe_succ, Bool.not_false, stripe_zero]
  conv at hend => rhs; rw [Nat.sub_self, stripe_zero, build_free msR (y' + 3 + 2) W hf]
  rw [hstart, hend]
  exact packet_to_marker (cons true (buildL true y' msL)) (build false (y' + 3 + 2 + 1) msR W)

/-- The marker sits one stripe cell after a block: the packet lands on the block and the machine halts. -/
theorem pkt_land_block (msL msR : List Mark) (r W : Nat) (hb : zeroBefore r msL) :
    steps (5 + 4 + 1) (pktCfgM (⟨.B, r⟩ :: msL) (r + 4) msR W) = none := by
  obtain ⟨L', hL⟩ := zeroBefore_tail hb
  have hstart : pktCfgM (⟨.B, r⟩ :: msL) (r + 4) msR W
      = ⟨cons true (stripe false (r + 4 - (r + 3)) (cons true (cons true (cons true (buildL true r msL))))),
         cons true (cons true (build false (r + 4 + 3) msR W)), .A⟩ := rfl
  have e : r + 4 - (r + 3) = 1 := by omega
  conv at hstart => rhs; rw [e, stripe_succ, Bool.not_false, stripe_zero, hL]
  rw [hstart]
  have h₂ := packet_to_marker (cons true (cons true (cons false L'))) (build false (r + 4 + 3) msR W)
  obtain ⟨h₃, h₄⟩ := packet_to_block L' (cons true (cons true (cons false (build false (r + 4 + 3) msR W))))
  have h := steps_halt (steps_seq h₂ h₃) h₄ 0
  simpa using h

/-- The marker on cell 0: the packet lands on it, and the round ends with the marker turned into the wall `W 5`. -/
theorem pkt_land_leftend_marker (msR : List Mark) (W : Nat) :
    steps 18 (pktCfgM [] 0 msR W) = some (roundStart (⟨.W, 5⟩ :: shiftMarks 4 msR) (W + 4)) := by
  have hstart : pktCfgM [] 0 msR W = ⟨cons true (stripe false 0 blank), cons true (cons true (build false 3 msR W)), .A⟩ := rfl
  have hend : roundStart (⟨.W, 5⟩ :: shiftMarks 4 msR) (W + 4)
      = ⟨cons false (cons false (cons true blank)),
         cons false (stripe true (5 - 4) (cons false (cons false (build false (3 + 4) (shiftMarks 4 msR) (W + 4))))), .E⟩ := rfl
  conv at hstart => rhs; rw [stripe_zero]
  conv at hend => rhs; rw [build_shiftMarks msR false 3 W 4]
  rw [hstart, hend]
  exact packet_to_leftend_marker (build false 3 msR W)

end BB6

namespace BB6

/-! ## The packet phase in the mark model, zipper form -/

inductive PR' where
  | gap (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat)
  | newRound (ms : List Mark) (W : Nat)
  | halt
  | uncovered
  deriving Repr

/-- The configuration an outcome denotes (`none` for a halt; `uncovered` makes no claim). -/
def PR'.cfg : PR' → Option Cfg
  | .gap msL g msR W => some (midCfg msL g msR W)
  | .newRound ms W => some (roundStart ms W)
  | .halt => none
  | .uncovered => none

/-- A stripe cell before the wall at `w` (a mark touching it from the left is not covered). -/
def wallFreeB (w : Nat) : List Mark → Bool
  | [] => decide (1 ≤ w)
  | m :: _ => decide (m.p + mlen m.t < w)

theorem wallFreeB_stripeBefore {w : Nat} {msL : List Mark} (h : wallFreeB w msL = true) : stripeBefore w msL := by
  cases msL <;> simp [wallFreeB, stripeBefore] at h ⊢ <;> exact h

/-- What happens from `pktCfgM msL y msR W`: the marker at `y` has just been reached from the right. -/
def pktLand : List Mark → Nat → List Mark → Nat → PR'
  | [], 0, msR, W => .newRound (⟨.W, 5⟩ :: shiftMarks 4 msR) (W + 4)
  | [], y, msR, W => .newRound (shiftMarks 2 (⟨.M, y⟩ :: msR)) (W + 2)
  | m :: msL, y, msR, W =>
    match m.t with
    | .M => if m.p + 3 ≤ y then pktLand msL m.p (⟨.M, y⟩ :: msR) W else .uncovered
    | .G => if m.p + 3 < y then .gap msL (m.p + 2) (⟨.M, y⟩ :: msR) W else .uncovered
    | .W => if m.p + 2 < y ∧ wallFreeB m.p msL = true then .gap (⟨.M, m.p - 1⟩ :: msL) (m.p + 1) (⟨.M, y⟩ :: msR) W
            else .uncovered
    | .B => .halt

/-- What happens from `pktCfg msL x msR W`: the zipper form of `Model.packetBack`. -/
def pktBack : List Mark → Nat → List Mark → Nat → PR'
  | [], _, msR, W => .newRound (shiftMarks 2 msR) (W + 2)
  | m :: msL, _, msR, W =>
    match m.t with
    | .M => pktLand msL m.p msR W
    | .G => .gap msL (m.p + 2) msR W
    | .W => if wallFreeB m.p msL = true then .gap (⟨.M, m.p - 1⟩ :: msL) (m.p + 1) msR W else .uncovered
    | .B => .halt

/-- Chaining a run with any run, halting or not. -/
theorem steps_seq_any {a b : Nat} {c c' : Cfg} {o : Option Cfg} (h₁ : steps a c = some c') (h₂ : steps b c' = o) :
    steps (a + b) c = o := by
  induction a generalizing c with
  | zero =>
    simp [steps] at h₁
    subst h₁
    simpa using h₂
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    cases hs : step c with
    | none => simp [steps, hs] at h₁
    | some d =>
      rw [steps_succ_of_step a hs] at h₁
      rw [steps_succ_of_step (a + b) hs]
      exact ih h₁

theorem rightOK_sub2k {q : Nat} {u : Bool} {W : Nat} {msR : List Mark} (k : Nat) (h : rightOK (q + 2 * k) u W msR) :
    rightOK q u W msR := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have e : q + 2 * (k + 1) = q + 2 * k + 2 := by omega
    rw [e] at h
    exact rightOK_pred2 h

theorem mod_two_zero_of_not_one {n : Nat} (h : n % 2 ≠ 1) : n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h' | h'
  · exact h'
  · exact absurd h' h

theorem leftOK_zeroBefore {r : Nat} {msL : List Mark} (h : leftOK r true msL) : zeroBefore r msL := by
  cases msL with
  | nil => trivial
  | cons m ms =>
    obtain ⟨h1, h2, -⟩ := h
    show m.p + mlen m.t < r ∨ (m.p + mlen m.t = r ∧ mval m.t = false)
    cases hv : mval m.t with
    | true =>
      rw [hv] at h2
      have h3 : (r - (m.p + mlen m.t)) % 2 = 1 := h2.mpr rfl
      left; omega
    | false =>
      rw [hv] at h2
      have h3 : (r - (m.p + mlen m.t)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      rcases Nat.lt_or_ge (m.p + mlen m.t) r with hlt | hge
      · left; exact hlt
      · right; exact ⟨by omega, rfl⟩

theorem leftOK_oneBefore {g : Nat} {msL : List Mark} (h : leftOK g false msL) : oneBefore g msL := by
  cases msL with
  | nil =>
    show 1 ≤ g
    have h' : g % 2 = 1 := h.mpr rfl
    omega
  | cons m ms =>
    obtain ⟨h1, h2, -⟩ := h
    show m.p + mlen m.t < g ∨ (m.p + mlen m.t = g ∧ mval m.t = true)
    cases hv : mval m.t with
    | false =>
      rw [hv] at h2
      have h3 : (g - (m.p + mlen m.t)) % 2 = 1 := h2.mpr rfl
      left; omega
    | true =>
      rw [hv] at h2
      have h3 : (g - (m.p + mlen m.t)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      rcases Nat.lt_or_ge (m.p + mlen m.t) g with hlt | hge
      · left; exact hlt
      · right; exact ⟨by omega, rfl⟩

/-- From the marker just reached, the machine arrives where `pktLand` says. -/
theorem pktLand_run (msL : List Mark) : ∀ (y : Nat) (msR : List Mark) (W : Nat), leftOK y true msL →
    rightOK (y + 3) false W msR → pktLand msL y msR W ≠ .uncovered →
    ∃ n, steps n (pktCfgM msL y msR W) = (pktLand msL y msR W).cfg := by
  induction msL with
  | nil =>
    intro y msR W hL hR _
    simp only [leftOK] at hL
    cases y with
    | zero => exact ⟨18, pkt_land_leftend_marker msR W⟩
    | succ y =>
      have hy : (y + 1) % 2 = 0 := by cases h : (y + 1) % 2 <;> simp_all <;> omega
      obtain ⟨j, hj⟩ : ∃ j, y + 1 = 2 * j + 2 := ⟨(y + 1) / 2 - 1, by omega⟩
      have h₁ := pkt_land_std [] msR (y + 1) W (by simp only [stripeBefore2]; omega) (rightOK_freeAt hR)
      have h₂ := ev_pkt_leftend (⟨.M, y + 1⟩ :: msR) j W (by simp only [startsAt]; omega)
      have e : y + 1 - 2 = 2 * j := by omega
      rw [e] at h₁
      exact ⟨5 + (4 * j + 7), steps_seq h₁ h₂⟩
  | cons m msL ih =>
    intro y msR W hL hR hnu
    obtain ⟨t, p⟩ := m
    simp only [leftOK] at hL
    obtain ⟨h1, h2, h3⟩ := hL
    cases t with
    | M =>
      simp only [mlen, mval] at h1 h2 h3
      have hodd : (y - (p + 2)) % 2 = 1 := by simpa using h2
      obtain ⟨j, hj⟩ : ∃ j, y = p + 3 + 2 * j := ⟨(y - (p + 2)) / 2, by omega⟩
      have hle : p + 3 ≤ y := by omega
      simp only [pktLand, hle, if_true] at hnu ⊢
      have hR' : rightOK (p + 3) false W (⟨.M, y⟩ :: msR) := by
        simp only [rightOK, mval, mlen]
        refine ⟨by omega, by simp; omega, ?_⟩
        have := rightOK_pred hR
        simpa using this
      obtain ⟨n, hn⟩ := ih p (⟨.M, y⟩ :: msR) W h3 hR' hnu
      cases j with
      | zero =>
        have hj' : y = p + 3 := by omega
        subst hj'
        have h₁ := pkt_land_next msL msR p W (rightOK_freeAt hR)
        exact ⟨5 + n, steps_seq_any h₁ hn⟩
      | succ j =>
        have h₁ := pkt_land_std (⟨.M, p⟩ :: msL) msR y W (by simp only [stripeBefore2, mlen]; omega) (rightOK_freeAt hR)
        have h₂ := pkt_carry msL (⟨.M, y⟩ :: msR) p j W (by simp only [startsAt]; omega)
        have e : y - 2 = p + 3 + 2 * j := by omega
        rw [e] at h₁
        exact ⟨5 + 4 * (j + 1) + n, steps_seq_any (steps_seq h₁ h₂) hn⟩
    | G =>
      simp only [mlen, mval] at h1 h2 h3
      have heven : (y - (p + 3)) % 2 = 0 := by cases h : (y - (p + 3)) % 2 <;> simp_all <;> omega
      obtain ⟨j, hj⟩ : ∃ j, y = p + 3 + 2 * j := ⟨(y - (p + 3)) / 2, by omega⟩
      cases j with
      | zero => subst hj; simp [pktLand] at hnu
      | succ j =>
        have hlt : p + 3 < y := by omega
        simp only [pktLand, hlt, if_true, PR'.cfg]
        have h₁ := pkt_land_std (⟨.G, p⟩ :: msL) msR y W (by simp only [stripeBefore2, mlen]; omega) (rightOK_freeAt hR)
        have h₂ := ev_pkt_gap msL (⟨.M, y⟩ :: msR) p j W (leftOK_endsBy h3) (by simp only [startsAt]; omega)
        have e : y - 2 = p + 3 + 2 * j := by omega
        rw [e] at h₁
        exact ⟨5 + (4 * j + 7), steps_seq h₁ h₂⟩
    | W =>
      simp only [mlen, mval] at h1 h2 h3
      have heven : (y - (p + 2)) % 2 = 0 := by cases h : (y - (p + 2)) % 2 <;> simp_all <;> omega
      obtain ⟨j, hj⟩ : ∃ j, y = p + 2 + 2 * j := ⟨(y - (p + 2)) / 2, by omega⟩
      cases j with
      | zero => subst hj; simp [pktLand] at hnu
      | succ j =>
        have hlt : p + 2 < y := by omega
        cases hw : wallFreeB p msL with
        | false => simp [pktLand, hw] at hnu
        | true =>
          simp only [pktLand, hlt, hw, and_self, if_true, PR'.cfg]
          have h₁ := pkt_land_std (⟨.W, p⟩ :: msL) msR y W (by simp only [stripeBefore2, mlen]; omega) (rightOK_freeAt hR)
          have h₂ := ev_pkt_wall msL (⟨.M, y⟩ :: msR) p j W (wallFreeB_stripeBefore hw) (by simp only [startsAt]; omega)
          have e : y - 2 = p + 2 + 2 * j := by omega
          rw [e] at h₁
          exact ⟨5 + (4 * j + 7), steps_seq h₁ h₂⟩
    | B =>
      simp only [mlen, mval] at h1 h2 h3
      have hodd : (y - (p + 3)) % 2 = 1 := by simpa using h2
      obtain ⟨j, hj⟩ : ∃ j, y = p + 4 + 2 * j := ⟨(y - (p + 3)) / 2, by omega⟩
      simp only [pktLand, PR'.cfg]
      cases j with
      | zero =>
        subst hj
        exact ⟨5 + 4 + 1, pkt_land_block msL msR p W (leftOK_zeroBefore h3)⟩
      | succ j =>
        have h₁ := pkt_land_std (⟨.B, p⟩ :: msL) msR y W (by simp only [stripeBefore2, mlen]; omega) (rightOK_freeAt hR)
        have h₂ := ev_pkt_block' msL (⟨.M, y⟩ :: msR) p j W (leftOK_zeroBefore h3)
        have e : y - 2 = p + 3 + (2 * j + 1) := by omega
        rw [e] at h₁
        exact ⟨5 + (4 * (j + 1) + 4 + 1), steps_seq_any h₁ h₂⟩

/-- From a packet configuration, the machine arrives where `pktBack` says. -/
theorem pktBack_run (msL : List Mark) (x : Nat) (msR : List Mark) (W : Nat) (hL : leftOK x true msL)
    (hR : rightOK (x + 2) false W msR) (hnu : pktBack msL x msR W ≠ .uncovered) :
    ∃ n, steps n (pktCfg msL x msR W) = (pktBack msL x msR W).cfg := by
  cases msL with
  | nil =>
    change (x % 2 = 1 ↔ true = false) at hL
    have hx : x % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (hL.mp h) (by decide))
    obtain ⟨j, hj⟩ : ∃ j, x = 2 * j := ⟨x / 2, by omega⟩
    subst hj
    exact ⟨4 * j + 7, ev_pkt_leftend msR j W (rightOK_startsAt hR)⟩
  | cons m msL =>
    obtain ⟨t, p⟩ := m
    obtain ⟨h1, h2, h3⟩ := hL
    cases t with
    | M =>
      simp only [mlen, mval] at h1 h2 h3
      have hodd : (x - (p + 2)) % 2 = 1 := h2.mpr trivial
      obtain ⟨j, hj⟩ : ∃ j, x = p + 3 + 2 * j := ⟨(x - (p + 2)) / 2, by omega⟩
      subst hj
      simp only [pktBack] at hnu ⊢
      have h₁ := pkt_carry msL msR p j W (startsAt_mono (rightOK_startsAt hR) (by omega))
      have hR' : rightOK (p + 3) false W msR := by
        have e : p + 3 + 2 * j + 2 = p + 3 + 2 * (j + 1) := by omega
        rw [e] at hR
        exact rightOK_sub2k (j + 1) hR
      obtain ⟨n, hn⟩ := pktLand_run msL p msR W h3 hR' hnu
      exact ⟨4 * (j + 1) + n, steps_seq_any h₁ hn⟩
    | G =>
      simp only [mlen, mval] at h1 h2 h3
      have heven : (x - (p + 3)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      obtain ⟨j, hj⟩ : ∃ j, x = p + 3 + 2 * j := ⟨(x - (p + 3)) / 2, by omega⟩
      subst hj
      simp only [pktBack, PR'.cfg]
      exact ⟨4 * j + 7, ev_pkt_gap msL msR p j W (leftOK_endsBy h3) (rightOK_startsAt hR)⟩
    | W =>
      simp only [mlen, mval] at h1 h2 h3
      have heven : (x - (p + 2)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      obtain ⟨j, hj⟩ : ∃ j, x = p + 2 + 2 * j := ⟨(x - (p + 2)) / 2, by omega⟩
      subst hj
      cases hw : wallFreeB p msL with
      | false => simp [pktBack, hw] at hnu
      | true =>
        simp only [pktBack, hw, if_true, PR'.cfg]
        exact ⟨4 * j + 7, ev_pkt_wall msL msR p j W (wallFreeB_stripeBefore hw) (rightOK_startsAt hR)⟩
    | B =>
      simp only [mlen, mval] at h1 h2 h3
      have hodd : (x - (p + 3)) % 2 = 1 := h2.mpr trivial
      obtain ⟨j, hj⟩ : ∃ j, x = p + 3 + (2 * j + 1) := ⟨(x - (p + 3)) / 2, by omega⟩
      subst hj
      simp only [pktBack, PR'.cfg]
      exact ⟨4 * (j + 1) + 4 + 1, ev_pkt_block' msL msR p j W (leftOK_zeroBefore h3)⟩

/-! ## Well-formedness of what the packet phase produces -/

theorem rightOK_shift {q : Nat} {u : Bool} {W : Nat} {ms : List Mark} (s : Nat) (h : rightOK q u W ms) :
    rightOK (q + s) u (W + s) (shiftMarks s ms) := by
  induction ms generalizing q u with
  | nil =>
    simp only [rightOK, shiftMarks, List.map_nil] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_add_right]
    exact h2
  | cons m ms ih =>
    simp only [rightOK, shiftMarks, List.map_cons] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by omega, ?_, ?_⟩
    · rw [Nat.add_sub_add_right]
      exact h2
    · have e : m.p + s + mlen m.t = m.p + mlen m.t + s := by omega
      rw [e]
      exact ih h3

/-- The outcome of the packet phase is well formed: a gap configuration, or a round start. -/
def PR'.wf : PR' → Prop
  | .gap msL g msR W => leftOK g false msL ∧ rightOK (g + 3) false W msR
  | .newRound ms W => rightOK 4 false W ms
  | .halt => True
  | .uncovered => True

theorem rightOK_cons_M {q : Nat} {W y : Nat} {msR : List Mark} (hq : q ≤ y) (hpar : (y - q) % 2 = 0)
    (h : rightOK (y + 3) false W msR) : rightOK q false W (⟨.M, y⟩ :: msR) := by
  simp only [rightOK, mval, mlen]
  refine ⟨hq, ?_, ?_⟩
  · constructor
    · intro h'; omega
    · intro h'; exact absurd h' (by decide)
  · have := rightOK_pred h
    simpa using this

theorem pktLand_wf (msL : List Mark) : ∀ (y : Nat) (msR : List Mark) (W : Nat), leftOK y true msL →
    rightOK (y + 3) false W msR → (pktLand msL y msR W).wf := by
  induction msL with
  | nil =>
    intro y msR W hL hR
    change (y % 2 = 1 ↔ true = false) at hL
    cases y with
    | zero =>
      show rightOK 4 false (W + 4) (⟨.W, 5⟩ :: shiftMarks 4 msR)
      simp only [rightOK, mval, mlen]
      refine ⟨by omega, by decide, ?_⟩
      have := rightOK_shift 4 hR
      simpa using this
    | succ y =>
      have hy : (y + 1) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (hL.mp h) (by decide))
      show rightOK 4 false (W + 2) (shiftMarks 2 (⟨.M, y + 1⟩ :: msR))
      have h2 : rightOK 2 false W (⟨.M, y + 1⟩ :: msR) := rightOK_cons_M (by omega) (by omega) hR
      have := rightOK_shift 2 h2
      simpa using this
  | cons m msL ih =>
    intro y msR W hL hR
    obtain ⟨t, p⟩ := m
    obtain ⟨h1, h2, h3⟩ := hL
    cases t with
    | M =>
      simp only [mlen, mval] at h1 h2 h3
      have hodd : (y - (p + 2)) % 2 = 1 := h2.mpr trivial
      have hle : p + 3 ≤ y := by omega
      simp only [pktLand, hle, if_true]
      exact ih p (⟨.M, y⟩ :: msR) W h3 (rightOK_cons_M (by omega) (by omega) hR)
    | G =>
      simp only [mlen, mval] at h1 h2 h3
      have heven : (y - (p + 3)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      by_cases hlt : p + 3 < y
      · simp only [pktLand, hlt, if_true, PR'.wf]
        exact ⟨leftOK_add2 h3, rightOK_cons_M (by omega) (by omega) hR⟩
      · simp only [pktLand, hlt, if_false, PR'.wf]
    | W =>
      simp only [mlen, mval] at h1 h2 h3
      have heven : (y - (p + 2)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      by_cases hc : p + 2 < y ∧ wallFreeB p msL = true
      · simp only [pktLand, hc, and_self, if_true, PR'.wf]
        have hs := wallFreeB_stripeBefore hc.2
        have hp : 1 ≤ p := by cases msL <;> simp only [stripeBefore] at hs <;> omega
        refine ⟨?_, rightOK_cons_M (by omega) (by omega) hR⟩
        simp only [leftOK, mlen, mval]
        refine ⟨by omega, ⟨fun h' => absurd h' (by omega), fun h' => absurd h' (by decide)⟩, ?_⟩
        have h3' : leftOK (p - 1 + 1) false msL := by rw [Nat.sub_add_cancel hp]; exact h3
        have := leftOK_pred h3' (stripeBefore_endsBy' hs)
        simpa using this
      · simp only [pktLand, hc, if_false, PR'.wf]
    | B => simp only [pktLand, PR'.wf]

theorem pktBack_wf (msL : List Mark) (x : Nat) (msR : List Mark) (W : Nat) (hL : leftOK x true msL)
    (hR : rightOK (x + 2) false W msR) : (pktBack msL x msR W).wf := by
  cases msL with
  | nil =>
    change (x % 2 = 1 ↔ true = false) at hL
    have hx : x % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (hL.mp h) (by decide))
    show rightOK 4 false (W + 2) (shiftMarks 2 msR)
    have h2 : rightOK 2 false W msR := by
      obtain ⟨j, hj⟩ : ∃ j, x = 2 * j := ⟨x / 2, by omega⟩
      subst hj
      have e : 2 * j + 2 = 2 + 2 * j := by omega
      rw [e] at hR
      exact rightOK_sub2k j hR
    have := rightOK_shift 2 h2
    simpa using this
  | cons m msL =>
    obtain ⟨t, p⟩ := m
    obtain ⟨h1, h2, h3⟩ := hL
    cases t with
    | M =>
      simp only [mlen, mval] at h1 h2 h3
      have hodd : (x - (p + 2)) % 2 = 1 := h2.mpr trivial
      simp only [pktBack]
      apply pktLand_wf msL p msR W h3
      obtain ⟨j, hj⟩ : ∃ j, x + 2 = p + 3 + 2 * (j + 1) := ⟨(x - (p + 3)) / 2, by omega⟩
      rw [hj] at hR
      exact rightOK_sub2k (j + 1) hR
    | G =>
      simp only [mlen, mval] at h1 h2 h3
      have heven : (x - (p + 3)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      simp only [pktBack, PR'.wf]
      refine ⟨leftOK_add2 h3, ?_⟩
      obtain ⟨j, hj⟩ : ∃ j, x + 2 = p + 2 + 3 + 2 * j := ⟨(x - (p + 3)) / 2, by omega⟩
      rw [hj] at hR
      exact rightOK_sub2k j hR
    | W =>
      simp only [mlen, mval] at h1 h2 h3
      have heven : (x - (p + 2)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      cases hw : wallFreeB p msL with
      | false => simp only [pktBack, hw, Bool.false_eq_true, if_false, PR'.wf]
      | true =>
        simp only [pktBack, hw, if_true, PR'.wf]
        have hs := wallFreeB_stripeBefore hw
        have hp : 1 ≤ p := by cases msL <;> simp only [stripeBefore] at hs <;> omega
        refine ⟨?_, ?_⟩
        · simp only [leftOK, mlen, mval]
          refine ⟨by omega, ⟨fun h' => absurd h' (by omega), fun h' => absurd h' (by decide)⟩, ?_⟩
          have h3' : leftOK (p - 1 + 1) false msL := by rw [Nat.sub_add_cancel hp]; exact h3
          have := leftOK_pred h3' (stripeBefore_endsBy' hs)
          simpa using this
        · obtain ⟨j, hj⟩ : ∃ j, x + 2 = p + 1 + 3 + 2 * j := ⟨(x - (p + 2)) / 2, by omega⟩
          rw [hj] at hR
          exact rightOK_sub2k j hR
    | B => simp only [pktBack, PR'.wf]

end BB6
