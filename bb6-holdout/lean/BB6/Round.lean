import BB6.PktRun

/-!
# The gap phase, and the round

`gapEvent msL g msR W` is one event of the gap phase in zipper form (the active gap at `g`, the marks to its left
nearest first, the marks to its right), the mirror of `Model.event`: the gap meets a marker (swap or merge), a wall
(the gap and the wall vanish and a shift runs to the next mark), a block (the block acts as a wall one cell left
while the gap sleeps), or nothing (a new end marker, and a packet).  Its outcome is a new gap configuration, a packet
configuration (plain, or on a marker's second cell when the packet starts right after a marker touching the gap), a
halt, or `uncovered`.

`gapEvent_ok` is the machine theorem for one event under well-formedness, `roundZ` runs events until a packet ends
the round, and `roundZ_run` is the round theorem: from a well-formed round start, the machine reaches the round
start `roundZ` computes, or halts when it says so.

One convention of the mark model shows up here: when a shift opens a gap at the position of the end marker, the
model keeps the width W = g + 2 (the gap's cells are the last ones).  Such a gap has no stripe to its right at all,
and its next event (the gap meets nothing) sends the packet from g − 1.  The well-formedness of a gap configuration
(`gapWF`) allows exactly this case besides a stripe of odd length after the gap.
-/

namespace BB6

inductive GR where
  | gap (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat)
  | pkt (msL : List Mark) (x : Nat) (msR : List Mark) (W : Nat)
  | pktM (msL : List Mark) (y : Nat) (msR : List Mark) (W : Nat)
  | halt
  | uncovered

def strictAfterB (q W : Nat) : List Mark → Bool
  | [] => decide (q < W)
  | m :: _ => decide (q < m.p)

def freeAtB (q W : Nat) : List Mark → Bool
  | [] => decide (q ≤ W)
  | m :: _ => decide (q < m.p)

theorem strictAfterB_iff {q W : Nat} {ms : List Mark} : strictAfterB q W ms = true ↔ strictAfter q W ms := by
  cases ms <;> simp [strictAfterB, strictAfter]

theorem freeAtB_iff {q W : Nat} {ms : List Mark} : freeAtB q W ms = true ↔ freeAt q W ms := by
  cases ms <;> simp [freeAtB, freeAt]

/-- A packet that starts at g − 1, where the cell g − 1 reads 1: a plain packet configuration when g − 1 is a stripe
cell; the packet on the second cell of a marker that ends at g; a halt when a block ends at g. -/
def pktFrom (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat) : GR :=
  if wallFreeB g msL = true then .pkt msL (g - 1) msR W
  else match msL with
    | ⟨.M, y⟩ :: msL' => .pktM msL' y msR W
    | ⟨.B, _⟩ :: _ => .halt
    | _ => .uncovered

/-- One more blank cell at the end of a stripe changes nothing when that cell would read 0. -/
theorem stripe_pad (c : Bool) (n : Nat) (h : (n % 2 = 0 ∧ c = false) ∨ (n % 2 = 1 ∧ c = true)) :
    stripe c (n + 1) blank = stripe c n blank := by
  induction n generalizing c with
  | zero =>
    rcases h with ⟨_, hc⟩ | ⟨h, _⟩
    · subst hc; exact cons_false_blank
    · simp at h
  | succ n ih =>
    show cons c (stripe (!c) (n + 1) blank) = cons c (stripe (!c) n blank)
    rw [ih (!c) (by cases c <;> simp at h ⊢ <;> omega)]

/-- A well-formed tape can be read with a width one larger: the extra cell is a 0. -/
theorem build_pad (ms : List Mark) : ∀ (q : Nat) (u : Bool) (W : Nat), rightOK q u W ms →
    build u q ms (W + 1) = build u q ms W := by
  induction ms with
  | nil =>
    intro q u W h
    obtain ⟨h1, h2⟩ := h
    show stripe (!u) (W + 1 - q) blank = stripe (!u) (W - q) blank
    rw [show W + 1 - q = (W - q) + 1 by omega]
    apply stripe_pad
    cases u <;> simp at h2 ⊢ <;> omega
  | cons m ms ih =>
    intro q u W h
    obtain ⟨h1, h2, h3⟩ := h
    show stripe (!u) (m.p - q) (app (mcells m.t) (build (mval m.t) (m.p + mlen m.t) ms (W + 1)))
      = stripe (!u) (m.p - q) (app (mcells m.t) (build (mval m.t) (m.p + mlen m.t) ms W))
    rw [ih _ _ _ h3]

/-- A wall in the last two cells (p, p + 1 = W − 1) is blank tape: the same tape as no wall and width p.  This is how
the mark model in Python, C and `Model.lean` writes the result of a shift that reaches a block ending the tape. -/
theorem build_trailing_wall (u : Bool) (q p : Nat) : build u q [⟨.W, p⟩] (p + 2) = build u q [] p := by
  show stripe (!u) (p - q) (app [false, false] (stripe (!false) (p + 2 - (p + 2)) blank)) = stripe (!u) (p - q) blank
  rw [Nat.sub_self, stripe_zero]
  show stripe (!u) (p - q) (cons false (cons false blank)) = _
  rw [cons_false_blank, cons_false_blank]

/-- One event of the gap phase. -/
def gapEvent (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat) : GR :=
  match msR with
  | [] => if W = g + 2 then pktFrom msL g [⟨.M, g + 3⟩] (g + 5) else .pkt msL (W - 3) [⟨.M, W + 1⟩] (W + 3)
  | m :: msR' =>
    match m.t with
    | .M =>
      if m.p < g + 3 then .uncovered else
      let d := m.p - (g + 3)
      if d % 2 = 1 then .uncovered else
      if d % 4 = 0 then
        if d = 0 ∧ wallFreeB g msL = false then .uncovered
        else .gap (⟨.M, g + d / 2 - 1⟩ :: msL) (g + d / 2 + 1) msR' W
      else
        if d = 2 then pktFrom msL g (⟨.W, g + 4⟩ :: msR') W
        else .pkt msL (g + d / 2 - 2) (⟨.W, g + d / 2 + 3⟩ :: msR') W
    | .W =>
      match msR' with
      | [] => .pkt msL (m.p - 3) [⟨.M, W⟩] (W + 2)
      | m₂ :: msR'' =>
        match m₂.t with
        | .M => if freeAtB (m₂.p + 2) W msR'' then .gap msL m₂.p msR'' W else .uncovered
        | .W => if strictAfterB (m₂.p + 2) W msR'' then .pkt msL (m.p - 3) (⟨.B, m₂.p⟩ :: msR'') W else .uncovered
        | .B => if msR''.isEmpty = true ∧ W = m₂.p + 3 then .pkt msL (m.p - 3) [] (m₂.p + 2)
                else if strictAfterB (m₂.p + 3) W msR'' then .pkt msL (m.p - 3) (⟨.W, m₂.p + 2⟩ :: msR'') W else .uncovered
        | .G => .uncovered
    | .B =>
      if m.p < g + 5 then .uncovered else
      match msR' with
      | [] => .gap (⟨.M, m.p - 2⟩ :: ⟨.G, g⟩ :: msL) m.p [⟨.M, W⟩] (W + 2)
      | m₂ :: msR'' =>
        match m₂.t with
        | .M => if freeAtB (m₂.p + 2) W msR'' then .gap (⟨.W, m.p - 1⟩ :: ⟨.G, g⟩ :: msL) m₂.p msR'' W else .uncovered
        | .W => if strictAfterB (m₂.p + 2) W msR'' then .gap (⟨.M, m.p - 2⟩ :: ⟨.G, g⟩ :: msL) m.p (⟨.B, m₂.p⟩ :: msR'') W
                else .uncovered
        | .B => if msR''.isEmpty = true ∧ W = m₂.p + 3 then .gap (⟨.M, m.p - 2⟩ :: ⟨.G, g⟩ :: msL) m.p [] (m₂.p + 2)
                else if strictAfterB (m₂.p + 3) W msR'' then .gap (⟨.M, m.p - 2⟩ :: ⟨.G, g⟩ :: msL) m.p (⟨.W, m₂.p + 2⟩ :: msR'') W
                else .uncovered
        | .G => .uncovered
    | .G => .uncovered

/-- Well-formedness of a gap configuration: the marks on the left as for any point with a 0 there, and on the right
either a stripe of odd length (then marks, or the width) or nothing at all (the gap's cells are the last ones,
W = g + 2). -/
def gapWF (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat) : Prop :=
  leftOK g false msL ∧ (rightOK (g + 3) false W msR ∨ (msR = [] ∧ W = g + 2))

/-- What the machine does from `c`, according to an outcome: reaches the configuration it denotes, which is well
formed, or halts. -/
def GR.ok (c : Cfg) : GR → Prop
  | .gap msL g msR W => (∃ n, steps n c = some (midCfg msL g msR W)) ∧ gapWF msL g msR W
  | .pkt msL x msR W => (∃ n, steps n c = some (pktCfg msL x msR W)) ∧ leftOK x true msL ∧ rightOK (x + 2) false W msR
  | .pktM msL y msR W => (∃ n, steps n c = some (pktCfgM msL y msR W)) ∧ leftOK y true msL ∧ rightOK (y + 3) false W msR
  | .halt => ∃ n, steps n c = none
  | .uncovered => True

theorem leftOK_add2k {p : Nat} {v : Bool} {msL : List Mark} (k : Nat) (h : leftOK p v msL) : leftOK (p + 2 * k) v msL := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have e : p + 2 * (k + 1) = p + 2 * k + 2 := by omega
    rw [e]
    exact leftOK_add2 ih

theorem rightOK_zeroAfter {p W : Nat} {msR : List Mark} (h : rightOK (p + 2) true W msR) : zeroAfter p W msR := by
  cases msR with
  | nil => exact h.1
  | cons m ms =>
    obtain ⟨h1, h2, -⟩ := h
    show p + 2 < m.p ∨ (p + 2 = m.p ∧ mval m.t = false)
    cases hv : mval m.t with
    | true =>
      rw [hv] at h2
      have h3 : (m.p - (p + 2)) % 2 = 1 := h2.mpr rfl
      left; omega
    | false =>
      rw [hv] at h2
      have h3 : (m.p - (p + 2)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      rcases Nat.lt_or_ge (p + 2) m.p with hlt | hge
      · left; exact hlt
      · right; exact ⟨by omega, rfl⟩

/-- A packet starting at g − 1 from the raw configuration the rules leave: `L'` is what is left of the 1 at g − 1. -/
theorem pktFrom_ok (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat) (L' : Tape)
    (hL : leftOK g false msL) (hL1 : buildL false g msL = cons true L') (hR : rightOK (g + 1) false W msR) :
    (pktFrom msL g msR W).ok ⟨L', cons true (cons true (build false (g + 1) msR W)), .A⟩ := by
  have hg := oneBefore_pos (leftOK_oneBefore hL)
  cases hw : wallFreeB g msL with
  | true =>
    simp only [pktFrom, hw, if_true, GR.ok]
    have hs := wallFreeB_stripeBefore hw
    have h := buildL_succ msL false (g - 1) (stripeBefore_endsBy' hs)
    rw [Nat.sub_add_cancel hg, hL1, Bool.not_false] at h
    have hL' : L' = buildL true (g - 1) msL := cons_tail_eq h
    refine ⟨⟨0, ?_⟩, ?_, ?_⟩
    · show some _ = some (pktCfg msL (g - 1) msR W)
      rw [hL']
      have e : g - 1 + 2 = g + 1 := by omega
      show some (⟨buildL true (g - 1) msL, cons true (cons true (build false (g + 1) msR W)), .A⟩ : Cfg)
        = some ⟨buildL true (g - 1) msL, cons true (cons true (build false (g - 1 + 2) msR W)), .A⟩
      rw [e]
    · have hL2 : leftOK (g - 1 + 1) false msL := by rw [Nat.sub_add_cancel hg]; exact hL
      have := leftOK_pred hL2 (stripeBefore_endsBy' hs)
      simpa using this
    · have e : g - 1 + 2 = g + 1 := by omega
      rw [e]; exact hR
  | false =>
    cases msL with
    | nil => simp [wallFreeB] at hw; omega
    | cons m msL' =>
      obtain ⟨t, p⟩ := m
      obtain ⟨h1, h2, h3⟩ := hL
      have hw' := hw
      simp only [wallFreeB, decide_eq_false_iff_not, Nat.not_lt] at hw
      dsimp only at h1 h2 h3 hw
      have he : p + mlen t = g := by omega
      have h2' : (g - (p + mlen t)) % 2 = 1 ↔ false = mval t := h2
      rw [he, Nat.sub_self] at h2'
      cases t with
      | G => simp [mval] at h2'
      | W => simp [mval] at h2'
      | M =>
        simp only [mlen] at he h3
        simp only [pktFrom, hw', Bool.false_eq_true, if_false, GR.ok]
        have hb : buildL false g (⟨.M, p⟩ :: msL') = cons true (cons true (buildL true p msL')) := by
          show stripe (!false) (g - (p + mlen .M)) _ = _
          rw [show g - (p + mlen .M) = 0 by simp only [mlen]; omega, stripe_zero]
          rfl
        rw [hb] at hL1
        have hL' : L' = cons true (buildL true p msL') := (cons_tail_eq hL1).symm
        refine ⟨⟨0, ?_⟩, h3, ?_⟩
        · rw [hL']
          show some (⟨cons true (buildL true p msL'), cons true (cons true (build false (g + 1) msR W)), .A⟩ : Cfg)
            = some ⟨cons true (buildL true p msL'), cons true (cons true (build false (p + 3) msR W)), .A⟩
          rw [show p + 3 = g + 1 by omega]
        · rw [show p + 3 = g + 1 by omega]; exact hR
      | B =>
        simp only [mlen] at he h3
        simp only [pktFrom, hw', Bool.false_eq_true, if_false, GR.ok]
        have hb : buildL false g (⟨.B, p⟩ :: msL') = cons true (cons true (cons true (buildL true p msL'))) := by
          show stripe (!false) (g - (p + mlen .B)) _ = _
          rw [show g - (p + mlen .B) = 0 by simp only [mlen]; omega, stripe_zero]
          rfl
        rw [hb] at hL1
        have hL' : L' = cons true (cons true (buildL true p msL')) := (cons_tail_eq hL1).symm
        obtain ⟨L'', hL''⟩ := zeroBefore_tail (leftOK_zeroBefore h3)
        rw [hL', hL'']
        obtain ⟨h₃, h₄⟩ := packet_to_block L'' (build false (g + 1) msR W)
        exact ⟨4 + (0 + 1), steps_halt h₃ h₄ 0⟩

/-- The merge in raw form: the configuration the rules leave, for any k (for k = 0 the packet sits at g − 1 and
`L'` is what is left of the 1 at g − 1). -/
theorem ev_merge_raw (msL msR : List Mark) (g k W : Nat) (L' : Tape) (hL1 : buildL false g msL = cons true L')
    (hR : zeroAfter (g + 3 + 4 * k + 2) W msR) :
    steps (bounceSteps k 1 + 31) (midCfg msL g (⟨.M, g + 3 + 4 * k + 2⟩ :: msR) W)
      = some ⟨rep k [false, true] L', cons true (cons true (build false (g + 2 * k + 1) (⟨.W, g + 2 * k + 4⟩ :: msR) W)), .A⟩ := by
  obtain ⟨R', hR1⟩ := zeroAfter_tail hR
  have hR2 := build_odd_shift msR (g + 3 + 4 * k + 2) W k R' (zeroAfter_startsAt hR) hR1 (by omega)
  have hstart : midCfg msL g (⟨.M, g + 3 + 4 * k + 2⟩ :: msR) W
      = ⟨cons false (cons false (buildL false g msL)),
         cons false (stripe true (g + 3 + 4 * k + 2 - (g + 3)) (cons true (cons true (build true (g + 3 + 4 * k + 2 + 2) msR W)))), .E⟩ := rfl
  have hend : build false (g + 2 * k + 1) (⟨.W, g + 2 * k + 4⟩ :: msR) W
      = stripe true (g + 2 * k + 4 - (g + 2 * k + 1)) (cons false (cons false (build false (g + 2 * k + 4 + 2) msR W))) := rfl
  have e₁ : g + 3 + 4 * k + 2 - (g + 3) = 2 * (2 * k + 1) := by omega
  have e₂ : g + 2 * k + 4 - (g + 2 * k + 1) = 3 := by omega
  have e₃ : g + 2 * k + 4 + 2 = g + 3 + 4 * k + 2 + 2 - (2 * k + 1) := by omega
  conv at hstart => rhs; rw [hL1, e₁, stripe_even, Bool.not_true, hR1]
  rw [hstart, hend, e₂, e₃, hR2]
  exact gap_marker_merge k L' R'

/-- After a marker followed by a free cell: the next point is well formed, or the marker was the end marker. -/
theorem rightOK_freeAt_next {q W : Nat} {msR : List Mark} (h : rightOK (q + 2) true W msR) (hf : freeAt (q + 2) W msR) :
    rightOK (q + 3) false W msR ∨ (msR = [] ∧ W = q + 2) := by
  cases msR with
  | nil =>
    simp only [freeAt] at hf
    rcases Nat.lt_or_ge (q + 2) W with hlt | hge
    · left
      have := rightOK_succ h (by simp only [strictAfter]; exact hlt)
      simpa using this
    · right; exact ⟨rfl, by omega⟩
  | cons m ms =>
    left
    have := rightOK_succ h (by simp only [strictAfter]; simp only [freeAt] at hf; exact hf)
    simpa using this

/-- Prepending steps to an outcome's run. -/
theorem GR.ok_seq {a : Nat} {c c' : Cfg} (h : steps a c = some c') {r : GR} (hr : r.ok c') : r.ok c := by
  cases r with
  | gap msL g msR W => obtain ⟨⟨n, hn⟩, hw⟩ := hr; exact ⟨⟨a + n, steps_seq h hn⟩, hw⟩
  | pkt msL x msR W => obtain ⟨⟨n, hn⟩, hw⟩ := hr; exact ⟨⟨a + n, steps_seq h hn⟩, hw⟩
  | pktM msL y msR W => obtain ⟨⟨n, hn⟩, hw⟩ := hr; exact ⟨⟨a + n, steps_seq h hn⟩, hw⟩
  | halt => obtain ⟨n, hn⟩ := hr; exact ⟨a + n, steps_seq_any h hn⟩
  | uncovered => trivial

/-- The gap meets nothing. -/
theorem gapEvent_nil_ok (msL : List Mark) (g W : Nat) (hL : leftOK g false msL)
    (hR : rightOK (g + 3) false W [] ∨ W = g + 2) : (gapEvent msL g [] W).ok (midCfg msL g [] W) := by
  have hb := leftOK_oneBefore hL
  by_cases hW : W = g + 2
  · subst hW
    simp only [gapEvent, if_true]
    obtain ⟨L', hL1⟩ := oneBefore_tail hb
    have hstart : midCfg msL g [] (g + 2)
        = ⟨cons false (cons false (buildL false g msL)), cons false (stripe true (g + 2 - (g + 3)) blank), .E⟩ := rfl
    have e : g + 2 - (g + 3) = 0 := by omega
    conv at hstart => rhs; rw [hL1, e, stripe_zero]
    have h₁ := gap_to_blankend L'
    rw [← hstart] at h₁
    have hb2 : build false (g + 1) [⟨.M, g + 3⟩] (g + 5)
        = cons true (cons false (cons true (cons true blank))) := by
      show stripe (!false) (g + 3 - (g + 1)) (cons true (cons true (stripe (!true) (g + 5 - (g + 3 + 2)) blank))) = _
      rw [show g + 3 - (g + 1) = 2 by omega, show g + 5 - (g + 3 + 2) = 0 by omega, stripe_zero]
      rfl
    have hok := pktFrom_ok msL g [⟨.M, g + 3⟩] (g + 5) L' hL hL1
      (by simp only [rightOK, mval, mlen]
          refine ⟨by omega, ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩, by omega,
            ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩⟩)
    rw [hb2] at hok
    exact GR.ok_seq h₁ hok
  · simp only [gapEvent, hW, if_false]
    have hR' : rightOK (g + 3) false W [] := by
      rcases hR with h | h
      · exact h
      · exact absurd h hW
    obtain ⟨h1, h2⟩ := hR'
    have hodd : (W - (g + 3)) % 2 = 1 := h2.mpr rfl
    obtain ⟨k, hk⟩ : ∃ k, W = g + 4 + 2 * k := ⟨(W - (g + 3)) / 2, by omega⟩
    subst hk
    simp only [GR.ok]
    refine ⟨⟨wallbounceSteps (k + 1) 0 + 13, ?_⟩, ?_, ?_⟩
    · have h := ev_gap_end' msL g k hb
      rw [show g + 4 + 2 * k - 3 = g + 2 * k + 1 by omega, show g + 4 + 2 * k + 1 = g + 2 * k + 5 by omega]
      exact h
    · rw [show g + 4 + 2 * k - 3 = g + 2 * k + 1 by omega]
      have := leftOK_succ (leftOK_add2k k hL)
      simpa using this
    · simp only [rightOK, mval, mlen]
      refine ⟨by omega, ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩, by omega,
        ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩⟩

/-- The gap meets a marker: swap or merge. -/
theorem gapEvent_M_ok (msL msR' : List Mark) (g p W : Nat) (hL : leftOK g false msL)
    (hR : rightOK (g + 3) false W (⟨.M, p⟩ :: msR')) :
    (gapEvent msL g (⟨.M, p⟩ :: msR') W).ok (midCfg msL g (⟨.M, p⟩ :: msR') W) := by
  have hb := leftOK_oneBefore hL
  have hg := oneBefore_pos hb
  obtain ⟨h1, h2, h3⟩ := hR
  simp only [mval, mlen] at h1 h2 h3
  have heven : (p - (g + 3)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
  have hnl : ¬ (p < g + 3) := by omega
  have hd2 : ¬ ((p - (g + 3)) % 2 = 1) := by omega
  simp only [gapEvent, hnl, hd2, if_false]
  by_cases hd4 : (p - (g + 3)) % 4 = 0
  · rw [if_pos hd4]
    obtain ⟨k, hk⟩ : ∃ k, p = g + 3 + 4 * k := ⟨(p - (g + 3)) / 4, by omega⟩
    subst hk
    by_cases hc : g + 3 + 4 * k - (g + 3) = 0 ∧ wallFreeB g msL = false
    · rw [if_pos hc]; trivial
    · rw [if_neg hc]
      have hk' : 1 ≤ k ∨ stripeBefore g msL := by
        by_cases hk0 : k = 0
        · right
          subst hk0
          have hw : wallFreeB g msL = true := by
            cases hw : wallFreeB g msL
            · exact absurd ⟨by omega, hw⟩ hc
            · rfl
          exact wallFreeB_stripeBefore hw
        · left; omega
      have e : (g + 3 + 4 * k - (g + 3)) / 2 = 2 * k := by omega
      rw [e]
      simp only [GR.ok, gapWF]
      refine ⟨⟨_, ev_swap' msL msR' g k W hb hk' (rightOK_zeroAfter h3)⟩, ?_, Or.inl ?_⟩
      · simp only [leftOK, mval, mlen]
        refine ⟨by omega, ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩, ?_⟩
        cases k with
        | zero =>
          have hs : stripeBefore g msL := by
            rcases hk' with hk1 | hs
            · omega
            · exact hs
          have hL2 : leftOK (g - 1 + 1) false msL := by rw [Nat.sub_add_cancel hg]; exact hL
          have := leftOK_pred hL2 (stripeBefore_endsBy' hs)
          simpa using this
        | succ k' =>
          have := leftOK_succ (leftOK_add2k k' hL)
          rw [show g + 2 * (k' + 1) - 1 = g + 2 * k' + 1 by omega]
          simpa using this
      · have h := rightOK_pred h3
        have h' : rightOK (g + 2 * k + 1 + 3 + 2 * k) false W msR' := by
          rw [show g + 2 * k + 1 + 3 + 2 * k = g + 3 + 4 * k + 1 by omega]
          simpa using h
        exact rightOK_sub2k k h'
  · rw [if_neg hd4]
    obtain ⟨k, hk⟩ : ∃ k, p = g + 3 + 4 * k + 2 := ⟨(p - (g + 3)) / 4, by omega⟩
    subst hk
    by_cases hd : g + 3 + 4 * k + 2 - (g + 3) = 2
    · rw [if_pos hd]
      have hk0 : k = 0 := by omega
      subst hk0
      obtain ⟨L', hL1⟩ := oneBefore_tail hb
      have h₁ := ev_merge_raw msL msR' g 0 W L' hL1 (rightOK_zeroAfter h3)
      simp only [rep, Nat.mul_zero, Nat.add_zero] at h₁
      refine GR.ok_seq h₁ (pktFrom_ok msL g (⟨.W, g + 4⟩ :: msR') W L' hL hL1 ?_)
      simp only [rightOK, mval, mlen]
      refine ⟨by omega, ⟨fun _ => trivial, fun _ => by omega⟩, ?_⟩
      have h := rightOK_pred h3
      simpa using h
    · rw [if_neg hd]
      have hk1 : 1 ≤ k := by omega
      have e₁ : g + (g + 3 + 4 * k + 2 - (g + 3)) / 2 - 2 = g + 2 * k - 1 := by omega
      have e₂ : g + (g + 3 + 4 * k + 2 - (g + 3)) / 2 + 3 = g + 2 * k + 4 := by omega
      rw [e₁, e₂]
      simp only [GR.ok]
      refine ⟨⟨_, ev_merge' msL msR' g k W hb (Or.inl hk1) (rightOK_zeroAfter h3)⟩, ?_, ?_⟩
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have := leftOK_succ (leftOK_add2k k' hL)
        rw [show g + 2 * (k' + 1) - 1 = g + 2 * k' + 1 by omega]
        simpa using this
      · simp only [rightOK, mval, mlen]
        refine ⟨by omega, ⟨fun _ => trivial, fun _ => by omega⟩, ?_⟩
        have h := rightOK_pred h3
        have h' : rightOK (g + 2 * k + 4 + 2 + 2 * k) false W msR' := by
          rw [show g + 2 * k + 4 + 2 + 2 * k = g + 3 + 4 * k + 2 + 1 by omega]
          simpa using h
        exact rightOK_sub2k k h'

theorem leftOK_pkt {g : Nat} {msL : List Mark} (k : Nat) (hL : leftOK g false msL) : leftOK (g + 2 * k + 1) true msL := by
  have := leftOK_succ (leftOK_add2k k hL)
  simpa using this

/-- The gap meets a wall: the shift that follows. -/
theorem gapEvent_W_ok (msL msR' : List Mark) (g w W : Nat) (hL : leftOK g false msL)
    (hR : rightOK (g + 3) false W (⟨.W, w⟩ :: msR')) :
    (gapEvent msL g (⟨.W, w⟩ :: msR') W).ok (midCfg msL g (⟨.W, w⟩ :: msR') W) := by
  have hb := leftOK_oneBefore hL
  have hR0 := hR
  obtain ⟨h1, h2, h3⟩ := hR
  simp only [mval, mlen] at h1 h2 h3
  have hodd : (w - (g + 3)) % 2 = 1 := by first | exact h2.mpr rfl | exact h2.mpr trivial
  obtain ⟨k, hk⟩ : ∃ k, w = g + 4 + 2 * k := ⟨(w - (g + 3)) / 2, by omega⟩
  subst hk
  have e3 : g + 4 + 2 * k - 3 = g + 2 * k + 1 := by omega
  cases msR' with
  | nil =>
    obtain ⟨h4, h5⟩ := h3
    have hodd2 : (W - (g + 4 + 2 * k + 2)) % 2 = 1 := by first | exact h5.mpr rfl | exact h5.mpr trivial
    obtain ⟨j, hj⟩ : ∃ j, W = g + 7 + 2 * k + 2 * j := ⟨(W - (g + 4 + 2 * k + 2)) / 2, by omega⟩
    subst hj
    simp only [gapEvent, GR.ok]
    rw [e3]
    refine ⟨⟨_, ev_gap_wall_blank' msL g k j hb⟩, leftOK_pkt k hL, ?_⟩
    simp only [rightOK, mval, mlen]
    refine ⟨by omega, ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩, by omega,
      ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩⟩
  | cons m₂ msR'' =>
    obtain ⟨t₂, p₂⟩ := m₂
    obtain ⟨h4, h5, h6⟩ := h3
    try dsimp only at h4 h5 h6
    cases t₂ with
    | M =>
      simp only [mval, mlen] at h5 h6
      have heven : (p₂ - (g + 4 + 2 * k + 2)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h5.mp h) (by decide))
      obtain ⟨j, hj⟩ : ∃ j, p₂ = g + 6 + 2 * k + 2 * j := ⟨(p₂ - (g + 4 + 2 * k + 2)) / 2, by omega⟩
      subst hj
      cases hf : freeAtB (g + 6 + 2 * k + 2 * j + 2) W msR'' with
      | false => simp only [gapEvent, hf, Bool.false_eq_true, if_false, GR.ok]
      | true =>
        simp only [gapEvent, hf, if_true, GR.ok, gapWF]
        refine ⟨⟨_, ev_gap_wall_marker' msL msR'' g k j W hb (freeAtB_iff.mp hf)⟩, ?_, ?_⟩
        · have := leftOK_add2k (3 + k + j) hL
          rw [show g + 6 + 2 * k + 2 * j = g + 2 * (3 + k + j) by omega]
          exact this
        · exact rightOK_freeAt_next h6 (freeAtB_iff.mp hf)
    | W =>
      simp only [mval, mlen] at h5 h6
      have hodd2 : (p₂ - (g + 4 + 2 * k + 2)) % 2 = 1 := by first | exact h5.mpr rfl | exact h5.mpr trivial
      obtain ⟨j, hj⟩ : ∃ j, p₂ = g + 7 + 2 * k + 2 * j := ⟨(p₂ - (g + 4 + 2 * k + 2)) / 2, by omega⟩
      subst hj
      cases hs : strictAfterB (g + 7 + 2 * k + 2 * j + 2) W msR'' with
      | false => simp only [gapEvent, hs, Bool.false_eq_true, if_false, GR.ok]
      | true =>
        simp only [gapEvent, hs, if_true, GR.ok]
        have hsa := strictAfterB_iff.mp hs
        rw [e3]
        refine ⟨⟨_, ev_gap_wall_wall' msL msR'' g k j W hb hsa⟩, leftOK_pkt k hL, ?_⟩
        simp only [rightOK, mval, mlen]
        refine ⟨by omega, ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩, ?_⟩
        have := rightOK_succ h6 hsa
        simpa using this
    | B =>
      simp only [mval, mlen] at h5 h6
      have heven : (p₂ - (g + 4 + 2 * k + 2)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h5.mp h) (by decide))
      obtain ⟨j, hj⟩ : ∃ j, p₂ = g + 6 + 2 * k + 2 * j := ⟨(p₂ - (g + 4 + 2 * k + 2)) / 2, by omega⟩
      subst hj
      by_cases hend : msR''.isEmpty = true ∧ W = g + 6 + 2 * k + 2 * j + 3
      · obtain ⟨he, hW⟩ := hend
        cases msR'' with
        | cons _ _ => simp at he
        | nil =>
          subst hW
          simp only [gapEvent, List.isEmpty_nil, and_self, if_true, GR.ok]
          have hcfg : midCfg msL g [⟨.W, g + 4 + 2 * k⟩, ⟨.B, g + 6 + 2 * k + 2 * j⟩] (g + 6 + 2 * k + 2 * j + 3)
              = midCfg msL g [⟨.W, g + 4 + 2 * k⟩, ⟨.B, g + 6 + 2 * k + 2 * j⟩] (g + 6 + 2 * k + 2 * j + 3 + 1) := by
            unfold midCfg; rw [build_pad _ _ _ _ hR0]
          have hev := ev_gap_wall_block' msL [] g k j (g + 6 + 2 * k + 2 * j + 3 + 1) hb
            (by simp only [strictAfter]; omega)
          have hfin : pktCfg msL (g + 2 * k + 1) [⟨.W, g + 6 + 2 * k + 2 * j + 2⟩] (g + 6 + 2 * k + 2 * j + 3 + 1)
              = pktCfg msL (g + 2 * k + 1) [] (g + 6 + 2 * k + 2 * j + 2) := by
            unfold pktCfg
            rw [show g + 6 + 2 * k + 2 * j + 3 + 1 = g + 6 + 2 * k + 2 * j + 2 + 2 by omega, build_trailing_wall]
          rw [hfin, ← hcfg] at hev
          rw [e3]
          refine ⟨⟨_, hev⟩, leftOK_pkt k hL, by omega, ⟨fun _ => rfl, fun _ => by omega⟩⟩
      cases hs : strictAfterB (g + 6 + 2 * k + 2 * j + 3) W msR'' with
      | false => simp only [gapEvent, if_neg hend, hs, Bool.false_eq_true, if_false, GR.ok]
      | true =>
        simp only [gapEvent, if_neg hend, hs, if_true, GR.ok]
        have hsa := strictAfterB_iff.mp hs
        rw [e3]
        refine ⟨⟨_, ev_gap_wall_block' msL msR'' g k j W hb hsa⟩, leftOK_pkt k hL, ?_⟩
        simp only [rightOK, mval, mlen]
        refine ⟨by omega, ⟨fun _ => trivial, fun _ => by omega⟩, ?_⟩
        have := rightOK_succ h6 hsa
        rw [show g + 6 + 2 * k + 2 * j + 2 + 2 = g + 6 + 2 * k + 2 * j + 3 + 1 by omega]
        simpa using this
    | G => simp only [gapEvent, GR.ok]

/-- The gap meets a block: the block acts as a wall one cell left while the gap sleeps. -/
theorem gapEvent_B_ok (msL msR' : List Mark) (g p W : Nat) (hL : leftOK g false msL)
    (hR : rightOK (g + 3) false W (⟨.B, p⟩ :: msR')) :
    (gapEvent msL g (⟨.B, p⟩ :: msR') W).ok (midCfg msL g (⟨.B, p⟩ :: msR') W) := by
  have hb := leftOK_oneBefore hL
  have hR0 := hR
  obtain ⟨h1, h2, h3⟩ := hR
  simp only [mval, mlen] at h1 h2 h3
  have heven : (p - (g + 3)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
  by_cases hlt : p < g + 5
  · simp only [gapEvent, hlt, if_true, GR.ok]
  · simp only [gapEvent, hlt, if_false]
    obtain ⟨m, hm⟩ : ∃ m, p = g + 5 + 2 * m := ⟨(p - (g + 5)) / 2, by omega⟩
    subst hm
    have hwL : leftOK (g + 5 + 2 * m) false (⟨.M, g + 5 + 2 * m - 2⟩ :: ⟨.G, g⟩ :: msL) := by
      simp only [leftOK, mval, mlen]
      refine ⟨by omega, ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩, by omega,
        ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩, hL⟩
    cases msR' with
    | nil =>
      obtain ⟨h4, h5⟩ := h3
      have heven2 : (W - (g + 5 + 2 * m + 3)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h5.mp h) (by decide))
      obtain ⟨j, hj⟩ : ∃ j, W = g + 8 + 2 * m + 2 * j := ⟨(W - (g + 5 + 2 * m + 3)) / 2, by omega⟩
      subst hj
      simp only [GR.ok, gapWF]
      have hm := ev_gap_block_blank' msL g m j hb
      rw [show g + 3 + 2 * m = g + 5 + 2 * m - 2 by omega,
        show g + 10 + 2 * m + 2 * j = g + 8 + 2 * m + 2 * j + 2 by omega] at hm
      refine ⟨⟨_, hm⟩, hwL, Or.inl ?_⟩
      simp only [rightOK, mval, mlen]
      refine ⟨by omega, ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩, by omega,
        ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩⟩
    | cons m₂ msR'' =>
      obtain ⟨t₂, p₂⟩ := m₂
      obtain ⟨h4, h5, h6⟩ := h3
      try dsimp only at h4 h5 h6
      cases t₂ with
      | M =>
        simp only [mval, mlen] at h5 h6
        have hodd : (p₂ - (g + 5 + 2 * m + 3)) % 2 = 1 := by first | exact h5.mpr rfl | exact h5.mpr trivial
        obtain ⟨j, hj⟩ : ∃ j, p₂ = g + 9 + 2 * m + 2 * j := ⟨(p₂ - (g + 5 + 2 * m + 3)) / 2, by omega⟩
        subst hj
        cases hf : freeAtB (g + 9 + 2 * m + 2 * j + 2) W msR'' with
        | false => simp only [hf, Bool.false_eq_true, if_false, GR.ok]
        | true =>
          simp only [hf, if_true, GR.ok, gapWF]
          have hm := ev_gap_block_marker' msL msR'' g m j W hb (freeAtB_iff.mp hf)
          rw [show g + 4 + 2 * m = g + 5 + 2 * m - 1 by omega] at hm
          refine ⟨⟨_, hm⟩, ?_, rightOK_freeAt_next h6 (freeAtB_iff.mp hf)⟩
          simp only [leftOK, mval, mlen]
          refine ⟨by omega, ⟨fun _ => trivial, fun _ => by omega⟩, by omega, ⟨fun _ => trivial, fun _ => by omega⟩, hL⟩
      | W =>
        simp only [mval, mlen] at h5 h6
        have heven2 : (p₂ - (g + 5 + 2 * m + 3)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h5.mp h) (by decide))
        obtain ⟨j, hj⟩ : ∃ j, p₂ = g + 8 + 2 * m + 2 * j := ⟨(p₂ - (g + 5 + 2 * m + 3)) / 2, by omega⟩
        subst hj
        cases hs : strictAfterB (g + 8 + 2 * m + 2 * j + 2) W msR'' with
        | false => simp only [hs, Bool.false_eq_true, if_false, GR.ok]
        | true =>
          simp only [hs, if_true, GR.ok, gapWF]
          have hsa := strictAfterB_iff.mp hs
          have hm := ev_gap_block_wall' msL msR'' g m j W hb hsa
          rw [show g + 3 + 2 * m = g + 5 + 2 * m - 2 by omega] at hm
          refine ⟨⟨_, hm⟩, hwL, Or.inl ?_⟩
          simp only [rightOK, mval, mlen]
          refine ⟨by omega, ⟨fun h => absurd h (by omega), fun h => absurd h (by decide)⟩, ?_⟩
          have := rightOK_succ h6 hsa
          simpa using this
      | B =>
        simp only [mval, mlen] at h5 h6
        have hodd : (p₂ - (g + 5 + 2 * m + 3)) % 2 = 1 := by first | exact h5.mpr rfl | exact h5.mpr trivial
        obtain ⟨j, hj⟩ : ∃ j, p₂ = g + 9 + 2 * m + 2 * j := ⟨(p₂ - (g + 5 + 2 * m + 3)) / 2, by omega⟩
        subst hj
        by_cases hend : msR''.isEmpty = true ∧ W = g + 9 + 2 * m + 2 * j + 3
        · obtain ⟨he, hW⟩ := hend
          cases msR'' with
          | cons _ _ => simp at he
          | nil =>
            subst hW
            simp only [List.isEmpty_nil, and_self, if_true, GR.ok, gapWF]
            have hcfg : midCfg msL g [⟨.B, g + 5 + 2 * m⟩, ⟨.B, g + 9 + 2 * m + 2 * j⟩] (g + 9 + 2 * m + 2 * j + 3)
                = midCfg msL g [⟨.B, g + 5 + 2 * m⟩, ⟨.B, g + 9 + 2 * m + 2 * j⟩] (g + 9 + 2 * m + 2 * j + 3 + 1) := by
              unfold midCfg; rw [build_pad _ _ _ _ hR0]
            have hev := ev_gap_block_block' msL [] g m j (g + 9 + 2 * m + 2 * j + 3 + 1) hb
              (by simp only [freeAt]; omega)
            have hfin : midCfg (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m)
                  [⟨.W, g + 9 + 2 * m + 2 * j + 2⟩] (g + 9 + 2 * m + 2 * j + 3 + 1)
                = midCfg (⟨.M, g + 5 + 2 * m - 2⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m) [] (g + 9 + 2 * m + 2 * j + 2) := by
              unfold midCfg
              rw [show g + 9 + 2 * m + 2 * j + 3 + 1 = g + 9 + 2 * m + 2 * j + 2 + 2 by omega, build_trailing_wall,
                show g + 5 + 2 * m - 2 = g + 3 + 2 * m by omega]
            rw [hfin, ← hcfg] at hev
            refine ⟨⟨_, hev⟩, hwL, Or.inl ⟨by omega, ⟨fun _ => rfl, fun _ => by omega⟩⟩⟩
        cases hs : strictAfterB (g + 9 + 2 * m + 2 * j + 3) W msR'' with
        | false => simp only [if_neg hend, hs, Bool.false_eq_true, if_false, GR.ok]
        | true =>
          simp only [if_neg hend, hs, if_true, GR.ok, gapWF]
          have hsa := strictAfterB_iff.mp hs
          have hm := ev_gap_block_block' msL msR'' g m j W hb (strictAfter_freeAt hsa)
          rw [show g + 3 + 2 * m = g + 5 + 2 * m - 2 by omega] at hm
          refine ⟨⟨_, hm⟩, hwL, Or.inl ?_⟩
          simp only [rightOK, mval, mlen]
          refine ⟨by omega, ⟨fun _ => trivial, fun _ => by omega⟩, ?_⟩
          have := rightOK_succ h6 hsa
          rw [show g + 9 + 2 * m + 2 * j + 2 + 2 = g + 9 + 2 * m + 2 * j + 3 + 1 by omega]
          simpa using this
      | G => simp only [GR.ok]

/-- One event of the gap phase, from a well-formed gap configuration. -/
theorem gapEvent_ok (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat) (h : gapWF msL g msR W) :
    (gapEvent msL g msR W).ok (midCfg msL g msR W) := by
  obtain ⟨hL, hR⟩ := h
  cases msR with
  | nil =>
    apply gapEvent_nil_ok msL g W hL
    rcases hR with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  | cons m msR' =>
    have hR' : rightOK (g + 3) false W (m :: msR') := by
      rcases hR with h | ⟨h, -⟩
      · exact h
      · cases h
    obtain ⟨t, p⟩ := m
    cases t with
    | M => exact gapEvent_M_ok msL msR' g p W hL hR'
    | W => exact gapEvent_W_ok msL msR' g p W hL hR'
    | B => exact gapEvent_B_ok msL msR' g p W hL hR'
    | G => simp only [gapEvent, GR.ok]

/-- Continue the gap phase from a woken gap; pass anything else through. -/
def PR'.cont (k : List Mark → Nat → List Mark → Nat → PR') : PR' → PR'
  | .gap msL g msR W => k msL g msR W
  | r => r

/-- The round from a gap configuration: events until a packet ends the round; `fuel` bounds the number of events. -/
def roundZ : Nat → List Mark → Nat → List Mark → Nat → PR'
  | 0, _, _, _, _ => .uncovered
  | fuel + 1, msL, g, msR, W =>
    match gapEvent msL g msR W with
    | .gap msL' g' msR' W' => roundZ fuel msL' g' msR' W'
    | .pkt msL' x msR' W' => (pktBack msL' x msR' W').cont (roundZ fuel)
    | .pktM msL' y msR' W' => (pktLand msL' y msR' W').cont (roundZ fuel)
    | .halt => .halt
    | .uncovered => .uncovered

theorem cont_ne_uncovered {k : List Mark → Nat → List Mark → Nat → PR'} {r : PR'} (h : r.cont k ≠ .uncovered) :
    r ≠ .uncovered := by
  intro hr; rw [hr] at h; exact h rfl

/-- The round theorem: from a well-formed gap configuration, the machine reaches the configuration `roundZ`
computes (a round start, or a woken gap further on), which is well formed, or halts when `roundZ` says so. -/
theorem roundZ_run (fuel : Nat) : ∀ (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat), gapWF msL g msR W →
    roundZ fuel msL g msR W ≠ .uncovered →
    ∃ n, steps n (midCfg msL g msR W) = (roundZ fuel msL g msR W).cfg ∧ (roundZ fuel msL g msR W).wf := by
  induction fuel with
  | zero => intro _ _ _ _ _ h; exact absurd rfl h
  | succ fuel ih =>
    intro msL g msR W hwf hnu
    have hok := gapEvent_ok msL g msR W hwf
    simp only [roundZ] at hnu ⊢
    cases hev : gapEvent msL g msR W with
    | gap msL' g' msR' W' =>
      rw [hev] at hok hnu
      try dsimp only at hnu ⊢
      obtain ⟨⟨n₁, h₁⟩, hwf'⟩ := hok
      obtain ⟨n₂, h₂, hw⟩ := ih msL' g' msR' W' hwf' hnu
      exact ⟨n₁ + n₂, steps_seq_any h₁ h₂, hw⟩
    | pkt msL' x msR' W' =>
      rw [hev] at hok hnu
      try dsimp only at hnu ⊢
      obtain ⟨⟨n₁, h₁⟩, hL', hR'⟩ := hok
      have hnu' := cont_ne_uncovered hnu
      obtain ⟨n₂, h₂⟩ := pktBack_run msL' x msR' W' hL' hR' hnu'
      have hw := pktBack_wf msL' x msR' W' hL' hR'
      cases hpb : pktBack msL' x msR' W' with
      | gap msL'' g'' msR'' W'' =>
        rw [hpb] at h₂ hw hnu
        simp only [PR'.cont] at hnu ⊢
        simp only [PR'.cfg] at h₂
        obtain ⟨n₃, h₃, hw₃⟩ := ih msL'' g'' msR'' W'' ⟨hw.1, Or.inl hw.2⟩ hnu
        exact ⟨n₁ + (n₂ + n₃), steps_seq_any h₁ (steps_seq_any h₂ h₃), hw₃⟩
      | newRound ms W'' =>
        rw [hpb] at h₂ hw
        exact ⟨n₁ + n₂, steps_seq_any h₁ h₂, hw⟩
      | halt =>
        rw [hpb] at h₂ hw
        exact ⟨n₁ + n₂, steps_seq_any h₁ h₂, hw⟩
      | uncovered => exact absurd hpb hnu'
    | pktM msL' y msR' W' =>
      rw [hev] at hok hnu
      try dsimp only at hnu ⊢
      obtain ⟨⟨n₁, h₁⟩, hL', hR'⟩ := hok
      have hnu' := cont_ne_uncovered hnu
      obtain ⟨n₂, h₂⟩ := pktLand_run msL' y msR' W' hL' hR' hnu'
      have hw := pktLand_wf msL' y msR' W' hL' hR'
      cases hpb : pktLand msL' y msR' W' with
      | gap msL'' g'' msR'' W'' =>
        rw [hpb] at h₂ hw hnu
        simp only [PR'.cont] at hnu ⊢
        simp only [PR'.cfg] at h₂
        obtain ⟨n₃, h₃, hw₃⟩ := ih msL'' g'' msR'' W'' ⟨hw.1, Or.inl hw.2⟩ hnu
        exact ⟨n₁ + (n₂ + n₃), steps_seq_any h₁ (steps_seq_any h₂ h₃), hw₃⟩
      | newRound ms W'' =>
        rw [hpb] at h₂ hw
        exact ⟨n₁ + n₂, steps_seq_any h₁ h₂, hw⟩
      | halt =>
        rw [hpb] at h₂ hw
        exact ⟨n₁ + n₂, steps_seq_any h₁ h₂, hw⟩
      | uncovered => exact absurd hpb hnu'
    | halt =>
      rw [hev] at hok hnu
      try dsimp only at hnu ⊢
      obtain ⟨n, hn⟩ := hok
      exact ⟨n, hn, trivial⟩
    | uncovered => rw [hev] at hnu; exact absurd rfl hnu

/-- A well-formed round start: the gap at 1 and the marks `ms` beyond it, with correct stripes up to the width. -/
def roundWF (ms : List Mark) (W : Nat) : Prop := rightOK 4 false W ms

/-- **The round theorem.** From a well-formed round start, the machine reaches the next round start that the mark
model computes (and it is well formed), or halts when the model says so; the model's `uncovered` makes no claim. -/
theorem round_run (fuel : Nat) (ms : List Mark) (W : Nat) (h : roundWF ms W)
    (hnu : roundZ fuel [] 1 ms W ≠ .uncovered) :
    ∃ n, steps n (roundStart ms W) = (roundZ fuel [] 1 ms W).cfg ∧ (roundZ fuel [] 1 ms W).wf := by
  have := roundZ_run fuel [] 1 ms W ⟨⟨fun _ => rfl, fun _ => rfl⟩, Or.inl h⟩ hnu
  rwa [roundStart_eq_mid]

/-- Several rounds, from a round start. -/
def roundsZ (fuel : Nat) : Nat → List Mark → Nat → PR'
  | 0, ms, W => .newRound ms W
  | n + 1, ms, W =>
    match roundZ fuel [] 1 ms W with
    | .newRound ms' W' => roundsZ fuel n ms' W'
    | r => r

theorem rounds_run (fuel n : Nat) : ∀ (ms : List Mark) (W : Nat), roundWF ms W → roundsZ fuel n ms W ≠ .uncovered →
    ∃ k, steps k (roundStart ms W) = (roundsZ fuel n ms W).cfg ∧ (roundsZ fuel n ms W).wf := by
  induction n with
  | zero => intro ms W h _; exact ⟨0, rfl, h⟩
  | succ n ih =>
    intro ms W h hnu
    simp only [roundsZ] at hnu ⊢
    have hnu1 : roundZ fuel [] 1 ms W ≠ .uncovered := by
      intro h1; rw [h1] at hnu; exact hnu rfl
    obtain ⟨k₁, h₁, hw₁⟩ := round_run fuel ms W h hnu1
    generalize roundZ fuel [] 1 ms W = r at h₁ hw₁ hnu hnu1 ⊢
    cases r with
    | newRound ms' W' =>
      obtain ⟨k₂, h₂, hw₂⟩ := ih ms' W' hw₁ hnu
      exact ⟨k₁ + k₂, steps_seq_any h₁ h₂, hw₂⟩
    | gap msL g msR W' => exact ⟨k₁, h₁, hw₁⟩
    | halt => exact ⟨k₁, h₁, hw₁⟩
    | uncovered => exact absurd rfl hnu1

/-! ## From blank tape -/

/-- The machine started on blank tape in state A reaches the first round start, the gap at 1 and width 5
(`1 0 0 0 1`, head on cell 3 in state E), after 17 steps. -/
theorem first_round_start : steps 17 ⟨blank, blank, .A⟩ = some (roundStart [] 5) := by
  have h : roundStart [] 5 = ⟨cons false (cons false (cons true blank)), cons false (cons true blank), .E⟩ := rfl
  have h17 : steps 17 ⟨blank, blank, .A⟩
      = some ⟨cons false (cons false (cons true blank)), cons false (cons true (cons false blank)), .E⟩ := rfl
  rw [h, h17, cons_false_blank]

theorem first_round_start_wf : roundWF [] 5 := ⟨by omega, ⟨fun _ => rfl, fun _ => rfl⟩⟩

/-- **The mark model is sound for the machine from blank tape.**  For any number of rounds `n`, if the zipper model
`roundsZ` run for `n` rounds from the first round start does not report `uncovered`, then the machine started on
blank tape reaches exactly the configuration it computes — the round start after `n` rounds, a gap in the middle of
a round, or a halt (`steps … = none`). -/
theorem blank_rounds (fuel n : Nat) (hnu : roundsZ fuel n [] 5 ≠ .uncovered) :
    ∃ k, steps k ⟨blank, blank, .A⟩ = (roundsZ fuel n [] 5).cfg := by
  obtain ⟨k, hk, -⟩ := rounds_run fuel n [] 5 first_round_start_wf hnu
  exact ⟨17 + k, steps_seq_any first_round_start hk⟩

end BB6
