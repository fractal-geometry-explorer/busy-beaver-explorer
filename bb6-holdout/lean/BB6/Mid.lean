import BB6.Model

/-!
# Configurations in the middle of a round, and the marker events at the level of positions

A round in progress is either a gap travelling right (head on the gap's last cell, state E) or a packet travelling
left (head on the packet's first cell, state A).  `buildL next pos msL` is the tape left of cell `pos`, nearest cell
first, given the marks `msL` to the left (nearest first) and the value `next` of the cell at `pos`; the stripe
between a mark and `pos` is read right to left, so it starts with `!next`.

* `midCfg msL g msR W`: the gap at `g` (cells g, g+1, g+2), head on g+2 in state E, marks `msL` to the left and
  `msR` to the right, width `W`.  `roundStart ms W = midCfg [] 1 ms W`.
* `pktCfg msL x msR W`: the packet `1 1` at cells x, x+1 with the head on x in state A.  To the right of a packet the
  stripe starts with `1` (what CARRY leaves behind), so the packet counts as a 0-mark for the parity of that stripe.

The two marker events (the `.M` case of `Model.event`) hold for every such configuration whose gap is preceded by
at least one stripe cell and whose marker is followed by at least one stripe cell or is the end marker:

* `ev_swap`:  marker at g + 3 + 4k      →  marker at g + 2k − 1, gap at g + 2k + 1 (6k² + 24k + 21 steps);
* `ev_merge`: marker at g + 3 + 4k + 2  →  packet at g + 2k − 1, wall at g + 2k + 4 (6k² + 30k + 31 steps).
-/

namespace BB6

/-- The tape left of `pos`, nearest cell first, with the marks `msL` (nearest first) and the cell at `pos` of value
`next`. -/
def buildL (next : Bool) (pos : Nat) : List Mark → Tape
  | [] => stripe (!next) pos blank
  | m :: ms => stripe (!next) (pos - (m.p + mlen m.t)) (app (mcells m.t).reverse (buildL (mval m.t) m.p ms))

def midCfg (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat) : Cfg :=
  ⟨cons false (cons false (buildL false g msL)), cons false (build false (g + 3) msR W), .E⟩

def pktCfg (msL : List Mark) (x : Nat) (msR : List Mark) (W : Nat) : Cfg :=
  ⟨buildL true x msL, cons true (cons true (build false (x + 2) msR W)), .A⟩

theorem roundStart_eq_mid (ms : List Mark) (W : Nat) : roundStart ms W = midCfg [] 1 ms W := rfl

/-- The stripe just left of `g` is nonempty: the first mark of `msL` ends before `g` (or there is none and g ≥ 1). -/
def stripeBefore (g : Nat) : List Mark → Prop
  | [] => 1 ≤ g
  | m :: _ => m.p + mlen m.t < g

/-- Moving the point `g` right by 2k − 1 cells into the stripe while the cell at the point changes from 0 to 1: the
tape left of the new point reads `(01)^k` nearest first, then what was left of `g` without its first cell. -/
theorem buildL_shift (msL : List Mark) (g : Nat) (hs : stripeBefore g msL) (k : Nat) :
    ∃ L', buildL false g msL = cons true L' ∧ buildL true (g + 2 * k - 1) msL = rep k [false, true] L' := by
  cases msL with
  | nil =>
    simp only [stripeBefore] at hs
    obtain ⟨n, hn⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
    subst hn
    refine ⟨stripe false n blank, rfl, ?_⟩
    have e : n + 1 + 2 * k - 1 = 2 * k + n := by omega
    show stripe (!true) (n + 1 + 2 * k - 1) blank = _
    rw [e, stripe_two_add]
    rfl
  | cons m ms =>
    simp only [stripeBefore] at hs
    obtain ⟨n, hn⟩ : ∃ n, g - (m.p + mlen m.t) = n + 1 := ⟨g - (m.p + mlen m.t) - 1, by omega⟩
    refine ⟨stripe false n (app (mcells m.t).reverse (buildL (mval m.t) m.p ms)), ?_, ?_⟩
    · show stripe (!false) (g - (m.p + mlen m.t)) _ = _
      rw [hn]
      rfl
    · have e : g + 2 * k - 1 - (m.p + mlen m.t) = 2 * k + n := by omega
      show stripe (!true) (g + 2 * k - 1 - (m.p + mlen m.t)) _ = _
      rw [e, stripe_two_add]
      rfl

/-- The marker ending at `p + 1` is followed by a stripe cell, or is the end marker (p + 2 = W). -/
def stripeAfter (p W : Nat) : List Mark → Prop
  | [] => p + 2 ≤ W
  | m :: _ => p + 2 < m.p

/-- Right of a marker ending at p + 1 the tape starts with a 0 (a stripe cell, or blank).  Moving the start point
2k + 1 cells left, onto the last stripe cell before the marker's old place, reads `(10)^(k+1)` and then what followed
that first 0. -/
theorem build_shift (msR : List Mark) (p W : Nat) (hs : stripeAfter p W msR) (k : Nat) (hk : 2 * k + 1 ≤ p + 2) :
    ∃ R', build true (p + 2) msR W = cons false R' ∧
      build false (p + 2 - (2 * k + 1)) msR W = rep (k + 1) [true, false] R' := by
  cases msR with
  | nil =>
    simp only [stripeAfter] at hs
    cases Nat.lt_or_ge (p + 2) W with
    | inl hlt =>
      obtain ⟨n, hn⟩ : ∃ n, W - (p + 2) = n + 1 := ⟨W - (p + 2) - 1, by omega⟩
      refine ⟨stripe true n blank, ?_, ?_⟩
      · show stripe (!true) (W - (p + 2)) blank = _
        rw [hn]
        rfl
      · have e : W - (p + 2 - (2 * k + 1)) = 2 * (k + 1) + n := by omega
        show stripe (!false) (W - (p + 2 - (2 * k + 1))) blank = _
        rw [e, stripe_two_add]
        rfl
    | inr hge =>
      have hW : W = p + 2 := by omega
      subst hW
      refine ⟨blank, ?_, ?_⟩
      · show stripe (!true) (p + 2 - (p + 2)) blank = _
        rw [Nat.sub_self, stripe_zero, cons_false_blank]
      · have e : p + 2 - (p + 2 - (2 * k + 1)) = 2 * k + 1 := by omega
        show stripe (!false) (p + 2 - (p + 2 - (2 * k + 1))) blank = _
        rw [e, stripe_two_add, ← rep_cons2 k true false blank, cons_false_blank]
        rfl
  | cons m ms =>
    simp only [stripeAfter] at hs
    obtain ⟨n, hn⟩ : ∃ n, m.p - (p + 2) = n + 1 := ⟨m.p - (p + 2) - 1, by omega⟩
    refine ⟨stripe true n (app (mcells m.t) (build (mval m.t) (m.p + mlen m.t) ms W)), ?_, ?_⟩
    · show stripe (!true) (m.p - (p + 2)) _ = _
      rw [hn]
      rfl
    · have e : m.p - (p + 2 - (2 * k + 1)) = 2 * (k + 1) + n := by omega
      show stripe (!false) (m.p - (p + 2 - (2 * k + 1))) _ = _
      rw [e, stripe_two_add]
      rfl

/-- The swap event at positions: a gap at g meets a marker at g + 3 + 4k. -/
theorem ev_swap (msL msR : List Mark) (g k W : Nat) (hL : stripeBefore g msL) (hR : stripeAfter (g + 3 + 4 * k) W msR) :
    steps (bounceSteps k 0 + 21) (midCfg msL g (⟨.M, g + 3 + 4 * k⟩ :: msR) W)
      = some (midCfg (⟨.M, g + 2 * k - 1⟩ :: msL) (g + 2 * k + 1) msR W) := by
  have hg : 1 ≤ g := by cases msL <;> simp only [stripeBefore] at hL <;> omega
  obtain ⟨L', hL1, hL2⟩ := buildL_shift msL g hL k
  obtain ⟨R', hR1, hR2⟩ := build_shift msR (g + 3 + 4 * k) W hR k (by omega)
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

/-- The merge event at positions: a gap at g meets a marker at g + 3 + 4k + 2. -/
theorem ev_merge (msL msR : List Mark) (g k W : Nat) (hL : stripeBefore g msL) (hR : stripeAfter (g + 3 + 4 * k + 2) W msR) :
    steps (bounceSteps k 1 + 31) (midCfg msL g (⟨.M, g + 3 + 4 * k + 2⟩ :: msR) W)
      = some (pktCfg msL (g + 2 * k - 1) (⟨.W, g + 2 * k + 4⟩ :: msR) W) := by
  have hg : 1 ≤ g := by cases msL <;> simp only [stripeBefore] at hL <;> omega
  obtain ⟨L', hL1, hL2⟩ := buildL_shift msL g hL k
  obtain ⟨R', hR1, hR2⟩ := build_shift msR (g + 3 + 4 * k + 2) W hR k (by omega)
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

end BB6
