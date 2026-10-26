import BB6.Gap2

/-!
# The gap meets a block, at the level of positions

A gap at `g` meets a block at `p = g + 5 + 2m` (an even, nonempty stripe between them).  The block rules of
`Rules.lean` cover what happens next in one go: the gap stays asleep, and a shift runs from the block to the next
mark:

* a marker at `q` (2j + 1 stripe cells after the block): the block becomes a wall at p − 1 and a gap opens at q
  (`ev_gap_block_marker`);
* a wall at `w` (2j stripe cells after the block): the wall becomes a block, a marker forms at p − 2 and the gap
  wakes at p (`ev_gap_block_wall`);
* a block at `r` (2j + 1 cells): the block becomes a wall at r + 2, a marker forms at p − 2 and the gap wakes at p
  (`ev_gap_block_block`);
* blank tape (2j stripe cells, W = p + 3 + 2j): an end marker forms at W and the width becomes W + 2; a marker forms
  at p − 2 and the gap wakes at p (`ev_gap_block_blank`).

A point the last case makes precise: the width `W` of a mark state is the first cell of the all-zero tail, so the
stripe before it ends with a 1 — an even number of cells after a 1-mark (marker, block), an odd number after a 0-mark
(gap, wall).  `build` does not enforce this (`build b q [] (W + 1)` with a 0 at cell W is the same tape as
`build b q [] W`), so a mark state with the wrong parity at the end denotes a tape whose width is one less than it
says, and the end-of-tape rows of the model (marker at W, width W + 2 after a shift; marker at W + 1, width W + 3
when the gap itself runs out of marks) are stated for the canonical width.  The round theorem will carry this as part
of the well-formedness of a mark state.
-/

namespace BB6

/-- Cell `q` is a stripe cell or blank: the next mark (if any) starts after it, and it is within or at the width. -/
def freeAt (q W : Nat) : List Mark → Prop
  | [] => q ≤ W
  | m :: _ => q < m.p

theorem stripeAfter_freeAt {p W : Nat} {msR : List Mark} (h : stripeAfter p W msR) : freeAt (p + 2) W msR := by
  cases msR <;> simp only [stripeAfter, freeAt] at h ⊢ <;> omega

theorem strictAfter_freeAt {q W : Nat} {msR : List Mark} (h : strictAfter q W msR) : freeAt q W msR := by
  cases msR <;> simp only [strictAfter, freeAt] at h ⊢ <;> omega

/-- Reading the tape from a free cell `q` after a 1: a 0, then the rest read after a 0. -/
theorem build_free (msR : List Mark) (q W : Nat) (h : freeAt q W msR) :
    build true q msR W = cons false (build false (q + 1) msR W) := by
  cases msR with
  | nil =>
    simp only [freeAt] at h
    cases Nat.lt_or_ge q W with
    | inl hlt =>
      have e : W - q = (W - (q + 1)) + 1 := by omega
      show stripe (!true) (W - q) blank = cons false (stripe (!false) (W - (q + 1)) blank)
      rw [e]
      rfl
    | inr hge =>
      have hW : W = q := by omega
      rw [hW]
      show stripe (!true) (q - q) blank = cons false (stripe (!false) (q - (q + 1)) blank)
      rw [Nat.sub_self, Nat.sub_eq_zero_of_le (Nat.le_succ q), stripe_zero, stripe_zero, cons_false_blank]
  | cons m ms =>
    simp only [freeAt] at h
    have e : m.p - q = (m.p - (q + 1)) + 1 := by omega
    show stripe (!true) (m.p - q) _ = cons false (stripe (!false) (m.p - (q + 1)) _)
    rw [e]
    rfl

/-- Reading the tape from a stripe cell `q` strictly before the next mark and the width: one cell, then the rest. -/
theorem build_step (msR : List Mark) (b : Bool) (q W : Nat) (h : strictAfter q W msR) :
    build b q msR W = cons (!b) (build (!b) (q + 1) msR W) := by
  cases msR with
  | nil =>
    simp only [strictAfter] at h
    have e : W - q = (W - (q + 1)) + 1 := by omega
    show stripe (!b) (W - q) blank = cons (!b) (stripe (!!b) (W - (q + 1)) blank)
    rw [e]
    rfl
  | cons m ms =>
    simp only [strictAfter] at h
    have e : m.p - q = (m.p - (q + 1)) + 1 := by omega
    show stripe (!b) (m.p - q) _ = cons (!b) (stripe (!!b) (m.p - (q + 1)) _)
    rw [e]
    rfl

theorem stripe_false_odd' (k : Nat) (s : Tape) : stripe false (2 * k + 1) s = cons false (rep k [true, false] s) := by
  rw [stripe_false_odd, rep_shift']

theorem rep_two (j : Nat) (s : Tape) :
    cons true (cons false (cons true (cons false (rep j [true, false] s)))) = rep (j + 2) [true, false] s := rfl

/-- The tape left of the woken gap at p = g + 5 + 2m: the new marker at p − 2, the sleeping gap at g, and what
was left of g. -/
theorem buildL_woken (msL : List Mark) (g m : Nat) (L' : Tape) (hL : buildL false g msL = cons true L') :
    buildL false (g + 5 + 2 * m) (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL)
      = cons true (rep (m + 1) [true, false] (cons false (cons false (cons true L')))) := by
  have h : buildL false (g + 5 + 2 * m) (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL)
      = stripe true (g + 5 + 2 * m - (g + 3 + 2 * m + 2)) (cons true (cons true
          (stripe false (g + 3 + 2 * m - (g + 3)) (cons false (cons false (cons false (buildL false g msL))))))) := rfl
  have e₁ : g + 5 + 2 * m - (g + 3 + 2 * m + 2) = 0 := by omega
  have e₂ : g + 3 + 2 * m - (g + 3) = 2 * m := by omega
  rw [h, e₁, stripe_zero, e₂, stripe_even, Bool.not_false, hL,
    rep_shift' true false m (cons false (cons false (cons false (cons true L')))),
    rep_cons2 m true false (cons false (cons false (cons true L')))]

/-- Gap meets block, shift meets marker: the block becomes a wall at p − 1, a gap opens at the marker. -/
theorem ev_gap_block_marker (msL msR : List Mark) (g m j W : Nat) (hb : stripeBefore g msL)
    (hf : freeAt (g + 9 + 2 * m + 2 * j + 2) W msR) :
    steps (2 * j + 2 * (m + 1) + 9)
        (midCfg msL g (⟨.B, g + 5 + 2 * m⟩ :: ⟨.M, g + 9 + 2 * m + 2 * j⟩ :: msR) W)
      = some (midCfg (⟨.W, g + 4 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 9 + 2 * m + 2 * j) msR W) := by
  obtain ⟨L', hL1, -⟩ := buildL_shift msL g hb 0
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

/-- Gap meets block, shift meets wall: the wall becomes a block; a marker forms at p − 2 and the gap wakes at p. -/
theorem ev_gap_block_wall (msL msR : List Mark) (g m j W : Nat) (hb : stripeBefore g msL)
    (ha : strictAfter (g + 8 + 2 * m + 2 * j + 2) W msR) :
    steps (6 * j + 2 * (m + 1) + 17)
        (midCfg msL g (⟨.B, g + 5 + 2 * m⟩ :: ⟨.W, g + 8 + 2 * m + 2 * j⟩ :: msR) W)
      = some (midCfg (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m) (⟨.B, g + 8 + 2 * m + 2 * j⟩ :: msR) W) := by
  obtain ⟨L', hL1, -⟩ := buildL_shift msL g hb 0
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

/-- Gap meets block, shift meets a second block: it becomes a wall two cells further right; a marker forms at p − 2
and the gap wakes at p. -/
theorem ev_gap_block_block (msL msR : List Mark) (g m j W : Nat) (hb : stripeBefore g msL)
    (hf : freeAt (g + 9 + 2 * m + 2 * j + 3) W msR) :
    steps (6 * j + 2 * (m + 1) + 23)
        (midCfg msL g (⟨.B, g + 5 + 2 * m⟩ :: ⟨.B, g + 9 + 2 * m + 2 * j⟩ :: msR) W)
      = some (midCfg (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m) (⟨.W, g + 9 + 2 * m + 2 * j + 2⟩ :: msR) W) := by
  obtain ⟨L', hL1, -⟩ := buildL_shift msL g hb 0
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

/-- Gap meets block, shift reaches blank tape (W = p + 3 + 2j, an even stripe after the block): an end marker forms
at W, the width becomes W + 2; a marker forms at p − 2 and the gap wakes at p. -/
theorem ev_gap_block_blank (msL : List Mark) (g m j : Nat) (hb : stripeBefore g msL) :
    steps (6 * j + 2 * (m + 1) + 17) (midCfg msL g [⟨.B, g + 5 + 2 * m⟩] (g + 8 + 2 * m + 2 * j))
      = some (midCfg (⟨.M, g + 3 + 2 * m⟩ :: ⟨.G, g⟩ :: msL) (g + 5 + 2 * m) [⟨.M, g + 8 + 2 * m + 2 * j⟩]
          (g + 10 + 2 * m + 2 * j)) := by
  obtain ⟨L', hL1, -⟩ := buildL_shift msL g hb 0
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

end BB6
