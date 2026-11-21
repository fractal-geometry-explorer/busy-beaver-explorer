import Pascal

/-!
# A frozen block of length 2 is absorbed

At a right turn the head (in E) is on the first block of the frozen tape.  `Pascal.lean` treats blocks of 3 or more
cells (a bounce takes 2 of them) and odd blocks (they end in a halt).  Here the block has 2 cells and the next block has
`4k + 1`: frozen tape `1 1 0 1^(4k+1) 0 1 R`.

`absorb`: whatever the zone `ws` and its prefix, the bounce runs as usual, then F runs right over the next block and
turns on the block after it.  The zone becomes `tmap ws`, then `k` letters `v`, then one `u` (nearest the head), still a
clean zone, and the head is in E on the rest of the third block (one cell shorter).  So the zone stays clean, and the
frozen tape loses its first two blocks and one cell.

`absorb3`: if the middle block has `4k + 3` cells instead, the zone comes out two cells out of step: the clean zone
`tmap ws`, `v^(k+1)`, then a *wall* `1 0` next to the head.  `wbounce`: a bounce against a walled zone is the same running
XOR with a `0` appended instead of a `1` (`smap`), and the wall stays.  So a wall, once made, rides at the right end of the
zone while blocks of 3 or more cells are eaten, and an odd block still halts (`halts_of_odd_wall`).  (Absorption with a wall present mixes the wall into the zone; not
treated here.)
-/

namespace H75625

open TM

theorem zl_append (xs ys : List Bool) (S : Tape) : zl (xs ++ ys) S = zl xs (zl ys S) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, zl, ih]

theorem zl_replicate (k : Nat) (S : Tape) : zl (List.replicate k false) S = rep k [true, true, true, true] S := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, zl, lt, ih, rep_succ]

/-- **Absorption.**  From a right turn with zone `ws` (prefix `p`) and frozen tape `1 1 0 1^(4k+1) 0 1 R`, the machine
comes to E reading `R` with the clean zone `tmap ws`, `v^k`, `u` (prefix `npre p ws`). -/
theorem absorb (ws : List Bool) (p : Bool) (k : Nat) (R : Tape) : ∃ n,
    steps n ⟨zl ws (pre p),
        cons true (cons true (cons false (rep k [true, true, true, true] (cons true (cons false (cons true R)))))), .E⟩ =
      some ⟨zl (true :: (List.replicate k false ++ tmap ws)) (pre (npre p ws)), R, .E⟩ := by
  -- the frozen tape after the first two cells
  let X := rep k [true, true, true, true] (cons true (cons false (cons true R)))
  have h0 : steps 1 ⟨zl ws (pre p), cons true (cons true (cons false X)), .E⟩ =
      some (onL (zl ws (pre p)) (cons false (cons true (cons false X))) (pst true)) := rfl
  have h1 := sweep ws (pre p) true (cons false (cons true (cons false X)))
  have h2 := lend p (par true ws) (sweepR true ws (cons false (cons true (cons false X))))
  have h3 := rsweep ws true (app [true, true] (pre (bne p (par true ws)))) (cons false (cons true (cons false X)))
  -- write RL for the tape the right sweep leaves on the left
  generalize hRL : rsweepL true ws (app [true, true] (pre (bne p (par true ws)))) = RL at h3
  -- F> 0 1 0: F writes 1, A writes 0, E writes 1 and F starts over the next block
  have h4 : steps 3 ⟨RL, cons false (cons true (cons false X)), .F⟩ =
      some ⟨cons true (cons false (cons true RL)), X, .F⟩ := rfl
  -- F crosses 1111 k times
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, true, true, true] R, .F⟩ =
      some ⟨app [] (app [true, true, true, true] L), R, .F⟩ := fun _ _ => rfl
  have h5 := cross_r trans c0 k (cons true (cons false (cons true RL))) (cons true (cons false (cons true R)))
  -- F> 1 0 1: F keeps the 1, writes 1 on the 0, A writes 0 on the first cell of the third block, E reads R
  have h6 : steps 3 ⟨app [] (rep k [true, true, true, true] (cons true (cons false (cons true RL)))),
        cons true (cons false (cons true R)), .F⟩ =
      some ⟨cons false (cons true (cons true (rep k [true, true, true, true] (cons true (cons false (cons true RL)))))),
        R, .E⟩ := rfl
  have e : cons false (cons true (cons true (rep k [true, true, true, true] (cons true (cons false (cons true RL)))))) =
      zl (true :: (List.replicate k false ++ tmap ws)) (pre (npre p ws)) := by
    have z : cons false (cons true RL) = zl (tmap ws) (pre (npre p ws)) := by
      rw [← hRL, regroup]; rfl
    have r : rep k [true, true, true, true] (cons true (cons false (cons true RL))) =
        cons true (rep k [true, true, true, true] (cons false (cons true RL))) :=
      (rep_rotate k [true] [true, true, true, true] [true, true, true, true] rfl _).symm
    rw [r, z]
    show _ = app [false, true, true, true] (zl (List.replicate k false ++ tmap ws) (pre (npre p ws)))
    rw [zl_append, zl_replicate]
    rfl
  rw [e] at h6
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans
    (steps_seq trans h0 h1) h2) h3) h4) h5) h6⟩

/-- **Absorption, middle block `4k + 3`.**  The zone comes out as `tmap ws`, `v^(k+1)` and a wall `1 0`. -/
theorem absorb3 (ws : List Bool) (p : Bool) (k : Nat) (R : Tape) : ∃ n,
    steps n ⟨zl ws (pre p), cons true (cons true (cons false (rep k [true, true, true, true]
        (cons true (cons true (cons true (cons false (cons true R)))))))), .E⟩ =
      some ⟨app [false, true] (zl (List.replicate (k + 1) false ++ tmap ws) (pre (npre p ws))), R, .E⟩ := by
  let X := rep k [true, true, true, true] (cons true (cons true (cons true (cons false (cons true R)))))
  have h0 : steps 1 ⟨zl ws (pre p), cons true (cons true (cons false X)), .E⟩ =
      some (onL (zl ws (pre p)) (cons false (cons true (cons false X))) (pst true)) := rfl
  have h1 := sweep ws (pre p) true (cons false (cons true (cons false X)))
  have h2 := lend p (par true ws) (sweepR true ws (cons false (cons true (cons false X))))
  have h3 := rsweep ws true (app [true, true] (pre (bne p (par true ws)))) (cons false (cons true (cons false X)))
  generalize hRL : rsweepL true ws (app [true, true] (pre (bne p (par true ws)))) = RL at h3
  have h4 : steps 3 ⟨RL, cons false (cons true (cons false X)), .F⟩ =
      some ⟨cons true (cons false (cons true RL)), X, .F⟩ := rfl
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, true, true, true] R, .F⟩ =
      some ⟨app [] (app [true, true, true, true] L), R, .F⟩ := fun _ _ => rfl
  have h5 := cross_r trans c0 k (cons true (cons false (cons true RL)))
    (cons true (cons true (cons true (cons false (cons true R)))))
  -- F crosses 1 1 1, writes 1 on the 0, A writes 0, E reads R
  have h6 : steps 5 ⟨app [] (rep k [true, true, true, true] (cons true (cons false (cons true RL)))),
        cons true (cons true (cons true (cons false (cons true R)))), .F⟩ =
      some ⟨cons false (cons true (cons true (cons true (cons true
        (rep k [true, true, true, true] (cons true (cons false (cons true RL)))))))), R, .E⟩ := rfl
  have e : cons false (cons true (cons true (cons true (cons true
        (rep k [true, true, true, true] (cons true (cons false (cons true RL)))))))) =
      app [false, true] (zl (List.replicate (k + 1) false ++ tmap ws) (pre (npre p ws))) := by
    have z : cons false (cons true RL) = zl (tmap ws) (pre (npre p ws)) := by
      rw [← hRL, regroup]; rfl
    have r : rep k [true, true, true, true] (cons true (cons false (cons true RL))) =
        cons true (rep k [true, true, true, true] (cons false (cons true RL))) :=
      (rep_rotate k [true] [true, true, true, true] [true, true, true, true] rfl _).symm
    rw [r, z, zl_append, zl_replicate]
    rfl
  rw [e] at h6
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans
    (steps_seq trans h0 h1) h2) h3) h4) h5) h6⟩

/-- The bounce map with a wall: append a `0` on the right (nearest) and take the running XOR from the right. -/
def smap (ws : List Bool) : List Bool := false :: sx false ws

/-- **A bounce against a walled zone.**  Zone `ws` (prefix `p`), then the wall `1 0`, frozen tape `1 1 1 R`: the machine
comes back to a right turn with zone `smap ws`, the wall, and frozen tape `1 R`. -/
theorem wbounce (ws : List Bool) (p : Bool) (R : Tape) : ∃ n,
    steps n ⟨app [false, true] (zl ws (pre p)), cons true (cons true (cons true R)), .E⟩ =
      some ⟨app [false, true] (zl (smap ws) (pre (bne p (par false ws)))), cons true R, .E⟩ := by
  let Rr := cons true (cons true (cons false (cons true (cons true R))))
  -- E writes 0 and steps onto the wall; C writes 1 on its 0, D keeps its 1: the left sweep starts even
  have h0 : steps 3 ⟨app [false, true] (zl ws (pre p)), cons true (cons true (cons true R)), .E⟩ =
      some (onL (zl ws (pre p)) Rr (pst false)) := rfl
  have h1 := sweep ws (pre p) false Rr
  have h2 := lend p (par false ws) (sweepR false ws Rr)
  have h3 := rsweep ws false (app [true, true] (pre (bne p (par false ws)))) Rr
  generalize hRL : rsweepL false ws (app [true, true] (pre (bne p (par false ws)))) = RL at h3
  -- F crosses the old wall (now 1 1), writes 1 on the 0, A writes 0, E reads the third frozen 1
  have h4 : steps 4 ⟨RL, Rr, .F⟩ = some ⟨cons false (cons true (cons true (cons true RL))), cons true R, .E⟩ := rfl
  have e : cons false (cons true (cons true (cons true RL))) =
      app [false, true] (zl (smap ws) (pre (bne p (par false ws)))) := by
    rw [← hRL, regroup]; rfl
  rw [e] at h4
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans h0 h1) h2) h3) h4⟩

/-- `smap` applied `k` times. -/
def siter : Nat → List Bool → List Bool
  | 0, ws => ws
  | k + 1, ws => siter k (smap ws)

/-- `k` bounces against a walled zone and a frozen block of `2k + 1` cells. -/
theorem wbounces (k : Nat) : ∀ (ws : List Bool) (p : Bool) (R : Tape), ∃ n p',
    steps n ⟨app [false, true] (zl ws (pre p)), cons true (rep k [true, true] R), .E⟩ =
      some ⟨app [false, true] (zl (siter k ws) (pre p')), cons true R, .E⟩ := by
  induction k with
  | zero => intro ws p R; exact ⟨0, p, rfl⟩
  | succ k ih =>
    intro ws p R
    obtain ⟨n1, h1⟩ := wbounce ws p (rep k [true, true] R)
    obtain ⟨n2, p', h2⟩ := ih (smap ws) (bne p (par false ws)) R
    exact ⟨n1 + n2, p', steps_seq trans h1 h2⟩

/-- With a wall, a block of one cell followed by `0 1` halts: F> 1 1 0 0 1 runs into B reading 1. -/
theorem halt_turn_wall (ws : List Bool) (p : Bool) (R : Tape) :
    ∃ n c, steps n ⟨app [false, true] (zl ws (pre p)), cons true (cons false (cons true R)), .E⟩ = some c ∧
      step c = none := by
  let Rr := cons true (cons true (cons false (cons false (cons true R))))
  have h0 : steps 3 ⟨app [false, true] (zl ws (pre p)), cons true (cons false (cons true R)), .E⟩ =
      some (onL (zl ws (pre p)) Rr (pst false)) := rfl
  have h1 := sweep ws (pre p) false Rr
  have h2 := lend p (par false ws) (sweepR false ws Rr)
  have h3 := rsweep ws false (app [true, true] (pre (bne p (par false ws)))) Rr
  generalize rsweepL false ws (app [true, true] (pre (bne p (par false ws)))) = RL at h3
  have h4 : steps 4 ⟨RL, Rr, .F⟩ = some ⟨cons true (cons true (cons true (cons true RL))), cons true R, .B⟩ := rfl
  exact ⟨_, _, steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans h0 h1) h2) h3) h4, rfl⟩

/-- **A walled zone does not save an odd block**: frozen tape `1^(2k+1) 0 1 ...` halts. -/
theorem halts_of_odd_wall (k : Nat) (ws : List Bool) (p : Bool) (R : Tape) :
    Halts trans ⟨app [false, true] (zl ws (pre p)), cons true (rep k [true, true] (cons false (cons true R))), .E⟩ := by
  obtain ⟨n, p', h⟩ := wbounces k ws p (cons false (cons true R))
  obtain ⟨m, c, hm, hc⟩ := halt_turn_wall (siter k ws) p' R
  exact ⟨n + m, c, steps_seq trans h hm, hc⟩

end H75625
