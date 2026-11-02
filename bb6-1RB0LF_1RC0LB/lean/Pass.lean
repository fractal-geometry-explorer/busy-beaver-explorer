import Machine

/-!
# The rightward pass, and the pieces of a bounce

The run is a sequence of bounces.  Moving right, C and B fill a sparse region (single 1s with gaps of 0s between them)
into solid 1s; moving left, A and F turn a solid block back into alternating `1 0`, and B erases a block.

**The pass.**  Call a gap a maximal run of 0s between two 1s, and say C *enters* a gap when it stands on the gap's
second cell (the first cell is behind it).  Gaps of 1 and 2 are crossed, and C enters the next gap (`gap1`,
`gap2`, `pass`).  The first gap of any other length ends the pass:

* length 3: the machine halts two steps later (`pass_halt`);
* length 4 or more: D and E fill two more cells and A turns left (`pass_turn_E`);
* length 0 (two 1s side by side): B or F turns left (`pass_turn_B1`, `pass_turn_B2`).

So **a pass halts exactly when the first gap it meets that is not 1 or 2 has length 3** (`pass_outcome`).  A pass
starts when F or B reads the first cell of a gap and moves right (`start_F`, `start_B`); every rightward run of the
machine starts that way.

**Moving left.**  `sweep` turns `1^(2k)` into `(1 0)^k` (A and F alternate), `erase` turns `1^k` into `0^k` (B).

Everything here is checked by Lean's kernel (`rfl` and the shift rules of `TM.Basic`).
-/

namespace BB6e

open TM

/-! ## The pieces of a pass -/

/-- A gap of 1 (C on the 1 that ends it, the next gap's first cell after it): `C>1 0` becomes `1 1 C>`. -/
theorem gap1 (L R : Tape) : steps 2 ⟨L, app [true, false] R, .C⟩ = some ⟨app [true, true] L, R, .C⟩ := rfl

/-- A gap of 2: `C>0 1 0` becomes `1 1 0 C>` (left words nearest first: `[false, true, true]`). -/
theorem gap2 (L R : Tape) :
    steps 3 ⟨L, app [false, true, false] R, .C⟩ = some ⟨app [false, true, true] L, R, .C⟩ := rfl

/-- A gap of 3: `C>0 0 1` halts (C0, D0, then E on a 1). -/
theorem gap3 (L R : Tape) :
    steps 2 ⟨L, app [false, false, true] R, .C⟩ = some ⟨app [true, true] L, app [true] R, .E⟩ ∧
      step ⟨app [true, true] L, app [true] R, .E⟩ = none := ⟨rfl, rfl⟩

/-- A gap of 4 or more: `C>0 0 0` writes three 1s and turns: A stands on the second of them. -/
theorem gapBig (L R : Tape) :
    steps 3 ⟨L, app [false, false, false] R, .C⟩ = some ⟨app [true] L, app [true, true] R, .A⟩ := rfl

/-- Gap 1 then two 1s side by side: `C>1 1` turns into B erasing leftward. -/
theorem gap1_then_0 (L R : Tape) :
    steps 2 ⟨L, app [true, true] R, .C⟩ = some ⟨L, app [true, false] R, .B⟩ := rfl

/-- Gap 2 then two 1s side by side: `C>0 1 1` turns into A. -/
theorem gap2_then_0 (L R : Tape) :
    steps 3 ⟨L, app [false, true, true] R, .C⟩ = some ⟨app [true] L, app [true, true] R, .A⟩ := rfl

/-! ## A pass over gaps of 1 and 2 -/

/-- The cells a crossed gap occupies from C's position: its remaining 0s, the 1 that ends it, and the first cell of
the next gap. -/
def tok : Nat → List Bool
  | 2 => [false, true, false]
  | _ => [true, false]

/-- What crossing a gap leaves behind, nearest first. -/
def wr : Nat → List Bool
  | 2 => [false, true, true]
  | _ => [true, true]

/-- Steps to cross a gap. -/
def cost : Nat → Nat
  | 2 => 3
  | _ => 2

/-- The cells of a list of crossed gaps, left to right. -/
def word : List Nat → List Bool
  | [] => []
  | g :: gs => tok g ++ word gs

/-- What a list of crossed gaps leaves behind, nearest first. -/
def wrote : List Nat → List Bool
  | [] => []
  | g :: gs => wrote gs ++ wr g

/-- Steps to cross a list of gaps. -/
def costs : List Nat → Nat
  | [] => 0
  | g :: gs => cost g + costs gs

theorem cross_one {g : Nat} (hg : g = 1 ∨ g = 2) (L R : Tape) :
    steps (cost g) ⟨L, app (tok g) R, .C⟩ = some ⟨app (wr g) L, R, .C⟩ := by
  rcases hg with rfl | rfl
  · exact gap1 L R
  · exact gap2 L R

/-- **The pass.**  C crosses any list of gaps of length 1 and 2 and enters the gap after them. -/
theorem pass : ∀ (gs : List Nat), (∀ g ∈ gs, g = 1 ∨ g = 2) → ∀ L R : Tape,
    steps (costs gs) ⟨L, app (word gs) R, .C⟩ = some ⟨app (wrote gs) L, R, .C⟩
  | [], _, L, R => rfl
  | g :: gs, h, L, R => by
    have h₁ := cross_one (h g (List.mem_cons_self ..)) L (app (word gs) R)
    have h₂ := pass gs (fun x hx => h x (List.mem_cons_of_mem _ hx)) (app (wr g) L) R
    rw [app_app] at h₂
    have e : app (tok g) (app (word gs) R) = app (word (g :: gs)) R := by simp [word, app_app]
    rw [e] at h₁
    exact steps_seq trans h₁ h₂

/-- The pass ends at a gap of 3: the machine halts. -/
theorem pass_halt (gs : List Nat) (h : ∀ g ∈ gs, g = 1 ∨ g = 2) (L R : Tape) :
    TM.Halts trans ⟨L, app (word gs) (app [false, false, true] R), .C⟩ :=
  ⟨costs gs + 2, _, steps_seq trans (pass gs h L _) (gap3 (app (wrote gs) L) R).1,
    (gap3 (app (wrote gs) L) R).2⟩

/-- The pass ends at a gap of 4 or more: A turns left on the second of three new 1s. -/
theorem pass_turn_E (gs : List Nat) (h : ∀ g ∈ gs, g = 1 ∨ g = 2) (L R : Tape) :
    steps (costs gs + 3) ⟨L, app (word gs) (app [false, false, false] R), .C⟩ =
      some ⟨app [true] (app (wrote gs) L), app [true, true] R, .A⟩ :=
  steps_seq trans (pass gs h L _) (gapBig _ R)

/-- The pass ends at two 1s side by side after a gap of 1: B erases leftward. -/
theorem pass_turn_B1 (gs : List Nat) (h : ∀ g ∈ gs, g = 1 ∨ g = 2) (L R : Tape) :
    steps (costs gs + 2) ⟨L, app (word gs) (app [true, true] R), .C⟩ =
      some ⟨app (wrote gs) L, app [true, false] R, .B⟩ :=
  steps_seq trans (pass gs h L _) (gap1_then_0 _ R)

/-- The pass ends at two 1s side by side after a gap of 2: A turns left. -/
theorem pass_turn_B2 (gs : List Nat) (h : ∀ g ∈ gs, g = 1 ∨ g = 2) (L R : Tape) :
    steps (costs gs + 3) ⟨L, app (word gs) (app [false, true, true] R), .C⟩ =
      some ⟨app [true] (app (wrote gs) L), app [true, true] R, .A⟩ :=
  steps_seq trans (pass gs h L _) (gap2_then_0 _ R)

/-- **Which passes halt.**  After crossing gaps of 1 and 2, C meets one of four endings (gap 3, gap 4 or more, a 1
right after gap 1, a 1 right after gap 2).  Only the first halts; the other three turn left in a state that is not
halting, after a known number of steps. -/
theorem pass_outcome (gs : List Nat) (h : ∀ g ∈ gs, g = 1 ∨ g = 2) (L R : Tape) :
    TM.Halts trans ⟨L, app (word gs) (app [false, false, true] R), .C⟩ ∧
    (∃ c, steps (costs gs + 3) ⟨L, app (word gs) (app [false, false, false] R), .C⟩ = some c ∧ c.st = .A) ∧
    (∃ c, steps (costs gs + 2) ⟨L, app (word gs) (app [true, true] R), .C⟩ = some c ∧ c.st = .B) ∧
    (∃ c, steps (costs gs + 3) ⟨L, app (word gs) (app [false, true, true] R), .C⟩ = some c ∧ c.st = .A) :=
  ⟨pass_halt gs h L R, ⟨_, pass_turn_E gs h L R, rfl⟩, ⟨_, pass_turn_B1 gs h L R, rfl⟩,
    ⟨_, pass_turn_B2 gs h L R, rfl⟩⟩

/-! ## Where passes start -/

/-- F reading the first cell of a gap (a 0) keeps it and C enters the gap. -/
theorem start_F (L R : Tape) : steps 1 ⟨L, app [false] R, .F⟩ = some ⟨app [false] L, R, .C⟩ := rfl

/-- B reading the first cell of a gap (a 0) writes a 1 and C enters the gap. -/
theorem start_B (L R : Tape) : steps 1 ⟨L, app [false] R, .B⟩ = some ⟨app [true] L, R, .C⟩ := rfl

/-! ## Moving left -/

/-- A and F over a solid block: `1^(2k) A>1` becomes `A>1 (1 0)^k`. -/
theorem sweep (k : Nat) (L R : Tape) :
    steps (k * 2) ⟨rep k [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (rep k [true, false] R), .A⟩ :=
  cross_l trans (s := 2) (u := [true]) (w := [true, true]) (v := [true, false]) (fun _ _ => rfl) k L R

/-- The sweep reaches the 0 left of an odd block: F keeps it and C enters the gap A just made. -/
theorem sweep_end_odd (L R : Tape) :
    steps 2 ⟨app [false] L, app [true] R, .A⟩ = some ⟨app [false] L, app [false] R, .C⟩ := rfl

/-- The sweep reaches the 0 left of an even block: A fills it and B starts erasing leftward. -/
theorem sweep_end_even (L R : Tape) :
    steps 4 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨L, app [true, false, false] R, .B⟩ := rfl

/-- B erasing: `1^k B>1` becomes `B>1 0^k`. -/
theorem erase (k : Nat) (L R : Tape) :
    steps (k * 1) ⟨rep k [true] L, app [true] R, .B⟩ = some ⟨L, app [true] (rep k [false] R), .B⟩ :=
  cross_l trans (s := 1) (u := [true]) (w := [true]) (v := [false]) (fun _ _ => rfl) k L R

/-- B erases its last 1 and reaches a 0: it writes a 1 and C runs right into the erased cells. -/
theorem erase_end (L R : Tape) :
    steps 2 ⟨app [false] L, app [true] R, .B⟩ = some ⟨app [true] L, app [false] R, .C⟩ := rfl

end BB6e
