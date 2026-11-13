import Machine
import Gadgets

/-!
# 1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---: the generic records

The machine is sampled at *E-records*: the head in state `E` on blank tape, with a `1` just left of it.  The tape
left of that `1` is built from blocks `(10)^n` and separators: `S = 01100`, a single `0`, or a single `1`.  The
*zone* is the run of blocks at the right end that are separated by `S`; the separator just left of the zone is the
*defect* `d`.  Read outward from the head (nearest first, as tapes are written here) an E-record is

    erec (zone z ds y (cons d T)) :   T  d  (10)^y  S  (10)^w1  S ... S  (10)^wr  S  (10)^z  1  E>0

with `ds = [w1, ..., wr]` (`sl ds` writes them, the last nearest), or `erec (blk z (cons d T))` for a zone of one
block.  One record is: a signal runs left across the zone (`across`, `sgad`), turns at the defect (`turn1`,
`turn0`), and `D` runs back right (`dunit`), turning every `(10)^(w+2) 1` into `S (10)^w`; the last block pays 2.

* `record_d1`: defect `1`, zone of at least two blocks: the defect becomes `0`, `y + 3`, `z - 2`.
* `record_d0`: defect `0` after a block `x + 2`: the block loses 2, the defect becomes `1`, `y + 5`, `z - 2`.
* `record1_d1`, `record1_d0`: the same for a zone of one block: `z + 1`, and `x - 2`, `z + 3`.

These are the rules the run follows almost always; the other cases (the last block 0 or 1, a defect at the left
edge, a block `x < 2` before a defect `0`, a frozen defect met by the signal) are events, found and checked by the
Python macro simulator in `py/` against direct simulation, not here.  Everything below is checked by Lean's kernel.
-/

namespace H3006

open TM

/-- A block `(10)^n` on the left (nearest cell first). -/
abbrev blk (n : Nat) (L : Tape) : Tape := rep n [false, true] L

/-- The separator `S = 01100`, nearest cell first. -/
abbrev sS : List Bool := [false, false, true, true, false]

/-- Blocks `w1 ... wr`, each after an `S`: `L S w1 S w2 ... S wr` (the last nearest). -/
def sl : List Nat → Tape → Tape
  | [], L => L
  | d :: ds, L => sl ds (blk d (app sS L))

/-- The right side after the leftward pass: `(10)^(w1+2) 1 (10)^(w2+2) 1 ... R`. -/
def rd : List Nat → Tape → Tape
  | [], R => R
  | d :: ds, R => rep (d + 2) [true, false] (cons true (rd ds R))

/-- A zone of at least two blocks: `T y S w1 S ... S wr S z`. -/
abbrev zone (z : Nat) (ds : List Nat) (y : Nat) (T : Tape) : Tape := blk z (app sS (sl ds (blk y T)))

/-- An E-record: `L 1 E>0` and blank tape to the right. -/
abbrev erec (L : Tape) : Config := ⟨cons true L, blank, .E⟩

theorem rotF (n : Nat) (W : Tape) : cons false (rep n [true, false] W) = rep n [false, true] (cons false W) :=
  rep_rotate n [false] [true, false] [false, true] rfl W

theorem e_start (L : Tape) : steps 1 (erec L) = some ⟨L, cons true (cons true blank), .A⟩ := rfl

theorem d_end (L : Tape) : steps 1 ⟨L, blank, .D⟩ = some (erec L) := rfl

/-- The leftward signal crosses a block: `(10)^n A>1 R` becomes `A>1 (10)^n R`. -/
theorem across (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨blk n L, cons true R, .A⟩ = some ⟨L, cons true (rep n [true, false] R), .A⟩ := by
  have c : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ =
      some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  exact steps_congr trans (Nat.mul_comm n 2) (cross_l trans c n L R)

/-- The steps of the leftward pass over `S w1 S ... S wr` (from the `S` nearest the head). -/
def acost : List Nat → Nat
  | [] => 21
  | d :: ds => acost ds + 2 * d + 21

/-- The S-gadget with its result written with a repeat. -/
theorem sgad' (L R : Tape) :
    steps 21 ⟨app sS L, cons true R, .A⟩ = some ⟨L, cons true (rep 2 [true, false] (cons true R)), .A⟩ :=
  sgad L R

/-- The leftward pass over the separators and middle blocks of a zone. -/
theorem apass : ∀ (ds : List Nat) (L R : Tape),
    steps (acost ds) ⟨app sS (sl ds L), cons true R, .A⟩ =
      some ⟨L, cons true (rep 2 [true, false] (cons true (rd ds R))), .A⟩
  | [], L, R => sgad' L R
  | d :: ds, L, R => by
    have h1 : steps (acost ds) ⟨app sS (sl (d :: ds) L), cons true R, .A⟩ =
        some ⟨blk d (app sS L), cons true (rep 2 [true, false] (cons true (rd ds R))), .A⟩ :=
      apass ds (blk d (app sS L)) R
    have h2 := across d (app sS L) (rep 2 [true, false] (cons true (rd ds R)))
    have h3 := sgad' L (rep d [true, false] (rep 2 [true, false] (cons true (rd ds R))))
    have e : rep d [true, false] (rep 2 [true, false] (cons true (rd ds R))) = rd (d :: ds) R := by
      simp only [rd, rep_add]
    rw [e] at h2 h3
    have h := steps_seq trans h1 (steps_seq trans h2 h3)
    exact steps_congr trans (by simp only [acost]; omega) h

/-- The steps of the rightward pass over `(10)^(w1+2) 1 ...`. -/
def dcost : List Nat → Nat
  | [] => 0
  | d :: ds => 2 * d + 5 + dcost ds

/-- The rightward unit, with the block written back in left form. -/
theorem dunit' (s : Nat) (L R : Tape) :
    steps (2 * s + 5) ⟨L, rep (s + 2) [true, false] (cons true R), .D⟩ = some ⟨blk s (app sS L), R, .D⟩ := by
  have h := dunit s L R
  rw [rotF] at h
  exact h

/-- The rightward pass: every `(10)^(w+2) 1` becomes `S (10)^w`. -/
theorem dpass : ∀ (ds : List Nat) (L R : Tape),
    steps (dcost ds) ⟨L, rd ds R, .D⟩ = some ⟨sl ds L, R, .D⟩
  | [], _, _ => rfl
  | d :: ds, L, R => steps_seq trans (dunit' d L (rd ds R)) (dpass ds (blk d (app sS L)) R)

/-- The turn at a defect `1`, in left form. -/
theorem turn1' (Y : Nat) (L R : Tape) :
    steps (2 * Y + 4) ⟨cons true L, cons true (rep Y [true, false] (cons true R)), .A⟩ =
      some ⟨blk (Y + 1) (cons false L), R, .D⟩ := by
  have h := turn1 Y L R
  rw [rotF] at h
  have e : rep Y [false, true] (cons false (cons true (cons false L))) = blk (Y + 1) (cons false L) :=
    rep_app_comm Y [false, true] (cons false L)
  rw [e] at h
  exact h

/-- The turn at a defect `0` after a block `x + 2`, in left form. -/
theorem turn0' (Y x : Nat) (L R : Tape) :
    steps (2 * Y + 16) ⟨cons false (blk (x + 2) L), cons true (rep Y [true, false] (cons true R)), .A⟩ =
      some ⟨blk (Y + 3) (cons true (blk x L)), R, .D⟩ := by
  have h := turn0 Y x L R
  rw [rotF] at h
  have e : rep Y [false, true] (cons false (cons true (cons false (cons true (cons false (cons true
      (cons true (rep x [false, true] L)))))))) = blk (Y + 3) (cons true (blk x L)) := by
    show rep Y [false, true] (rep 3 [false, true] (cons true (blk x L))) = _
    rw [← rep_add]
  rw [e] at h
  exact h

/-- From an E-record to the turn: the signal has crossed the zone and stands at the defect. -/
theorem to_turn (z : Nat) (ds : List Nat) (y : Nat) (T : Tape) :
    steps (1 + 2 * z + acost ds + 2 * y) (erec (zone z ds y T)) =
      some ⟨T, cons true (rep (y + 2) [true, false] (cons true (rd ds (rep z [true, false] (cons true blank))))), .A⟩ := by
  have h1 := e_start (zone z ds y T)
  have h2 := across z (app sS (sl ds (blk y T))) (cons true blank)
  have h3 := apass ds (blk y T) (rep z [true, false] (cons true blank))
  have h4 := across y T (rep 2 [true, false] (cons true (rd ds (rep z [true, false] (cons true blank)))))
  rw [← rep_add] at h4
  have h := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))
  exact steps_congr trans (by omega) h

/-- From the turn back to the next E-record: `D` crosses the zone and pays 2 from the last block. -/
theorem from_turn (z : Nat) (ds : List Nat) (L : Tape) :
    steps (dcost ds + (2 * z + 5) + 1) ⟨L, rd ds (rep (z + 2) [true, false] (cons true blank)), .D⟩ =
      some (erec (blk z (app sS (sl ds L)))) :=
  steps_congr trans (by omega)
    (steps_seq trans (dpass ds L _) (steps_seq trans (dunit' z (sl ds L) blank) (d_end _)))

/-- The steps of a generic record: `4z + 4y + 40 + Σ (4w + 26)` for defect `1` (and 12 more for defect `0`). -/
def rcost (z : Nat) (ds : List Nat) (y : Nat) : Nat :=
  1 + 2 * (z + 2) + acost ds + 2 * y + (2 * (y + 2) + 4) + (dcost ds + (2 * z + 5) + 1)

/-- Defect `1`, zone of at least two blocks: the defect becomes `0`, `y + 3`, `z - 2`. -/
theorem record_d1 (z : Nat) (ds : List Nat) (y : Nat) (T : Tape) :
    steps (rcost z ds y) (erec (zone (z + 2) ds y (cons true T))) =
      some (erec (zone z ds (y + 3) (cons false T))) := by
  have h1 := to_turn (z + 2) ds y (cons true T)
  have h2 := turn1' (y + 2) T (rd ds (rep (z + 2) [true, false] (cons true blank)))
  rw [show y + 2 + 1 = y + 3 from rfl] at h2
  have h3 := from_turn z ds (blk (y + 3) (cons false T))
  exact steps_congr trans (by simp only [rcost]; omega) (steps_seq trans h1 (steps_seq trans h2 h3))

/-- Defect `0` after a block `x + 2`, zone of at least two blocks: `x - 2`, the defect becomes `1`, `y + 5`,
`z - 2`. -/
theorem record_d0 (z : Nat) (ds : List Nat) (y x : Nat) (T : Tape) :
    steps (rcost z ds y + 12) (erec (zone (z + 2) ds y (cons false (blk (x + 2) T)))) =
      some (erec (zone z ds (y + 5) (cons true (blk x T)))) := by
  have h1 := to_turn (z + 2) ds y (cons false (blk (x + 2) T))
  have h2 := turn0' (y + 2) x T (rd ds (rep (z + 2) [true, false] (cons true blank)))
  rw [show y + 2 + 3 = y + 5 from rfl] at h2
  have h3 := from_turn z ds (blk (y + 5) (cons true (blk x T)))
  have h := steps_seq trans h1 (steps_seq trans h2 h3)
  exact steps_congr trans (by simp only [rcost]; omega) h

/-- Defect `1`, a zone of one block: it grows by one and the defect becomes `0`. -/
theorem record1_d1 (z : Nat) (T : Tape) :
    steps (4 * z + 6) (erec (blk z (cons true T))) = some (erec (blk (z + 1) (cons false T))) := by
  have h := steps_seq trans (e_start _) (steps_seq trans (across z (cons true T) (cons true blank))
    (steps_seq trans (turn1' z T blank) (d_end _)))
  exact steps_congr trans (by omega) h

/-- Defect `0` after a block `x + 2`, a zone of one block: `x - 2`, the defect becomes `1`, `z + 3`. -/
theorem record1_d0 (z x : Nat) (T : Tape) :
    steps (4 * z + 18) (erec (blk z (cons false (blk (x + 2) T)))) =
      some (erec (blk (z + 3) (cons true (blk x T)))) := by
  have h := steps_seq trans (e_start _) (steps_seq trans (across z _ (cons true blank))
    (steps_seq trans (turn0' z x T blank) (d_end _)))
  exact steps_congr trans (by omega) h

/-- The closed form of the cost of a generic record with defect `1`: `4z + 4y + 40 + Σ (4w + 26)`. -/
theorem rcost_eq (z : Nat) (ds : List Nat) (y : Nat) :
    rcost z ds y = 4 * z + 4 * y + 40 + (ds.map (fun w => 4 * w + 26)).sum := by
  have ha : ∀ ds : List Nat, acost ds + dcost ds = 21 + (ds.map (fun w => 4 * w + 26)).sum := by
    intro ds
    induction ds with
    | nil => rfl
    | cons d ds ih => simp only [acost, dcost, List.map_cons, List.sum_cons]; omega
  have := ha ds
  simp only [rcost]; omega

/-- The list configuration at step 431 from blank tape (kernel evaluation of the list simulator). -/
theorem fsteps431 : fsteps 431 (FCfg.blank .A) = some ⟨[true, false, true, false, true, false, true, false, true, false, true, true, false, false, true, true, false, false, true, false, true, false, false, true, true, false, false, true, false, true, false, false, true, true, false, false, true, false, true], [], .E⟩ := by
  decide +kernel

/-- The run from blank tape reaches the E-record `<2> S <2> S <2> S 1 <5> 1 E>0` at step 431, where `record1_d1`
applies. -/
theorem reach431 :
    steps 431 init = some (erec (blk 5 (cons true (app sS (blk 2 (app sS (blk 2 (app sS (blk 2 blank))))))))) := by
  have h := blank_reaches trans fsteps431
  exact h

/-- ... and the next one, `<2> S <2> S <2> S 0 <6> 1 E>0`, 26 steps later by `record1_d1`. -/
theorem reach457 :
    steps 457 init = some (erec (blk 6 (cons false (app sS (blk 2 (app sS (blk 2 (app sS (blk 2 blank))))))))) :=
  steps_congr trans (a := 431 + (4 * 5 + 6)) rfl (steps_seq trans reach431 (record1_d1 5 _))

end H3006
