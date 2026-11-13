import Blank

/-! # Marker configurations of 1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC: the start and the halting shape

With `a = 10` and `b = 110`, the moments the head extends the tape to the left in state B have the tape

    P[k0, k1, ..., kn]  =  0^∞ B> 0 0 a^k0 b a^k1 b ... b a^kn 1 0^∞        (`pcfg`)

a block of pairs cut by `n` markers `b`.  Proved here:

* `blank_to_P`: blank tape reaches `P[1, 1, 1]` in 72 steps;
* `single_halts`: `P[N]`, a block with no marker, halts for every `N` (after `2N + 7` steps): F and C walk
  right over the pairs and F reads the blank cell after the tape.

The map between marker configurations (`py/map.py`) is fitted, not proved. -/

namespace H113170

open TM

/-- The cells `a^k0 b a^k1 b ... a^kn 1` of a marker list. -/
def ptape : List Nat → Tape
  | [] => cons true blank
  | [k] => rep k [true, false] (cons true blank)
  | k :: G => rep k [true, false] (cons true (cons true (cons false (ptape G))))

/-- `P[G]`: the head in B at the left end, on `0 0`, in front of the marker list. -/
def pcfg (G : List Nat) : Config := ⟨blank, cons false (cons false (ptape G)), .B⟩

/-- From blank tape the machine reaches `P[1, 1, 1] = B> 0 0 a b a b a 1` in 72 steps. -/
theorem blank_to_P : steps 72 init = some (pcfg [1, 1, 1]) := by
  have h : fsteps 72 (FCfg.blank .A) = some ⟨[], [false, false, true, false, true, true, false, true, false,
      true, true, false, true, false, true], .B⟩ := by decide +kernel
  exact blank_reaches trans h

/-- F and C walk right over pairs `10`. -/
theorem fc_run (n : Nat) (L R : Tape) :
    steps (n * 2) ⟨L, rep n [true, false] R, .F⟩ = some ⟨rep n [false, true] L, R, .F⟩ := by
  have c : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .F⟩ = some ⟨app [] (app [false, true] L), R, .F⟩ :=
    fun _ _ => rfl
  exact cross_r trans c n L R

/-- **A block with no marker halts.**  `P[N] = B> 0 0 a^N 1` halts for every `N`. -/
theorem single_halts (n : Nat) : Halts trans (pcfg [n]) := by
  have h0 : steps 4 (pcfg [n]) = some ⟨cons false (cons true (cons false blank)),
      rep n [true, false] (cons true blank), .F⟩ := rfl
  have h1 := fc_run n (cons false (cons true (cons false blank))) (cons true blank)
  have h2 : steps 2 ⟨rep n [false, true] (cons false (cons true (cons false blank))), cons true blank, .F⟩ =
      some ⟨cons false (cons true (rep n [false, true] (cons false (cons true (cons false blank))))), blank, .F⟩ := rfl
  exact ⟨_, _, steps_seq trans h0 (steps_seq trans h1 h2), rfl⟩

end H113170
