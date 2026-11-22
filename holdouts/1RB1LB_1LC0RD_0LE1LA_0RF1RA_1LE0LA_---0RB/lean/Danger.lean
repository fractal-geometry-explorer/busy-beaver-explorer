import Xor

/-!
# The danger pattern halts, and an `x` in front of the defect shields it

During a right sweep B meets each run `1^m 0` at its first cell (`Xor.lean`).  A `10` defect is a run with `m = 1`, and
B on `1 0` goes into *token mode*: `B 1 → 0 D`, `D 0 → 0 F`, and F on the next cell.

* `token_y`: in token mode F crosses `y = 110` words, turning each into `000` (`F 1 → 0 B`, `B 1 → 0 D`, `D 0 → 0 F`).
* `danger_halts`: so B at the start of `y 10 y^n 0` (the defect with `y` before it, an all-`y` gap and a `0` wall) halts,
  for every `n`: the `y` is a run `1 1 0`, the defect puts B in token mode, the gap is crossed, and F reads the wall's 0.
* `shield`: with `x` before the defect, `x 10` is a single run `1 1 1 1 0`, which B rewrites to `0 0 0 1 1` and leaves in
  B at the start of the gap, the ordinary way: no token mode.
-/

namespace H696

open TM

/-- In token mode F crosses `y` words. -/
theorem token_y (n : Nat) : ∀ L R : Tape,
    steps (n * 3) ⟨app [] L, rep n [true, true, false] R, .F⟩ = some ⟨app [] (rep n [false, false, false] L), R, .F⟩ :=
  cross_r trans (u := []) (w := [true, true, false]) (v := [false, false, false]) (fun _ _ => rfl) n

/-- **The danger pattern halts.**  B at the start of `y 10 y^n 0`, any `n`. -/
theorem danger_halts (n : Nat) (L R : Tape) :
    Halts trans ⟨L, app [true, true, false, true, false] (rep n [true, true, false] (cons false R)), .B⟩ := by
  -- the run 1 1 0 (the word y): B leaves it as 0 1 1; then B 1 → 0 D, D 0 → 0 F: token mode
  have h1 : steps 5 ⟨L, app [true, true, false, true, false] (rep n [true, true, false] (cons false R)), .B⟩ =
      some ⟨app [] (app [false, false, true, true, false] L), rep n [true, true, false] (cons false R), .F⟩ := rfl
  have h2 := token_y n (app [false, false, true, true, false] L) (cons false R)
  exact ⟨_, _, steps_seq trans h1 h2, rfl⟩

/-- **An `x` before the defect shields it**: `x 10` is the run `1 1 1 1 0`, rewritten to `0 0 0 1 1` with B after it. -/
theorem shield (L R : Tape) :
    steps 9 ⟨L, app [true, true, true, true, false] R, .B⟩ = some ⟨app [true, true, false, false, false] L, R, .B⟩ := rfl

end H696
