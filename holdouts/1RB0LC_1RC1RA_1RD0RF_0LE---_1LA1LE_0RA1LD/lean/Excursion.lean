import Pulse

/-! # 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD: the excursion of mode A at a `011` word

In the return after a `00` pulse (`Return.lean`), mode A reaching the image `100` of a word `011` sends the head
right again. This file shows that this excursion is an ordinary pulse (`Pulse.lean`): the head stands in state A on
the last cell of `100`, a 0, and that 0 with the six-cell carry after it is a list of words
(`start_110110`, `start_110101`; with carry `110100` it is two words and then a `00`, so a nested `00` pulse).
When the pulse finds a run of three or more 1s it comes back with the packet `111`, which turns `10 111` into
`11 011`, and the head goes on left in mode E (`after_w01`, `after_w011`). `excursion_110110` puts this together for
the carry `110110` followed by a run of 1s.

Kernel only (`rfl`, `omega`). -/

namespace H126068

open TM

/-- Carry `110110`: the last 0 of `100` and the carry are the words `011 011`, then a 0 that starts the next word. -/
theorem start_110110 (R : Tape) :
    app [false, true, true, false, true, true, false] R = words [true, true] (app [false] R) := rfl

/-- Carry `110101`: the words `011 01`, then `01` …. -/
theorem start_110101 (R : Tape) :
    app [false, true, true, false, true, false, true] R = words [true, false, false] R := rfl

/-- Carry `110100`: the words `011 01`, then `00`. -/
theorem start_110100 (R : Tape) :
    app [false, true, true, false, true, false, false] R = words [true, false] (app [false, false] R) := rfl

/-- The packet back at the image of a `011` word with the image `11` of a word `01` to its left: 5 steps, mode E. -/
theorem after_w01 (L R : Tape) :
    steps 5 ⟨app [false, true] (app [true, true] L), app [true, true, true] R, .A⟩ =
      some ⟨app [true] L, app [true, true, true, false, true, true] R, .E⟩ := rfl

/-- The same with the image `100` of a word `011` to its left. -/
theorem after_w011 (L R : Tape) :
    steps 5 ⟨app [false, true] (app [false, false, true] L), app [true, true, true] R, .A⟩ =
      some ⟨app [false, true] L, app [false, true, true, false, true, true] R, .E⟩ := rfl

/-- **The excursion from carry `110110`, when a run of three or more 1s follows.** Mode A on the image `100` (with the
image `11` to its left) runs a pulse over the two words of the carry, takes three 1s from the run and comes back;
35 steps later the head is in mode E on the image to the left, and the run has three 1s fewer. -/
theorem excursion_110110 (L R : Tape) :
    steps 35 ⟨app [false, true] (app [true, true] L),
        app [false, true, true, false, true, true, false, true, true, true] R, .A⟩ =
      some ⟨app [true] L, app [true, true, true, false, true, true] (words [true, true] (app [false] R)), .E⟩ := by
  have e : app [false, true, true, false, true, true, false, true, true, true] R =
      words [true, true] (app [false, true, true, true] R) := rfl
  rw [e]
  have h1 := pulse [true, true] (app [false, true] (app [true, true] L)) R
  have h2 := after_w01 L (words [true, true] (app [false] R))
  exact TM.steps_seq trans h1 h2

end H126068
