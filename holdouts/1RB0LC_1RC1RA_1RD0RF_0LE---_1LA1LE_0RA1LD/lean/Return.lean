import Machine

/-! # 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD: the return after a `00` pulse, word by word

Written by `py/ret_rules.py`; do not edit by hand.

After the right sweep (`Pulse.lean`) every word to the left of the head is an image: `11` (from `01`) or `100`
(from `011`). When the sweep meets a `00` instead of a run of 1s, the head comes back left in one of three modes,
named by its state when it enters the last cell of an image. Each theorem below is one mode crossing one image, with
the six cells to its right (the *carry*) as they occur on such returns; it holds whatever the tape further left and
further right is. In the name `ret_S_c_w`, S is the mode, c the carry and w the word whose image is crossed.

- **C** turns the image `100` back into the word `011`, carry unchanged; on `11` it writes the word `01` and the
  carry's first cells `011` become `101`. It stays C.
- **E** leaves `11` as it is, so the word's 1s join the run on its right, and stays E; at `100` it writes `110`,
  clears the second cell of the carry and switches to A.
- **A** leaves `11` as it is and clears the first cell of the carry, so the word becomes a run of two 1s; at `100`
  the head goes back right beyond the carry (a new excursion, not covered here).

So a run of `01` words crossed in mode E becomes one run of 1s: one way a `00` pulse writes a new fuse.

Kernel only (`rfl`). -/

namespace H126068

open TM

theorem ret_A_110100_w01 (L R : Tape) :
    steps 8 ⟨app [true] L, app [true, true, true, false, true, false, false] R, .A⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, false, true, false, true, false, false] R), .A⟩ := rfl

theorem ret_A_110101_w01 (L R : Tape) :
    steps 8 ⟨app [true] L, app [true, true, true, false, true, false, true] R, .A⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, false, true, false, true, false, true] R), .A⟩ := rfl

theorem ret_A_110110_w01 (L R : Tape) :
    steps 8 ⟨app [true] L, app [true, true, true, false, true, true, false] R, .A⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, false, true, false, true, true, false] R), .A⟩ := rfl

theorem ret_C_011010_w01 (L R : Tape) :
    steps 8 ⟨app [true] L, app [true, false, true, true, false, true, false] R, .C⟩ =
      some ⟨tail L, cons (L 0) (app [false, true, true, false, true, false, true, false] R), .C⟩ := rfl

theorem ret_C_011010_w011 (L R : Tape) :
    steps 5 ⟨app [false, true] L, app [false, false, true, true, false, true, false] R, .C⟩ =
      some ⟨tail L, cons (L 0) (app [false, true, true, false, true, true, false, true, false] R), .C⟩ := rfl

theorem ret_C_011011_w01 (L R : Tape) :
    steps 8 ⟨app [true] L, app [true, false, true, true, false, true, true] R, .C⟩ =
      some ⟨tail L, cons (L 0) (app [false, true, true, false, true, false, true, true] R), .C⟩ := rfl

theorem ret_C_011011_w011 (L R : Tape) :
    steps 5 ⟨app [false, true] L, app [false, false, true, true, false, true, true] R, .C⟩ =
      some ⟨tail L, cons (L 0) (app [false, true, true, false, true, true, false, true, true] R), .C⟩ := rfl

theorem ret_C_011101_w01 (L R : Tape) :
    steps 8 ⟨app [true] L, app [true, false, true, true, true, false, true] R, .C⟩ =
      some ⟨tail L, cons (L 0) (app [false, true, true, false, true, true, false, true] R), .C⟩ := rfl

theorem ret_C_011101_w011 (L R : Tape) :
    steps 5 ⟨app [false, true] L, app [false, false, true, true, true, false, true] R, .C⟩ =
      some ⟨tail L, cons (L 0) (app [false, true, true, false, true, true, true, false, true] R), .C⟩ := rfl

theorem ret_E_110110_w01 (L R : Tape) :
    steps 2 ⟨app [true] L, app [true, true, true, false, true, true, false] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, true, true, false, true, true, false] R), .E⟩ := rfl

theorem ret_E_110110_w011 (L R : Tape) :
    steps 19 ⟨app [false, true] L, app [false, true, true, false, true, true, false] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, false, true, false, false, true, true, false] R), .A⟩ := rfl

theorem ret_E_110111_w01 (L R : Tape) :
    steps 2 ⟨app [true] L, app [true, true, true, false, true, true, true] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, true, true, false, true, true, true] R), .E⟩ := rfl

theorem ret_E_110111_w011 (L R : Tape) :
    steps 19 ⟨app [false, true] L, app [false, true, true, false, true, true, true] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, false, true, false, false, true, true, true] R), .A⟩ := rfl

theorem ret_E_111011_w01 (L R : Tape) :
    steps 2 ⟨app [true] L, app [true, true, true, true, false, true, true] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, true, true, true, false, true, true] R), .E⟩ := rfl

theorem ret_E_111011_w011 (L R : Tape) :
    steps 19 ⟨app [false, true] L, app [false, true, true, true, false, true, true] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, false, true, false, true, false, true, true] R), .A⟩ := rfl

theorem ret_E_111101_w01 (L R : Tape) :
    steps 2 ⟨app [true] L, app [true, true, true, true, true, false, true] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, true, true, true, true, false, true] R), .E⟩ := rfl

theorem ret_E_111101_w011 (L R : Tape) :
    steps 19 ⟨app [false, true] L, app [false, true, true, true, true, false, true] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, false, true, false, true, true, false, true] R), .A⟩ := rfl

theorem ret_E_111110_w01 (L R : Tape) :
    steps 2 ⟨app [true] L, app [true, true, true, true, true, true, false] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, true, true, true, true, true, false] R), .E⟩ := rfl

theorem ret_E_111110_w011 (L R : Tape) :
    steps 19 ⟨app [false, true] L, app [false, true, true, true, true, true, false] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, false, true, false, true, true, true, false] R), .A⟩ := rfl

theorem ret_E_111111_w01 (L R : Tape) :
    steps 2 ⟨app [true] L, app [true, true, true, true, true, true, true] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, true, true, true, true, true, true] R), .E⟩ := rfl

theorem ret_E_111111_w011 (L R : Tape) :
    steps 19 ⟨app [false, true] L, app [false, true, true, true, true, true, true] R, .E⟩ =
      some ⟨tail L, cons (L 0) (app [true, true, false, true, false, true, true, true, true] R), .A⟩ := rfl

end H126068
