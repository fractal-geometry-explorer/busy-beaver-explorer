import Phases

/-!
# 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD: the frame map with whole sweeps as one jump

`Phases.lean` proves the frame map `next` (78 cases) and `halts_iff`.  Most of its applications are repetitions of
a few cases, which are summed here in closed form for all sizes:

* `w_sweep`  `w(l, j + 2k, r + 1)` → `w(l + 4k, j, r + 1)` in `k` frames (and `W_sweep`)
* `u_sweep`  `u(l, j + k, r)` → `u(l, j, r + 2k)` in `k` frames (and `U_sweep`, for `U(l + 1, ..)`)
* `y_zigzag` `y(a + 3k, j, r + 1 + k)` → `y(a, j + 2k, r + 1)` in `2k` frames, if `a ≥ 3` (and `Y_zigzag`)

`jump` takes a whole sweep or zigzag at once (the largest `k` that applies) and is `next` otherwise; `jump_sound`:
each jump is a positive number of frames of `next`.  The halting rows (`halt_y`, `halt_Y`):

* `y(3k + 1, 2m, k + 2)` halts: `k` zigzag rounds to `y(1, 2m + 2k, 2)`, then `z(0, 2m + 2k + 2, 1)`,
  `w(0, 2m + 2k + 2, 1)`, a sweep to `w(4m + 4k + 4, 0, 1)`, where `next` is `none`;
* `Y(3k + 1, 2m, k + 3)` halts: `k` rounds to `Y(1, 2m + 2k, 3)`, then `z(2, 2m + 2k + 3, 2)`, `y(0, 2m + 2k + 3, 2)`,
  `z(0, 2m + 2k + 4, 1)`, `w(0, 2m + 2k + 4, 1)`, a sweep to `w(4m + 4k + 8, 0, 1)`;
* with odd `j` (no zigzag start of the run from blank tape has had one so far): `y(3k, 2m + 1, k + 2)` (`halt_y0`),
  `y(3k + 2, 2m + 1, k + 2)` (`halt_y2`), `Y(3k, 2m + 1, k + 2)` (`halt_Y0`).

From every frame with all three numbers below 60, every halt within 400 jumps comes before the first zigzag start
or right after a zigzag start in one of these five rows (`c/frun.c`, mode `rows`); that this holds always is not
proved here.

`no_halt_jumps` checks by `native_decide` that the first `10^8` jumps from `Ph.z 0 0 2` never meet a frame where
`next` is `none`; they are `146530202670678` frames (`jumps_frames`), so the first `1.4 * 10^14` frames of the run
from blank tape do not halt (`no_halt_frames`), against `10^8` frames in `Phases.lean`.
-/

namespace H97525

/-! ## Iterating `next` -/

theorem iter_add : ∀ (m n : Nat) (p q : Ph), iter m p = some q → iter (m + n) p = iter n q
  | 0, n, p, q, h => by simp only [iter, Option.some.injEq] at h; subst h; simp
  | m + 1, n, p, q, h => by
    simp only [iter] at h
    rw [Nat.add_right_comm]
    simp only [iter]
    cases hp : next p with
    | none => simp [hp] at h
    | some p1 => simp only [hp, Option.bind_some] at h ⊢; exact iter_add m n p1 q h

theorem iter_trans {m n : Nat} {p q s : Ph} (h1 : iter m p = some q) (h2 : iter n q = some s) :
    iter (m + n) p = some s := by rw [iter_add m n p q h1]; exact h2

theorem iter_one {p q : Ph} (h : next p = some q) : iter 1 p = some q := by simp [iter, h]

/-- A frame before a defined later frame is not a halting frame. -/
theorem not_none_before : ∀ (n : Nat) (p s : Ph), iter n p = some s →
    ∀ i, i < n → ∀ q, iter i p = some q → next q ≠ none := by
  intro n p s h i hi q hq hn
  have h1 : iter (i + 1) p = none := by rw [iter_succ i p q hq, hn]
  have h2 := iter_add (i + 1) (n - (i + 1)) p
  have : i + 1 + (n - (i + 1)) = n := by omega
  cases hx : iter (i + 1) p with
  | none =>
    have h3 : ∀ k (p : Ph), iter k p = none → ∀ m, iter (k + m) p = none := by
      intro k
      induction k with
      | zero => intro p h; simp [iter] at h
      | succ k ih =>
        intro p h m
        simp only [iter] at h
        rw [Nat.add_right_comm]; simp only [iter]
        cases hp : next p with
        | none => simp
        | some p1 => simp only [hp, Option.bind_some] at h ⊢; exact ih p1 h m
    have := h3 (i + 1) p hx (n - (i + 1))
    rw [show i + 1 + (n - (i + 1)) = n by omega, h] at this
    simp at this
  | some _ => rw [h1] at hx; simp at hx

/-! ## The single cases used by the sweeps -/

theorem nw (l j r : Nat) : next (.w l (j + 2) (r + 1)) = some (.w (l + 4) j (r + 1)) := by
  simp [next]

theorem nW (l j r : Nat) : next (.W l (j + 2) (r + 1)) = some (.W (l + 4) j (r + 1)) := by
  simp [next]

theorem nu (l j r : Nat) : next (.u l (j + 1) r) = some (.u l j (r + 2)) := by
  simp [next]

theorem nU (l j r : Nat) : next (.U (l + 1) (j + 1) r) = some (.U (l + 1) j (r + 2)) := by
  simp [next]

theorem ny (a j r : Nat) : next (.y (a + 1) j (r + 2)) = some (.z a (j + 2) (r + 1)) := by
  simp [next]

theorem nz (a j r : Nat) : next (.z (a + 2) (j + 1) (r + 1)) = some (.y a (j + 1) (r + 1)) := by
  simp [next]

theorem nY (a j r : Nat) : next (.Y (a + 2) j (r + 2)) = some (.Z (a + 1) (j + 2) (r + 1)) := by
  simp [next]

theorem nZ (a j r : Nat) : next (.Z (a + 2) (j + 1) (r + 1)) = some (.Y a (j + 1) (r + 1)) := by
  simp [next]

/-! ## Sweeps and zigzags in closed form -/

theorem w_sweep (l j r : Nat) : ∀ k, iter k (.w l (j + 2 * k) (r + 1)) = some (.w (l + 4 * k) j (r + 1))
  | 0 => by simp [iter]
  | k + 1 => by
    have h := iter_trans (iter_one (nw l (j + 2 * k) r)) (w_sweep (l + 4) j r k)
    rw [show j + 2 * (k + 1) = j + 2 * k + 2 by omega, show l + 4 * (k + 1) = l + 4 + 4 * k by omega,
      Nat.add_comm k 1]
    exact h

theorem W_sweep (l j r : Nat) : ∀ k, iter k (.W l (j + 2 * k) (r + 1)) = some (.W (l + 4 * k) j (r + 1))
  | 0 => by simp [iter]
  | k + 1 => by
    have h := iter_trans (iter_one (nW l (j + 2 * k) r)) (W_sweep (l + 4) j r k)
    rw [show j + 2 * (k + 1) = j + 2 * k + 2 by omega, show l + 4 * (k + 1) = l + 4 + 4 * k by omega,
      Nat.add_comm k 1]
    exact h

theorem u_sweep (l j : Nat) : ∀ k r, iter k (.u l (j + k) r) = some (.u l j (r + 2 * k))
  | 0, r => by simp [iter]
  | k + 1, r => by
    have h := iter_trans (iter_one (nu l (j + k) r)) (u_sweep l j k (r + 2))
    rw [show j + (k + 1) = j + k + 1 by omega, show r + 2 * (k + 1) = r + 2 + 2 * k by omega, Nat.add_comm k 1]
    exact h

theorem U_sweep (l j : Nat) : ∀ k r, iter k (.U (l + 1) (j + k) r) = some (.U (l + 1) j (r + 2 * k))
  | 0, r => by simp [iter]
  | k + 1, r => by
    have h := iter_trans (iter_one (nU l (j + k) r)) (U_sweep l j k (r + 2))
    rw [show j + (k + 1) = j + k + 1 by omega, show r + 2 * (k + 1) = r + 2 + 2 * k by omega, Nat.add_comm k 1]
    exact h

theorem y_round (a j r : Nat) : iter 2 (.y (a + 3) j (r + 2)) = some (.y a (j + 2) (r + 1)) := by
  have h := iter_trans (iter_one (ny (a + 2) j r)) (iter_one (nz a (j + 1) r))
  exact h

theorem Y_round (a j r : Nat) : iter 2 (.Y (a + 3) j (r + 2)) = some (.Y a (j + 2) (r + 1)) := by
  have h := iter_trans (iter_one (nY (a + 1) j r)) (iter_one (nZ a (j + 1) r))
  exact h

theorem y_zigzag (a r : Nat) : ∀ k j, iter (2 * k) (.y (a + 3 * k) j (r + 1 + k)) = some (.y a (j + 2 * k) (r + 1))
  | 0, j => by simp [iter]
  | k + 1, j => by
    have h1 := y_round (a + 3 * k) j (r + k)
    have h2 := y_zigzag a r k (j + 2)
    rw [show a + 3 * (k + 1) = a + 3 * k + 3 by omega, show r + 1 + (k + 1) = r + k + 2 by omega,
      show j + 2 * (k + 1) = j + 2 + 2 * k by omega, show 2 * (k + 1) = 2 + 2 * k by omega]
    rw [show r + k + 1 = r + 1 + k by omega] at h1
    exact iter_trans h1 h2

theorem Y_zigzag (a r : Nat) : ∀ k j, iter (2 * k) (.Y (a + 3 * k) j (r + 1 + k)) = some (.Y a (j + 2 * k) (r + 1))
  | 0, j => by simp [iter]
  | k + 1, j => by
    have h1 := Y_round (a + 3 * k) j (r + k)
    have h2 := Y_zigzag a r k (j + 2)
    rw [show a + 3 * (k + 1) = a + 3 * k + 3 by omega, show r + 1 + (k + 1) = r + k + 2 by omega,
      show j + 2 * (k + 1) = j + 2 + 2 * k by omega, show 2 * (k + 1) = 2 + 2 * k by omega]
    rw [show r + k + 1 = r + 1 + k by omega] at h1
    exact iter_trans h1 h2

/-! ## The halting rows -/

/-- `y(3k + 1, 2m, k + 2)` halts: the frame map reaches a frame where it is `none`. -/
theorem halt_y (k m : Nat) : ∃ n p, iter n (.y (3 * k + 1) (2 * m) (k + 2)) = some p ∧ next p = none := by
  have h1 := y_zigzag 1 1 k (2 * m)
  rw [show 1 + 3 * k = 3 * k + 1 by omega, show 1 + 1 + k = k + 2 by omega] at h1
  have h2 : next (.y 1 (2 * m + 2 * k) 2) = some (.z 0 (2 * m + 2 * k + 2) 1) := ny 0 (2 * m + 2 * k) 0
  have h3 : next (.z 0 (2 * m + 2 * k + 2) 1) = some (.w 0 (2 * m + 2 * k + 2) 1) := by simp [next]
  have h4 := w_sweep 0 0 0 (m + k + 1)
  rw [show 0 + 2 * (m + k + 1) = 2 * m + 2 * k + 2 by omega] at h4
  exact ⟨_, _, iter_trans (iter_trans (iter_trans h1 (iter_one h2)) (iter_one h3)) h4, by simp [next]⟩

/-- `Y(3k + 1, 2m, k + 3)` halts. -/
theorem halt_Y (k m : Nat) : ∃ n p, iter n (.Y (3 * k + 1) (2 * m) (k + 3)) = some p ∧ next p = none := by
  have h1 := Y_zigzag 1 2 k (2 * m)
  rw [show 1 + 3 * k = 3 * k + 1 by omega, show 2 + 1 + k = k + 3 by omega] at h1
  have h2 : next (.Y 1 (2 * m + 2 * k) 3) = some (.z 2 (2 * m + 2 * k + 3) 2) := by simp [next]
  have h3 : next (.z 2 (2 * m + 2 * k + 3) 2) = some (.y 0 (2 * m + 2 * k + 3) 2) := nz 0 (2 * m + 2 * k + 2) 1
  have h4 : next (.y 0 (2 * m + 2 * k + 3) 2) = some (.z 0 (2 * m + 2 * k + 4) 1) := by simp [next]
  have h5 : next (.z 0 (2 * m + 2 * k + 4) 1) = some (.w 0 (2 * m + 2 * k + 4) 1) := by simp [next]
  have h6 := w_sweep 0 0 0 (m + k + 2)
  rw [show 0 + 2 * (m + k + 2) = 2 * m + 2 * k + 4 by omega] at h6
  exact ⟨_, _, iter_trans (iter_trans (iter_trans (iter_trans (iter_trans h1 (iter_one h2)) (iter_one h3))
    (iter_one h4)) (iter_one h5)) h6, rfl⟩

/-- `y(3k, 2m + 1, k + 2)` halts (a zigzag start with odd `j`; none occurs in the run from blank tape so far). -/
theorem halt_y0 (k m : Nat) : ∃ n p, iter n (.y (3 * k) (2 * m + 1) (k + 2)) = some p ∧ next p = none := by
  have h1 := y_zigzag 0 1 k (2 * m + 1)
  rw [show 0 + 3 * k = 3 * k by omega, show 1 + 1 + k = k + 2 by omega] at h1
  have h2 : next (.y 0 (2 * m + 1 + 2 * k) 2) = some (.z 0 (2 * m + 2 * k + 2) 1) := by
    rw [show 2 * m + 2 * k + 2 = 2 * m + 1 + 2 * k + 1 by omega]; simp [next]
  have h3 : next (.z 0 (2 * m + 2 * k + 2) 1) = some (.w 0 (2 * m + 2 * k + 2) 1) := by simp [next]
  have h4 := w_sweep 0 0 0 (m + k + 1)
  rw [show 0 + 2 * (m + k + 1) = 2 * m + 2 * k + 2 by omega] at h4
  exact ⟨_, _, iter_trans (iter_trans (iter_trans h1 (iter_one h2)) (iter_one h3)) h4, by simp [next]⟩

/-- `y(3k + 2, 2m + 1, k + 2)` halts (odd `j`). -/
theorem halt_y2 (k m : Nat) : ∃ n p, iter n (.y (3 * k + 2) (2 * m + 1) (k + 2)) = some p ∧ next p = none := by
  have h1 := y_zigzag 2 1 k (2 * m + 1)
  rw [show 2 + 3 * k = 3 * k + 2 by omega, show 1 + 1 + k = k + 2 by omega] at h1
  have h2 : next (.y 2 (2 * m + 1 + 2 * k) 2) = some (.z 1 (2 * m + 2 * k + 3) 1) := by
    rw [show 2 * m + 2 * k + 3 = 2 * m + 1 + 2 * k + 2 by omega]; exact ny 1 _ 0
  have h3 : next (.z 1 (2 * m + 2 * k + 3) 1) = some (.W 4 (2 * m + 2 * k) 1) := by simp [next]
  have h4 := W_sweep 4 0 0 (m + k)
  rw [show 0 + 2 * (m + k) = 2 * m + 2 * k by omega] at h4
  exact ⟨_, _, iter_trans (iter_trans (iter_trans h1 (iter_one h2)) (iter_one h3)) h4, by simp [next]⟩

/-- `Y(3k, 2m + 1, k + 2)` halts (odd `j`). -/
theorem halt_Y0 (k m : Nat) : ∃ n p, iter n (.Y (3 * k) (2 * m + 1) (k + 2)) = some p ∧ next p = none := by
  have h1 := Y_zigzag 0 1 k (2 * m + 1)
  rw [show 0 + 3 * k = 3 * k by omega, show 1 + 1 + k = k + 2 by omega] at h1
  have h2 : next (.Y 0 (2 * m + 1 + 2 * k) 2) = some (.w 3 (2 * m + 2 * k + 2) 1) := by
    rw [show 2 * m + 2 * k + 2 = 2 * m + 1 + 2 * k + 1 by omega]; simp [next]
  have h4 := w_sweep 3 0 0 (m + k + 1)
  rw [show 0 + 2 * (m + k + 1) = 2 * m + 2 * k + 2 by omega] at h4
  exact ⟨_, _, iter_trans (iter_trans h1 (iter_one h2)) h4, by simp [next]⟩

/-! ## The jump map -/

/-- One jump and its number of frames: a whole sweep or zigzag, else one case of `next`. -/
def jump : Ph → Option (Ph × Nat)
  | .w l j (r + 1) => if 2 ≤ j then some (.w (l + 4 * (j / 2)) (j % 2) (r + 1), j / 2)
      else (next (.w l j (r + 1))).map (·, 1)
  | .W l j (r + 1) => if 2 ≤ j then some (.W (l + 4 * (j / 2)) (j % 2) (r + 1), j / 2)
      else (next (.W l j (r + 1))).map (·, 1)
  | .u l (j + 1) r => some (.u l 0 (r + 2 * (j + 1)), j + 1)
  | .U (l + 1) (j + 1) r => some (.U (l + 1) 0 (r + 2 * (j + 1)), j + 1)
  | .y a j (r + 2) => if 3 ≤ a then
        (let k := min (a / 3) (r + 1); some (.y (a - 3 * k) (j + 2 * k) (r + 2 - k), 2 * k))
      else (next (.y a j (r + 2))).map (·, 1)
  | .Y a j (r + 2) => if 3 ≤ a then
        (let k := min (a / 3) (r + 1); some (.Y (a - 3 * k) (j + 2 * k) (r + 2 - k), 2 * k))
      else (next (.Y a j (r + 2))).map (·, 1)
  | p => (next p).map (·, 1)

theorem map_sound {p : Ph} {q : Ph} {n : Nat} (h : (next p).map (·, 1) = some (q, n)) : iter n p = some q := by
  cases hp : next p with
  | none => simp [hp] at h
  | some q' => simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact iter_one hp

theorem map_none {p : Ph} (h : (next p).map (·, 1) = (none : Option (Ph × Nat))) : next p = none := by
  cases hp : next p with
  | none => rfl
  | some _ => simp [hp] at h

/-- Each jump is `n` frames of `next`. -/
theorem jump_sound : ∀ p q n, jump p = some (q, n) → iter n p = some q := by
  intro p q n h
  match p with
  | .w l j (r + 1) =>
    simp only [jump] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have := w_sweep l (j % 2) r (j / 2)
      rw [show j % 2 + 2 * (j / 2) = j by omega] at this; exact this
    · exact map_sound h
  | .W l j (r + 1) =>
    simp only [jump] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have := W_sweep l (j % 2) r (j / 2)
      rw [show j % 2 + 2 * (j / 2) = j by omega] at this; exact this
    · exact map_sound h
  | .u l (j + 1) r =>
    simp only [jump, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have := u_sweep l 0 (j + 1) r
    rw [Nat.zero_add] at this; exact this
  | .U (l + 1) (j + 1) r =>
    simp only [jump, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have := U_sweep l 0 (j + 1) r
    rw [Nat.zero_add] at this; exact this
  | .y a j (r + 2) =>
    simp only [jump] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have := y_zigzag (a - 3 * min (a / 3) (r + 1)) (r + 1 - min (a / 3) (r + 1)) (min (a / 3) (r + 1)) j
      rw [show a - 3 * min (a / 3) (r + 1) + 3 * min (a / 3) (r + 1) = a by omega,
        show r + 1 - min (a / 3) (r + 1) + 1 + min (a / 3) (r + 1) = r + 2 by omega,
        show r + 1 - min (a / 3) (r + 1) + 1 = r + 2 - min (a / 3) (r + 1) by omega] at this
      exact this
    · exact map_sound h
  | .Y a j (r + 2) =>
    simp only [jump] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have := Y_zigzag (a - 3 * min (a / 3) (r + 1)) (r + 1 - min (a / 3) (r + 1)) (min (a / 3) (r + 1)) j
      rw [show a - 3 * min (a / 3) (r + 1) + 3 * min (a / 3) (r + 1) = a by omega,
        show r + 1 - min (a / 3) (r + 1) + 1 + min (a / 3) (r + 1) = r + 2 by omega,
        show r + 1 - min (a / 3) (r + 1) + 1 = r + 2 - min (a / 3) (r + 1) by omega] at this
      exact this
    · exact map_sound h
  | .z l j r => exact map_sound h
  | .w l j 0 => exact map_sound h
  | .W l j 0 => exact map_sound h
  | .u l 0 r => exact map_sound h
  | .U 0 j r => exact map_sound h
  | .U (l + 1) 0 r => exact map_sound h
  | .y a j 0 => exact map_sound h
  | .y a j 1 => exact map_sound h
  | .Y a j 0 => exact map_sound h
  | .Y a j 1 => exact map_sound h
  | .Z l j r => exact map_sound h

/-- `N` jumps from `p` reach a frame with `next` defined there; the result is the frame and the frames counted. -/
def jumps : Nat → Ph → Nat → Option (Ph × Nat)
  | 0, p, f => some (p, f)
  | N + 1, p, f => match jump p with
    | none => none
    | some (q, n) => jumps N q (f + n)

theorem jumps_sound : ∀ N p f q F, jumps N p f = some (q, F) → iter (F - f) p = some q ∧ f ≤ F
  | 0, p, f, q, F, h => by
    simp only [jumps, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [iter]
  | N + 1, p, f, q, F, h => by
    simp only [jumps] at h
    cases hj : jump p with
    | none => simp [hj] at h
    | some qn =>
      obtain ⟨q1, n⟩ := qn
      simp only [hj] at h
      obtain ⟨h1, h2⟩ := jumps_sound N q1 (f + n) q F h
      refine ⟨?_, by omega⟩
      have := iter_trans (jump_sound p q1 n hj) h1
      rwa [show n + (F - (f + n)) = F - f by omega] at this

/-- The frame and frame count after the first `10^8` jumps (`c/frun.c` prints the same). -/
theorem jumps_frames : jumps 100000000 (Ph.z 0 0 2) 0 = some (.U 20516103 0 19787804, 146530202670678) := by
  native_decide

/-- **No halt in the first 146,530,202,670,678 frames** (about `1.5 * 10^14`) of the run from blank tape. -/
theorem no_halt_frames : ∀ i, i < 146530202670678 → ∀ q, iter i (Ph.z 0 0 2) = some q → next q ≠ none := by
  have h := (jumps_sound _ _ _ _ _ jumps_frames).1
  exact not_none_before _ _ _ h

end H97525
