import MoverRules
import Walk
set_option linter.unusedSimpArgs false

/-!
# Movers: the head crosses them unchanged

During a rebuild the head bounces between the right end of the tape and the reflector `Q` (`Walk.lean`); during a
drain it bounces between the right end and the left end.  In between lie *movers*.  At rest (head at the right end
in state E) a mover is the word `0 0 1 1 0` followed by its gap, `g` pairs `01`:

    movers [g₁, …, gₖ] L  =  L  0 0 1 1 0 (01)^gₖ  …  0 0 1 1 0 (01)^g₁         (g₁ the rightmost)

The separators of the list, the reservoir's words (`g = 1`) and the separators Q has passed are all movers.  The left
sweep (state E reading a 0) crosses every mover and comes out on the left in the same state, reading a 0
(`left_all`).  The right sweep crosses them all again (`right_gen`): it goes in in state D (or F) and comes out in
state D; after a mover with a one-pair gap it is in state F for a while (`rm1`, `fm1`, `fm`), which changes nothing
but the first cell it writes.  Neither looks at anything outside the movers, so:

* `bounce_gen`: **any** bounce works the same way, whatever happens on the left of the movers, as long as the head,
  sent in from the right in state E on a 0, comes back out on the right in state D or F without looking at the
  right: every mover is four cells further right, the gaps between movers stay the same, and the gap between the
  last mover and the right end shrinks by one pair;
* `bounce0m`, `bounce1m`: with Q on the left, the gap between Q and the first mover grows by three pairs;
* `walkm`: k double bounces, `Q0 (c+2k), gap a+1, (n+2+2k) :: rest` → `Q0 c, gap a+1+6k, (n+2) :: rest`.

Every gap must be at least one pair, the rightmost at least two before the bounce.  Checked by Lean's kernel.
-/

namespace H71372

open TM

/-- A mover at rest with `g` pairs on its right, in front of the left tape `L` (written nearest first). -/
def mv (g : Nat) (L : Tape) : Tape :=
  rep g [true, false] (cons false (cons true (cons true (cons false (cons false L)))))

/-- Movers at rest, the rightmost first. -/
def movers : List Nat → Tape → Tape
  | [], L => L
  | g :: gs, L => mv g (movers gs L)

/-- A mover as the left sweep leaves it: `0 1 0 1 1 (01)^g` on the right of the head. -/
def W (g : Nat) (R : Tape) : Tape :=
  cons false (cons true (cons false (cons true (cons true (rep g [false, true] R)))))

/-- Swept movers on the right of the head, the leftmost first. -/
def swL : List Nat → Tape → Tape
  | [], R => R
  | g :: gs, R => W g (swL gs R)

theorem movers_append (xs ys : List Nat) (L : Tape) : movers (xs ++ ys) L = movers xs (movers ys L) := by
  induction xs with
  | nil => rfl
  | cons g xs ih => simp only [List.cons_append, movers, ih]

theorem swL_append (xs ys : List Nat) (R : Tape) : swL (xs ++ ys) R = swL xs (swL ys R) := by
  induction xs with
  | nil => rfl
  | cons g xs ih => simp only [List.cons_append, swL, ih]

/-- The cost of the left sweep over movers. -/
def lcost : List Nat → Nat
  | [] => 0
  | g :: gs => 2 * g + 15 + lcost gs

/-- The cost of the right sweep over movers (the leftmost first). -/
def rcost : List Nat → Nat
  | [] => 0
  | g :: gs => 2 * g + 5 + rcost gs

theorem lm (n : Nat) (L R : Tape) :
    steps (2 * (n + 1) + 15) ⟨mv (n + 1) L, cons false R, .E⟩ = some ⟨L, cons false (W (n + 1) R), .E⟩ :=
  steps_congr trans (by omega) (lm_cells n L R)

/-- The left sweep crosses all movers and comes out on their left, in state E reading a 0. -/
theorem left_all (gs : List Nat) (hg : ∀ g ∈ gs, 1 ≤ g) (L R : Tape) :
    steps (lcost gs) ⟨movers gs L, cons false R, .E⟩ = some ⟨L, cons false (swL gs.reverse R), .E⟩ := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by have := hg g (by simp); omega⟩
    have h1 := lm n (movers gs L) R
    have h2 := ih (fun x hx => hg x (by simp [hx])) (W (n + 1) R)
    rw [List.reverse_cons, swL_append]
    exact steps_seq trans h1 h2

theorem rm (n : Nat) (L R : Tape) :
    steps (2 * (n + 2) + 5) ⟨L, W (n + 2) R, .D⟩ =
      some ⟨cons false (mv n (cons true (cons false (cons true L)))), R, .D⟩ := by
  have h := rm_cells n L R
  have e : rep n [false, true] (cons false (cons false (cons true (cons true (cons false (cons false (cons true
      (cons false (cons true L))))))))) = cons false (mv n (cons true (cons false (cons true L)))) :=
    (rep_rotate n [false] [true, false] [false, true] rfl _).symm
  rw [e] at h
  exact steps_congr trans (by omega) h

theorem fm (n : Nat) (L R : Tape) :
    steps (2 * (n + 2) + 5) ⟨L, W (n + 2) R, .F⟩ =
      some ⟨cons false (mv n (cons true (cons false (cons false L)))), R, .D⟩ := by
  have h := fm_cells n L R
  have e : rep n [false, true] (cons false (cons false (cons true (cons true (cons false (cons false (cons true
      (cons false (cons false L))))))))) = cons false (mv n (cons true (cons false (cons false L)))) :=
    (rep_rotate n [false] [true, false] [false, true] rfl _).symm
  rw [e] at h
  exact steps_congr trans (by omega) h

/-- The right sweep crosses all movers (the leftmost first; every gap at least one pair, the last one `n + 2`)
and comes out on their right in state D; each mover is now four cells further right.  The head may enter in state
D or in state F (it is in F after a mover with a one-pair gap); the two differ only in the first cell written. -/
theorem right_gen (pre : List Nat) (hp : ∀ g ∈ pre, 1 ≤ g) (n : Nat) (R : Tape) : ∀ L : Tape,
    steps (rcost (pre ++ [n + 2])) ⟨L, swL (pre ++ [n + 2]) R, .D⟩ =
      some ⟨cons false (mv n (movers pre.reverse (cons true (cons false (cons true L))))), R, .D⟩ ∧
    steps (rcost (pre ++ [n + 2])) ⟨L, swL (pre ++ [n + 2]) R, .F⟩ =
      some ⟨cons false (mv n (movers pre.reverse (cons true (cons false (cons false L))))), R, .D⟩ := by
  induction pre with
  | nil => intro L; exact ⟨steps_congr trans (by simp [rcost]) (rm n L R),
      steps_congr trans (by simp [rcost]) (fm n L R)⟩
  | cons g pre ih =>
    intro L
    have ih' := ih (fun x hx => hp x (by simp [hx]))
    have hg := hp g (by simp)
    rw [List.reverse_cons, movers_append, movers_append]
    simp only [List.cons_append, swL, rcost, movers]
    rcases Nat.lt_or_ge g 2 with hlt | hge
    · obtain rfl : g = 1 := by omega
      have hD := steps_seq trans (rm1_cells L (swL (pre ++ [n + 2]) R))
        (ih' (cons true (cons true (cons false (cons false (cons true (cons false (cons true L)))))))).2
      have hF := steps_seq trans (fm1_cells L (swL (pre ++ [n + 2]) R))
        (ih' (cons true (cons true (cons false (cons false (cons true (cons false (cons false L)))))))).2
      exact ⟨steps_congr trans (by omega) hD, steps_congr trans (by omega) hF⟩
    · obtain ⟨m, rfl⟩ : ∃ m, g = m + 2 := ⟨g - 2, by omega⟩
      have hD := steps_seq trans (rm m L (swL (pre ++ [n + 2]) R))
        (ih' (cons false (mv m (cons true (cons false (cons true L)))))).1
      have hF := steps_seq trans (fm m L (swL (pre ++ [n + 2]) R))
        (ih' (cons false (mv m (cons true (cons false (cons false L)))))).1
      exact ⟨steps_congr trans (by omega) hD, steps_congr trans (by omega) hF⟩

/-- The D half of `right_gen`. -/
theorem right_all (pre : List Nat) (hp : ∀ g ∈ pre, 1 ≤ g) (n : Nat) (L R : Tape) :
    steps (rcost (pre ++ [n + 2])) ⟨L, swL (pre ++ [n + 2]) R, .D⟩ =
      some ⟨cons false (mv n (movers pre.reverse (cons true (cons false (cons true L))))), R, .D⟩ :=
  (right_gen pre hp n R L).1

/-- **Any bounce with movers.**  Whatever happens on the left of the movers, as long as the head, sent in from
the right in state E on a 0, comes back out on the right in state D (`hD`) or F (`hF`) without looking at the
right, the movers are carried four cells to the right and the gap of the rightmost one shrinks by one pair. -/
theorem bounce_gen (Y Y' : Tape) (s : Nat) (p : Bool)
    (hY : ∀ R : Tape, steps s ⟨Y, cons false R, .E⟩ = some ⟨Y', R, if p then .D else .F⟩)
    (n : Nat) (rest : List Nat) (hr : ∀ g ∈ rest, 1 ≤ g) :
    steps (lcost ((n + 2) :: rest) + s + rcost ((n + 2) :: rest).reverse + 1)
      ⟨movers ((n + 2) :: rest) Y, blank, .E⟩ =
      some ⟨movers ((n + 1) :: rest) (cons true (cons false (cons p Y'))), blank, .E⟩ := by
  have hg : ∀ g ∈ (n + 2) :: rest, 1 ≤ g := by
    intro g hg; simp at hg; rcases hg with rfl | hg
    · omega
    · exact hr g hg
  have h1 := left_all ((n + 2) :: rest) hg Y blank
  have e0 : (⟨movers ((n + 2) :: rest) Y, blank, .E⟩ : Config) = ⟨movers ((n + 2) :: rest) Y, cons false blank, .E⟩ := by
    rw [cons_false_blank]
  rw [e0]
  have hrev : ((n + 2) :: rest).reverse = rest.reverse ++ [n + 2] := List.reverse_cons
  have hp : ∀ g ∈ rest.reverse, 1 ≤ g := fun g hg' => hr g (List.mem_reverse.mp hg')
  have h2 := hY (swL ((n + 2) :: rest).reverse blank)
  have hR := right_gen rest.reverse hp n blank Y'
  rw [List.reverse_reverse] at hR
  have h4 : ∀ Z : Tape, steps 1 ⟨cons false (mv n Z), blank, .D⟩ = some ⟨mv (n + 1) Z, blank, .E⟩ := fun _ => rfl
  rw [hrev] at h1 h2 ⊢
  cases p with
  | true =>
    have h := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans hR.1 (h4 _)))
    simp only [movers] at h ⊢
    exact steps_congr trans (by omega) h
  | false =>
    have h := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans hR.2 (h4 _)))
    simp only [movers] at h ⊢
    exact steps_congr trans (by omega) h

/-- At the right end: Q (`q`), with `c` pairs on its left and `a` on its right, then the movers `gs`, the head in
state E on the blank. -/
def Cfgm (q : Bool) (c a : Nat) (gs : List Nat) (L : Tape) : Config :=
  ⟨movers gs (rep a [true, false] (cons q (rep c [true, false] L))), blank, .E⟩

/-- The cost of one bounce with Q's gap `a + 1` and movers `gs` (the rightmost first): left sweep, the turn at Q
(`base` = 13 for the short form, 9 for the long), right sweep and the last step. -/
def bcost (base a : Nat) (gs : List Nat) : Nat := lcost gs + (4 * a + base) + rcost gs.reverse + 1

theorem bounce_m (q : Bool) (base : Nat) (hq : ∀ (c : Nat) (L R : Tape),
      steps (4 * a + base) ⟨rep (a + 1) [true, false] (cons q (rep (c + 1) [true, false] L)), cons false R, .E⟩ =
        some ⟨rep (a + 1) [false, true] (cons false (cons true (cons false (cons (!q) (rep c [true, false] L))))),
          R, .D⟩)
    (c n : Nat) (rest : List Nat) (hr : ∀ g ∈ rest, 1 ≤ g) (L : Tape) :
    steps (bcost base a ((n + 2) :: rest)) (Cfgm q (c + 1) (a + 1) ((n + 2) :: rest) L) =
      some (Cfgm (!q) c (a + 4) ((n + 1) :: rest) L) := by
  have hg : ∀ g ∈ (n + 2) :: rest, 1 ≤ g := by
    intro g hg; simp at hg; rcases hg with rfl | hg
    · omega
    · have := hr g hg; omega
  have h1 := left_all ((n + 2) :: rest) hg (rep (a + 1) [true, false] (cons q (rep (c + 1) [true, false] L))) blank
  rw [cons_false_blank] at h1
  have h2 := hq c L (swL ((n + 2) :: rest).reverse blank)
  rw [← cons_false_blank] at h2
  have hp : ∀ g ∈ rest.reverse, 1 ≤ g := fun g hg' => hr g (List.mem_reverse.mp hg')
  have h3 := right_all rest.reverse hp n
    (rep (a + 1) [false, true] (cons false (cons true (cons false (cons (!q) (rep c [true, false] L)))))) blank
  rw [List.reverse_reverse] at h3
  rw [rebracket (a + 1) (!q) (rep c [true, false] L), show a + 1 + 3 = a + 4 by omega] at h3
  have h4 : ∀ Y : Tape, steps 1 ⟨cons false (mv n Y), blank, .D⟩ = some ⟨mv (n + 1) Y, blank, .E⟩ := fun _ => rfl
  have h4 := h4 (movers rest (rep (a + 4) [true, false] (cons (!q) (rep c [true, false] L))))
  have hrev : ((n + 2) :: rest).reverse = rest.reverse ++ [n + 2] := List.reverse_cons
  rw [hrev] at h1 h2
  rw [cons_false_blank] at h2
  have h := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))
  unfold Cfgm bcost
  rw [hrev]
  simp only [movers] at h ⊢
  exact steps_congr trans (by omega) h

theorem bounce0m (a c n : Nat) (rest : List Nat) (hr : ∀ g ∈ rest, 1 ≤ g) (L : Tape) :
    steps (bcost 13 a ((n + 2) :: rest)) (Cfgm false (c + 1) (a + 1) ((n + 2) :: rest) L) =
      some (Cfgm true c (a + 4) ((n + 1) :: rest) L) :=
  bounce_m false 13 (fun c L R => qr0_cells a c L R) c n rest hr L

theorem bounce1m (a c n : Nat) (rest : List Nat) (hr : ∀ g ∈ rest, 1 ≤ g) (L : Tape) :
    steps (bcost 9 a ((n + 2) :: rest)) (Cfgm true (c + 1) (a + 1) ((n + 2) :: rest) L) =
      some (Cfgm false c (a + 4) ((n + 1) :: rest) L) :=
  bounce_m true 9 (fun c L R => qr1_cells a c L R) c n rest hr L

/-- The cost of k double bounces. -/
def wmcost : Nat → Nat → Nat → List Nat → Nat
  | _, _, 0, _ => 0
  | a, n, k + 1, rest => bcost 13 a ((n + 2 * k + 4) :: rest) + bcost 9 (a + 3) ((n + 2 * k + 3) :: rest)
      + wmcost (a + 6) n k rest

/-- **Walk with movers**: k double bounces carry Q 2k pairs to the left and every mover 4k pairs to the right. -/
theorem walkm (k c a n : Nat) (rest : List Nat) (hr : ∀ g ∈ rest, 1 ≤ g) (L : Tape) :
    steps (wmcost a n k rest) (Cfgm false (c + 2 * k) (a + 1) ((n + 2 * k + 2) :: rest) L) =
      some (Cfgm false c (a + 1 + 6 * k) ((n + 2) :: rest) L) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    have h1 := bounce0m a (c + 2 * k + 1) (n + 2 * k + 2) rest hr L
    have h2 := bounce1m (a + 3) (c + 2 * k) (n + 2 * k + 1) rest hr L
    have h3 := ih (a + 6)
    rw [show c + 2 * k + 1 + 1 = c + 2 * (k + 1) by omega, show n + 2 * k + 2 + 2 = n + 2 * (k + 1) + 2 by omega,
      show n + 2 * k + 2 + 1 = n + 2 * k + 1 + 2 by omega] at h1
    rw [show a + 3 + 1 = a + 4 by omega, show a + 3 + 4 = a + 6 + 1 by omega,
      show n + 2 * k + 1 + 1 = n + 2 * k + 2 by omega] at h2
    rw [show a + 6 + 1 + 6 * k = a + 1 + 6 * (k + 1) by omega] at h3
    have h := steps_seq trans h1 (steps_seq trans h2 h3)
    simp only [wmcost]
    rw [show n + 2 * k + 4 = n + 2 * (k + 1) + 2 by omega, show n + 2 * k + 3 = n + 2 * k + 1 + 2 by omega]
    exact steps_congr trans (by omega) h

end H71372
