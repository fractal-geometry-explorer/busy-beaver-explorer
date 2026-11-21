import Danger

/-!
# The two deep sweeps at a `10` defect, for every length

A deep sweep is a round trip that reaches a bulk `10` defect `T` and turns at the `0` after the gap.  Write `P` for the
words before the word in front of `T` and `G` for the gap (words, `x = false`, `y = true`).

* `shielded`: `P x T G y 0` becomes `x102 P x, T, x102 (y G y) y, 1`.  The defect moves one word to the left; in the
  defect's frame the whole line `P x (T as y) G y` is one row of rule 102 (`x102_shielded` below).
* `jump`: with `y` in front, `P y T y^j x^(a+1) C y 0` (`C` empty or starting with `y`) becomes
  `x102 (P y) x, x^(j+a+1), T, x102 (C y) y, 1`.  The defect jumps over the `y`s and the first block of `x`s and lands
  in the block's last slot; the words it jumped over become `x`, so the next `j + a + 1` sweeps are shielded.
* With no `x` in the gap, `P y T y^n 0` halts (`danger_halts` in `Danger.lean`).

So the danger pattern is the jump with nothing to jump to.  Both rules are checked against the machine for all short
words in `py/hop_rule.py` and against every deep sweep of the real run to `1.2 * 10^7` steps.
-/

namespace H696

open TM

/-! ## Tape bookkeeping -/

theorem two_ones (X : Tape) (h0 : X 0 = true) (h1 : X 1 = true) : X = cons true (cons true (tail (tail X))) := by
  funext n
  rcases n with _ | _ | n
  · exact h0
  · exact h1
  · rfl

theorem enc_head (ws : List Bool) (R : Tape) (h0 : R 0 = true) (h1 : R 1 = true) :
    enc ws R 0 = true ∧ enc ws R 1 = true := by
  cases ws with
  | nil => exact ⟨h0, h1⟩
  | cons a ws => cases a <;> exact ⟨rfl, rfl⟩

/-- B over a word string followed by two 1s: each `x` becomes `000`, each `y` becomes `011`. -/
theorem rpre (ws : List Bool) : ∀ (L R : Tape), R 0 = true → R 1 = true →
    steps (rc ws) ⟨L, enc ws R, .B⟩ = some ⟨swL ws L, R, .B⟩ := by
  induction ws with
  | nil => intro L R _ _; rfl
  | cons a ws ih =>
    intro L R h0 h1
    have ih' := ih
    cases a with
    | false =>
      obtain ⟨e0, e1⟩ := enc_head ws R h0 h1
      have h := rx L (tail (tail (enc ws R)))
      rw [← two_ones _ e0 e1] at h
      exact steps_seq trans h (ih' (app [false, false, false] L) R h0 h1)
    | true =>
      exact steps_seq trans (ry L (enc ws R)) (ih' (app [true, true, false] L) R h0 h1)

theorem enc_rep_true (j : Nat) (R : Tape) : enc (List.replicate j true) R = rep j [true, true, false] R := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [List.replicate_succ, enc, ih, wd, rep_succ]

theorem enc_rep_false (j : Nat) (R : Tape) : enc (List.replicate j false) R = rep j [true, true, true] R := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [List.replicate_succ, enc, ih, wd, rep_succ]

theorem swL_rep_false (j : Nat) : ∀ L : Tape, swL (List.replicate j false) L = rep j [false, false, false] L := by
  induction j with
  | zero => intro L; rfl
  | succ j ih =>
    intro L
    rw [List.replicate_succ, swL, ih, sw, rep_app_comm]

theorem rep3 (k : Nat) (S : Tape) : rep k [false, false, false] S = rep (3 * k) [false] S := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : 3 * (k + 1) = 1 + (1 + (1 + 3 * k)) := by omega
    rw [rep_succ, ih, e, rep_add, rep_add, rep_add]; rfl

/-- `B 1 1 1 → 0 B 1 1`: one zigzag of the right sweep inside a run of 1s. -/
theorem zig1 (L R : Tape) :
    steps 3 ⟨L, cons true (cons true (cons true R)), .B⟩ = some ⟨cons false L, cons true (cons true R), .B⟩ := rfl

/-- **A run** `1^(m+2) 0` becomes `0^(m+1) 1 1`, B after it. -/
theorem run (m : Nat) : ∀ L R : Tape,
    steps (3 * m + 3) ⟨L, rep (m + 2) [true] (cons false R), .B⟩ = some ⟨app [true, true, false] (rep m [false] L), R, .B⟩ := by
  induction m with
  | zero => intro L R; rfl
  | succ m ih =>
    intro L R
    have h1 : steps 3 ⟨L, rep (m + 1 + 2) [true] (cons false R), .B⟩ =
        some ⟨cons false L, rep (m + 2) [true] (cons false R), .B⟩ := zig1 L _
    have h2 := ih (cons false L) R
    have e : 3 * (m + 1) + 3 = 3 + (3 * m + 3) := by omega
    rw [e]
    refine steps_seq trans h1 ?_
    have e2 : rep (m + 1) [false] L = rep m [false] (cons false L) := by
      rw [← rep_app_comm]; rfl
    rw [e2]; exact h2

theorem rep_ones_x (a : Nat) (X : Tape) : rep (3 * a) [true] X = rep a [true, true, true] X := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have e : 3 * (a + 1) = 1 + (1 + (1 + 3 * a)) := by omega
    rw [e, rep_add, rep_add, rep_add, ih]; rfl

/-! ## The left sweep over the defect -/

/-- The left sweep in C (a `y` to the right) reads the `00` the right sweep left at the defect and writes `10`. -/
theorem lT (Y R : Tape) :
    steps 2 (onL (app [false, false] Y) R .C) = some (onL Y (app [true, false] R) .E) := by
  rw [eta Y]; cases Y 0 <;> rfl

theorem x102_rep (ws : List Bool) (n : Nat) :
    x102 (ws ++ List.replicate n false) false = x102 ws false ++ List.replicate n false := by
  induction ws with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
        show bne false false :: x102 (List.replicate (n + 1) false) false = _
        rw [show x102 (List.replicate (n + 1) false) false = List.replicate (n + 1) false from ih]; rfl
  | cons a ws ih =>
    show bne a (hd (ws ++ List.replicate n false) false) :: x102 (ws ++ List.replicate n false) false =
      bne a (hd ws false) :: x102 ws false ++ List.replicate n false
    rw [ih]
    cases ws with
    | nil => cases n <;> rfl
    | cons b ws => rfl

theorem hd_append (ws vs : List Bool) (q : Bool) (h : ws ≠ []) : hd (ws ++ vs) q = hd ws q := by
  cases ws with
  | nil => exact absurd rfl h
  | cons a ws => rfl

/-! ## The shielded sweep -/

/-- **Shielded deep sweep.**  `P x T G y 0` becomes `x102 P x, T, x102 (y G y) y, 1`, head just left of it. -/
theorem shielded (P G : List Bool) (L R : Tape) :
    ∃ n, steps n ⟨L, enc (P ++ [false]) (app [true, false] (enc (G ++ [true]) (cons false R))), .B⟩ =
      some (onL L (enc (x102 P false) (app [true, false] (enc (x102 (true :: G ++ [true]) true) (cons true R))))
        (ps (hd P false))) := by
  have e0 : enc (P ++ [false]) (app [true, false] (enc (G ++ [true]) (cons false R))) =
      enc P (app [true, true, true, true, false] (enc (G ++ [true]) (cons false R))) := by
    rw [enc_append]; rfl
  rw [e0]
  have h1 := rpre P L (app [true, true, true, true, false] (enc (G ++ [true]) (cons false R))) rfl rfl
  have h2 := shield (swL P L) (enc (G ++ [true]) (cons false R))
  have h3 : steps (rc G + 3) ⟨app [true, true, false, false, false] (swL P L), enc (G ++ [true]) (cons false R), .B⟩ =
      some ⟨swL (G ++ [true]) (app [true, true, false, false, false] (swL P L)), cons false R, .B⟩ := by
    rw [enc_append]; exact rsweep G (cons false R) _
  have h4 : steps 1 ⟨swL (G ++ [true]) (app [true, true, false, false, false] (swL P L)), cons false R, .B⟩ =
      some (onL (swL (G ++ [true]) (app [true, true, false, false, false] (swL P L))) (cons true R) (ps true)) := rfl
  have e1 : swL (G ++ [true]) (app [true, true, false, false, false] (swL P L)) =
      swL (true :: G ++ [true]) (app [false, false] (swL P L)) := by
    show _ = swL (G ++ [true]) (app (sw true) (app [false, false] (swL P L)))
    rfl
  rw [e1] at h4
  have h5 := lsweep (true :: G ++ [true]) true (cons true R) (app [false, false] (swL P L))
  have h6 := lT (swL P L) (enc (x102 (true :: G ++ [true]) true) (cons true R))
  have h7 := lsweep P false (app [true, false] (enc (x102 (true :: G ++ [true]) true) (cons true R))) L
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans
    (steps_seq trans h1 h2) h3) h4) h5) h6) h7⟩

/-! ## The jump -/

/-- The right sweep from the defect to the end of the first `x` block: `T y^j x (x^a) y` with B on the `T`.  Token mode
crosses the `y`s, the first `x` sends B back into ordinary mode one cell late, and the rest is one run of 1s. -/
theorem jump_core (S Rv : Tape) (j a : Nat) :
    ∃ n, steps n ⟨S, app [true, false] (rep j [true, true, false] (app [true, true, true]
        (rep a [true, true, true] (app [true, true, false] Rv)))), .B⟩ =
      some ⟨swL [true] (app [false, false] (swL (List.replicate (j + a + 1) false) S)), Rv, .B⟩ := by
  -- B on the defect `1 0` goes into token mode
  have h2 : steps 2 ⟨S, app [true, false] (rep j [true, true, false] (app [true, true, true]
        (rep a [true, true, true] (app [true, true, false] Rv)))), .B⟩ =
      some ⟨app [false, false] S, rep j [true, true, false] (app [true, true, true]
        (rep a [true, true, true] (app [true, true, false] Rv))), .F⟩ := rfl
  -- F crosses the `y`s
  have h3 := token_y j (app [false, false] S) (app [true, true, true] (rep a [true, true, true] (app [true, true, false] Rv)))
  simp only [app_nil] at h3
  -- F on the first `x`: `F 1 → 0 B`, `B 1 → 0 D`, `D 1 → 1 A`, `A 1 → 1 L B`: back in B on the `x`'s last cell
  have h4 : steps 4 ⟨rep j [false, false, false] (app [false, false] S),
        app [true, true, true] (rep a [true, true, true] (app [true, true, false] Rv)), .F⟩ =
      some ⟨app [false, false] (rep j [false, false, false] (app [false, false] S)),
        cons true (rep a [true, true, true] (app [true, true, false] Rv)), .B⟩ := by
    have e : rep a [true, true, true] (app [true, true, false] Rv) =
        cons true (cons true (tail (tail (rep a [true, true, true] (app [true, true, false] Rv))))) := by
      apply two_ones <;> cases a <;> rfl
    rw [e]; rfl
  -- the run `1 (111)^a 11 0` (the `x`'s last cell, `a` more `x`s and the `y`) is an ordinary run of the right sweep
  have h5 := run (3 * a + 1) (app [false, false] (rep j [false, false, false] (app [false, false] S))) Rv
  have e5 : cons true (rep a [true, true, true] (app [true, true, false] Rv)) =
      rep (3 * a + 1 + 2) [true] (cons false Rv) := by
    rw [← rep_ones_x]
    have e : 3 * a + 1 + 2 = 1 + (3 * a + 2) := by omega
    rw [e, rep_add]
    show cons true (rep (3 * a) [true] (cons true (cons true (cons false Rv)))) =
      cons true (rep (3 * a + 2) [true] (cons false Rv))
    rw [rep_add]; rfl
  rw [← e5] at h5
  -- what the right sweep left behind: `y` over the run's end, zeros back to the defect
  have eZ : app [true, true, false] (rep (3 * a + 1) [false] (app [false, false] (rep j [false, false, false]
        (app [false, false] S)))) =
      swL [true] (app [false, false] (swL (List.replicate (j + a + 1) false) S)) := by
    show app [true, true, false] _ = app [true, true, false] _
    congr 1
    rw [swL_rep_false, rep3, rep3]
    show rep (3 * a + 1) [false] (rep 2 [false] (rep (3 * j) [false] (rep 2 [false] S))) =
      rep 2 [false] (rep (3 * (j + a + 1)) [false] S)
    rw [← rep_add, ← rep_add, ← rep_add, ← rep_add]
    congr 1; omega
  rw [eZ] at h5
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans h2 h3) h4) h5⟩

/-- **The defect jumps.**  `P y T y^j x^(a+1) C y 0`, with `C` empty or starting with `y`, becomes
`x102 (P y) x, x^(j+a+1), T, x102 (C y) y, 1`, head just left of it. -/
theorem jump (P C : List Bool) (j a : Nat) (hC : hd C true = true) (L R : Tape) :
    ∃ n, steps n ⟨L, enc (P ++ [true]) (app [true, false]
        (enc (List.replicate j true ++ List.replicate (a + 1) false ++ C ++ [true]) (cons false R))), .B⟩ =
      some (onL L (enc (x102 (P ++ [true]) false ++ List.replicate (j + a + 1) false)
        (app [true, false] (enc (x102 (C ++ [true]) true) (cons true R)))) (ps (hd (P ++ [true]) false))) := by
  -- the rest of the string, `C y`, as a `y` followed by the words after it
  obtain ⟨vs, hv1, hv2⟩ : ∃ vs, C ++ [true] = true :: vs ∧ (vs = [] ∨ ∃ us, vs = us ++ [true]) := by
    cases C with
    | nil => exact ⟨[], rfl, Or.inl rfl⟩
    | cons c us =>
      have : c = true := hC
      subst this
      exact ⟨us ++ [true], rfl, Or.inr ⟨us, rfl⟩⟩
  have eR : enc (List.replicate j true ++ List.replicate (a + 1) false ++ C ++ [true]) (cons false R) =
      rep j [true, true, false] (app [true, true, true] (rep a [true, true, true]
        (app [true, true, false] (enc vs (cons false R))))) := by
    rw [List.append_assoc, List.append_assoc, enc_append, enc_rep_true, enc_append, hv1, List.replicate_succ, enc,
      enc_rep_false]
    rfl
  rw [eR]
  -- the right sweep up to the defect
  have h1 : steps (rc P + 3) ⟨L, enc (P ++ [true]) (app [true, false] (rep j [true, true, false] (app [true, true, true]
        (rep a [true, true, true] (app [true, true, false] (enc vs (cons false R))))))), .B⟩ =
      some ⟨swL (P ++ [true]) L, app [true, false] (rep j [true, true, false] (app [true, true, true]
        (rep a [true, true, true] (app [true, true, false] (enc vs (cons false R)))))), .B⟩ := by
    rw [enc_append]; exact rsweep P _ L
  obtain ⟨m2, h2⟩ := jump_core (swL (P ++ [true]) L) (enc vs (cons false R)) j a
  -- the rest of the right sweep and the turn
  have h6 : ∃ m, steps m ⟨swL [true] (app [false, false] (swL (List.replicate (j + a + 1) false) (swL (P ++ [true]) L))),
        enc vs (cons false R), .B⟩ =
      some (onL (swL (C ++ [true]) (app [false, false] (swL (List.replicate (j + a + 1) false) (swL (P ++ [true]) L))))
        (cons true R) (ps true)) := by
    rcases hv2 with h | ⟨us, h⟩
    · subst h
      rw [hv1]
      exact ⟨1, rfl⟩
    · subst h
      have hr := rsweep us (cons false R)
        (swL [true] (app [false, false] (swL (List.replicate (j + a + 1) false) (swL (P ++ [true]) L))))
      have ee : enc (us ++ [true]) (cons false R) = enc us (app [true, true, false] (cons false R)) := by
        rw [enc_append]; rfl
      have ht : steps 1 ⟨swL (us ++ [true]) (swL [true] (app [false, false] (swL (List.replicate (j + a + 1) false)
            (swL (P ++ [true]) L)))), cons false R, .B⟩ =
          some (onL (swL (us ++ [true]) (swL [true] (app [false, false] (swL (List.replicate (j + a + 1) false)
            (swL (P ++ [true]) L))))) (cons true R) (ps true)) := rfl
      rw [← swL_append] at ht
      rw [hv1, ee]
      exact ⟨_, steps_seq trans hr ht⟩
  obtain ⟨m6, h6⟩ := h6
  -- the left sweep over `C y`, the defect, and the rest
  have h7 := lsweep (C ++ [true]) true (cons true R)
    (app [false, false] (swL (List.replicate (j + a + 1) false) (swL (P ++ [true]) L)))
  have hhd : hd (C ++ [true]) true = true := by rw [hv1]; rfl
  rw [hhd] at h7
  have h8 := lT (swL (List.replicate (j + a + 1) false) (swL (P ++ [true]) L)) (enc (x102 (C ++ [true]) true) (cons true R))
  have h9 := lsweep (P ++ [true] ++ List.replicate (j + a + 1) false) false
    (app [true, false] (enc (x102 (C ++ [true]) true) (cons true R))) L
  rw [swL_append, x102_rep, hd_append _ _ _ (by simp)] at h9
  exact ⟨_, steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans (steps_seq trans h1 h2) h6) h7) h8) h9⟩

/-! ## The line view -/

theorem x102_append (ws vs : List Bool) (q : Bool) : x102 (ws ++ vs) q = x102 ws (hd vs q) ++ x102 vs q := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    show bne a (hd (ws ++ vs) q) :: x102 (ws ++ vs) q = bne a (hd ws (hd vs q)) :: x102 ws (hd vs q) ++ x102 vs q
    rw [ih]
    cases ws <;> rfl

/-- **One line.**  Count the defect as a `y`.  Then the shielded sweep is rule 102 on the whole line `P x T G y`: the
words `x102 P x`, then the value `x xor y = y` in the slot where the defect now sits, then `x102 (y G y) y`. -/
theorem x102_shielded (P G : List Bool) :
    x102 (P ++ [false, true] ++ G ++ [true]) true = x102 P false ++ [true] ++ x102 (true :: G ++ [true]) true := by
  rw [List.append_assoc, List.append_assoc, x102_append, List.append_assoc]
  rfl

/-! ## The jump clock -/

/-- What a shielded sweep does to the words before the defect (`shielded`: `P x` becomes `x102 P x`). -/
def lstep (L : List Bool) : List Bool := x102 L.dropLast false

/-- `k` shielded sweeps. -/
def liter : Nat → List Bool → List Bool
  | 0, L => L
  | k + 1, L => lstep (liter k L)

theorem lstep_tick (Q : List Bool) (n : Nat) :
    lstep (Q ++ true :: List.replicate (n + 1) false) = x102 Q true ++ true :: List.replicate n false := by
  have e0 : Q ++ true :: List.replicate (n + 1) false = (Q ++ [true] ++ List.replicate n false) ++ [false] := by
    simp [List.replicate_succ']
  have e : (Q ++ true :: List.replicate (n + 1) false).dropLast = Q ++ [true] ++ List.replicate n false := by
    rw [e0, List.dropLast_concat]
  unfold lstep
  rw [e, x102_rep, x102_append, List.append_assoc]
  rfl

/-- **The clock.**  After a jump over `m` slots the words before the defect are `Q y x^m` (`jump`).  Then the next `m`
sweeps are shielded, and after them the word before the defect is `y`, so the sweep after those is again a jump (or a
merge, or the danger pattern): `k ≤ m` shielded sweeps leave `Q' y x^(m-k)`. -/
theorem clock (m : Nat) : ∀ k, k ≤ m → ∀ Q : List Bool,
    ∃ Q', liter k (Q ++ true :: List.replicate m false) = Q' ++ true :: List.replicate (m - k) false := by
  intro k
  induction k with
  | zero => intro _ Q; exact ⟨Q, rfl⟩
  | succ k ih =>
    intro hk Q
    obtain ⟨Q', h⟩ := ih (by omega) Q
    refine ⟨x102 Q' true, ?_⟩
    show lstep (liter k _) = _
    rw [h]
    have e : m - k = (m - (k + 1)) + 1 := by omega
    rw [e, lstep_tick]

end H696
