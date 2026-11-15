import Zone

/-!
# 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE: many visits of a zone at once

In the coordinates `N_0 = n_0 - s_1`, `N_j = n_j + s_j - s_(j+1)`, `N_k = n_k + s_k` a visit of a zone is a plain
binary increment in which the count paired with a bit loses 1 when that bit is set, and `N_0` gains 2.  A zone in
these coordinates is a list `ps` of pairs (bit `s_j`, `N_(j-1)`), `j = 1..k`, and the number `top = N_k`.

* `incN`: the increment.  `addV V`: `V` increments at once, in closed form (bit `j` sees `V_j` increments, half of
  them set it).  `addV_succ`: one more increment after `addV V` is `addV (V + 1)`.
* `physP`, `n0of`: back to the counts on the tape.  `inc_physP`: on a zone with every `N_j >= 2`, `incN` is the
  `inc` of `Zone.lean`.
* `jump`: if the bits do not overflow in `V` visits and every `N_j` is still at least 2 after them, the machine
  goes from the zone `ps` to the zone after `V` visits.
-/

namespace H172044

open TM

/-- The binary increment in N coordinates. -/
def incN : List (Bool × Nat) → Option (List (Bool × Nat))
  | [] => none
  | (false, M) :: r => some ((true, M - 1) :: r)
  | (true, M) :: r => (incN r).map (fun r' => (false, M) :: r')

/-- `V` increments at once. -/
def addV : Nat → List (Bool × Nat) → List (Bool × Nat)
  | _, [] => []
  | V, (b, M) :: r => ((V + b.toNat) % 2 == 1, M - (V + 1 - b.toNat) / 2) :: addV ((V + b.toNat) / 2) r

/-- The carry out of the last bit after `V` increments. -/
def ovf : Nat → List (Bool × Nat) → Nat
  | V, [] => V
  | V, (b, _) :: r => ovf ((V + b.toNat) / 2) r

/-- Add `d` to the first count. -/
def bump (d : Nat) : List (Bool × Nat) → List (Bool × Nat)
  | [] => []
  | (b, M) :: r => (b, M + d) :: r

theorem addV_zero : ∀ ps : List (Bool × Nat), addV 0 ps = ps
  | [] => rfl
  | (b, M) :: r => by
    have ih := addV_zero r
    cases b <;> simp [addV, ih]

theorem ovf_succ : ∀ (ps : List (Bool × Nat)) (V : Nat), ovf (V + 1) ps = 0 → ovf V ps = 0
  | [], V, h => by simp [ovf] at h
  | (b, M) :: r, V, h => by
    simp only [ovf] at h ⊢
    have hc : (V + 1 + b.toNat) / 2 = (V + b.toNat) / 2 ∨ (V + 1 + b.toNat) / 2 = (V + b.toNat) / 2 + 1 := by omega
    rcases hc with hc | hc
    · rw [hc] at h; exact h
    · rw [hc] at h; exact ovf_succ r _ h

theorem addV_succ : ∀ (ps : List (Bool × Nat)) (V : Nat), ovf (V + 1) ps = 0 →
    incN (addV V ps) = some (addV (V + 1) ps)
  | [], V, h => by simp [ovf] at h
  | (b, M) :: r, V, h => by
    simp only [ovf] at h
    simp only [addV]
    rcases Nat.mod_two_eq_zero_or_one (V + b.toNat) with hp | hp
    · -- the bit is 0 after V increments: it is set
      have e1 : ((V + b.toNat) % 2 == 1) = false := by simp [hp]
      have e2 : ((V + 1 + b.toNat) % 2 == 1) = true := by
        have : (V + 1 + b.toNat) % 2 = 1 := by omega
        simp [this]
      have e3 : (V + 1 + b.toNat) / 2 = (V + b.toNat) / 2 := by omega
      have e4 : M - (V + 1 - b.toNat) / 2 - 1 = M - (V + 1 + 1 - b.toNat) / 2 := by
        cases b <;> simp at hp ⊢ <;> omega
      rw [e1, e2, e3]
      simp only [incN]
      rw [e4]
    · -- the bit is 1: it is cleared and the carry goes on
      have e1 : ((V + b.toNat) % 2 == 1) = true := by simp [hp]
      have e2 : ((V + 1 + b.toNat) % 2 == 1) = false := by
        have : (V + 1 + b.toNat) % 2 = 0 := by omega
        simp [this]
      have e3 : (V + 1 + b.toNat) / 2 = (V + b.toNat) / 2 + 1 := by omega
      have e4 : M - (V + 1 - b.toNat) / 2 = M - (V + 1 + 1 - b.toNat) / 2 := by
        cases b <;> simp at hp ⊢ <;> omega
      rw [e3] at h
      rw [e1, e2, e3]
      simp only [incN]
      rw [addV_succ r _ h, e4]
      rfl

/-! ## Back to the tape -/

/-- The (bit, count) pairs of `Zone.lean` for a zone given in N coordinates. -/
def physP : List (Bool × Nat) → Nat → List (Bool × Nat)
  | [], _ => []
  | [(b, _)], top => [(b, top - b.toNat)]
  | (b, _) :: (b', M') :: rest, top => (b, M' + b'.toNat - b.toNat) :: physP ((b', M') :: rest) top

/-- The last counter. -/
def n0of : List (Bool × Nat) → Nat
  | [] => 0
  | (b, M) :: _ => M + b.toNat

/-- Every count at least 2. -/
def goodAll : List (Bool × Nat) → Bool
  | [] => true
  | (_, M) :: r => decide (2 ≤ M) && goodAll r

/-- Every `N_j` with `j >= 1` at least 2. -/
def goodN (ps : List (Bool × Nat)) (top : Nat) : Bool :=
  match ps with
  | [] => false
  | _ :: r => goodAll r && decide (2 ≤ top)

theorem hd_physP : ∀ (ps : List (Bool × Nat)) (top : Nat), hd (physP ps top) = hd ps
  | [], _ => rfl
  | [(_, _)], _ => rfl
  | (_, _) :: (_, _) :: _, _ => rfl

theorem physP_bump (d : Nat) : ∀ (ps : List (Bool × Nat)) (top : Nat), physP (bump d ps) top = physP ps top
  | [], _ => rfl
  | [(_, _)], _ => rfl
  | (_, _) :: (_, _) :: _, _ => rfl

theorem hd_incN : ∀ (ps ps' : List (Bool × Nat)), incN ps = some ps' → hd ps' = !hd ps
  | [], _, h => by simp [incN] at h
  | (false, M) :: r, ps', h => by
    simp only [incN] at h
    have e : ps' = (true, M - 1) :: r := by simpa using h.symm
    subst e; rfl
  | (true, M) :: r, ps', h => by
    simp only [incN] at h
    cases hi : incN r with
    | none => rw [hi] at h; simp at h
    | some r' =>
      rw [hi] at h
      have e : ps' = (false, M) :: r' := by simpa using h.symm
      subst e; rfl

/-- On a zone whose `N_j` are all at least 2, the increment in N coordinates is the `inc` of the tape. -/
theorem inc_physP (top : Nat) (htop : 2 ≤ top) : ∀ (ps ps' : List (Bool × Nat)),
    goodAll ps.tail = true → incN ps = some ps' → inc (physP ps top) = some (physP ps' top)
  | [], _, _, h => by simp [incN] at h
  | [(false, M)], ps', _, h => by
    simp only [incN] at h
    have e : ps' = [(true, M - 1)] := by simpa using h.symm
    subst e
    have : top ≠ 0 := by omega
    simp [physP, inc, this]
  | [(true, M)], ps', _, h => by simp [incN] at h
  | (false, M) :: (b', M') :: rest, ps', hg, h => by
    simp only [incN] at h
    have e : ps' = (true, M - 1) :: (b', M') :: rest := by simpa using h.symm
    subst e
    simp only [List.tail, goodAll, Bool.and_eq_true, decide_eq_true_eq] at hg
    simp [physP, inc]
    intro h0; omega
  | (true, M) :: (b', M') :: rest, ps', hg, h => by
    simp only [incN] at h
    cases hi : incN ((b', M') :: rest) with
    | none => rw [hi] at h; simp at h
    | some q =>
      rw [hi] at h
      have e : ps' = (false, M) :: q := by simpa using h.symm
      subst e
      simp only [List.tail, goodAll, Bool.and_eq_true, decide_eq_true_eq] at hg
      have ih := inc_physP top htop ((b', M') :: rest) q (by
        cases rest with
        | nil => rfl
        | cons x rest' => exact hg.2) hi
      have hq : hd q = !b' := hd_incN _ _ hi
      -- the shape of q
      cases q with
      | nil => cases b' <;> simp [incN] at hi <;> (cases hj : incN rest <;> rw [hj] at hi <;> simp at hi)
      | cons x q' =>
        obtain ⟨b'', M''⟩ := x
        have hb : b'' = !b' := hq
        have hM : M'' + b''.toNat = if b' then M' + b'.toNat - 1 else M' + b'.toNat - 1 + 1 := by
          cases b' with
          | false =>
            simp only [incN] at hi
            have e : (true, M' - 1) :: rest = (b'', M'') :: q' := by simpa using hi
            injection e with e1 e2
            injection e1 with e3 e4
            subst e3; subst e4
            simp
          | true =>
            simp only [incN] at hi
            cases hj : incN rest with
            | none => rw [hj] at hi; simp at hi
            | some z =>
              rw [hj] at hi
              have e : (false, M') :: z = (b'', M'') :: q' := by simpa using hi
              injection e with e1 e2
              injection e1 with e3 e4
              subst e3; subst e4
              simp
        have hne : M' + b'.toNat - 1 ≠ 0 := by cases b' <;> simp <;> omega
        show inc ((true, M' + b'.toNat - true.toNat) :: physP ((b', M') :: rest) top) =
          some ((false, M'' + b''.toNat - false.toNat) :: physP ((b'', M'') :: q') top)
        rw [inc]
        simp only [Bool.toNat_true, Bool.toNat_false, hne, ite_false, ih, Option.map_some, hd_physP,
          Nat.sub_zero]
        simp only [hd, hM]
        first | rfl | (cases b' <;> rfl) | simp

/-- A count never grows in an increment. -/
theorem goodAll_incN : ∀ (ps ps' : List (Bool × Nat)), incN ps = some ps' → goodAll ps' = true → goodAll ps = true
  | [], _, h, _ => by simp [incN] at h
  | (false, M) :: r, ps', h, hg => by
    simp only [incN] at h
    have e : ps' = (true, M - 1) :: r := by simpa using h.symm
    subst e
    simp only [goodAll, Bool.and_eq_true, decide_eq_true_eq] at hg ⊢
    exact ⟨by omega, hg.2⟩
  | (true, M) :: r, ps', h, hg => by
    simp only [incN] at h
    cases hi : incN r with
    | none => rw [hi] at h; simp at h
    | some r' =>
      rw [hi] at h
      have e : ps' = (false, M) :: r' := by simpa using h.symm
      subst e
      simp only [goodAll, Bool.and_eq_true, decide_eq_true_eq] at hg ⊢
      exact ⟨hg.1, goodAll_incN r r' hi hg.2⟩

theorem goodN_incN (top : Nat) : ∀ (ps ps' : List (Bool × Nat)), incN ps = some ps' → goodN ps' top = true →
    goodN ps top = true
  | [], _, h, _ => by simp [incN] at h
  | (false, M) :: r, ps', h, hg => by
    simp only [incN] at h
    have e : ps' = (true, M - 1) :: r := by simpa using h.symm
    subst e; exact hg
  | (true, M) :: r, ps', h, hg => by
    simp only [incN] at h
    cases hi : incN r with
    | none => rw [hi] at h; simp at h
    | some r' =>
      rw [hi] at h
      have e : ps' = (false, M) :: r' := by simpa using h.symm
      subst e
      simp only [goodN, Bool.and_eq_true, decide_eq_true_eq] at hg ⊢
      exact ⟨goodAll_incN r r' hi hg.1, hg.2⟩

/-- The zone tape of a zone in N coordinates. -/
def zoneN (ps : List (Bool × Nat)) (top : Nat) (t : Tape) : Tape := zoneT (n0of ps) (physP ps top) t

/-- One visit, in N coordinates: 2 more in `N_0`, then the increment. -/
theorem visitN (ps ps' : List (Bool × Nat)) (top : Nat) (t : Tape) (hg : goodN ps top = true)
    (h : incN (bump 2 ps) = some ps') :
    Reach ⟨zoneN ps top t, blank, .A⟩ ⟨zoneN ps' top t, blank, .A⟩ := by
  cases ps with
  | nil => simp [bump, incN] at h
  | cons p r =>
    obtain ⟨b, M⟩ := p
    simp only [goodN, Bool.and_eq_true, decide_eq_true_eq] at hg
    have hi := inc_physP top hg.2 (bump 2 ((b, M) :: r)) ps' hg.1 h
    rw [physP_bump] at hi
    have hv := visit (n0of ((b, M) :: r)) _ _ t hi
    have e : n0of ((b, M) :: r) + (if hd (physP ((b, M) :: r) top) then 1 else 2) = n0of ps' := by
      rw [hd_physP]
      cases b with
      | false =>
        simp only [bump, incN] at h
        have e : ps' = (true, M + 2 - 1) :: r := by simpa using h.symm
        subst e; simp [n0of, hd] <;> omega
      | true =>
        simp only [bump, incN] at h
        cases hj : incN r with
        | none => rw [hj] at h; simp at h
        | some z =>
          rw [hj] at h
          have e : ps' = (false, M + 2) :: z := by simpa using h.symm
          subst e; simp [n0of, hd]
    rw [e] at hv
    exact hv

theorem ovf_bump (d V : Nat) : ∀ ps : List (Bool × Nat), ovf V (bump d ps) = ovf V ps
  | [] => rfl
  | (_, _) :: _ => rfl

theorem bump_addV (V d : Nat) : ∀ ps : List (Bool × Nat),
    bump 2 (addV V (bump (2 * V + d) ps)) = addV V (bump (2 * V + d + 2) ps)
  | [] => rfl
  | (b, M) :: r => by
    simp only [bump, addV]
    have : M + (2 * V + d) - (V + 1 - b.toNat) / 2 + 2 = M + (2 * V + d + 2) - (V + 1 - b.toNat) / 2 := by
      cases b <;> simp <;> omega
    rw [this]

theorem goodN_bump (d top : Nat) : ∀ ps : List (Bool × Nat), goodN (bump d ps) top = goodN ps top
  | [] => rfl
  | (_, _) :: _ => rfl

/-- The zone after `V` visits. -/
def after (V : Nat) (ps : List (Bool × Nat)) : List (Bool × Nat) := addV V (bump (2 * V) ps)

/-- **Many visits at once.**  If the bits do not overflow in `V` visits and every `N_j` (`j >= 1`) is at least 2
after them, the machine goes from the zone `ps` to the zone `after V ps`. -/
theorem jump (ps : List (Bool × Nat)) (top : Nat) (t : Tape) : ∀ V : Nat, ovf V ps = 0 →
    goodN (after V ps) top = true → Reach ⟨zoneN ps top t, blank, .A⟩ ⟨zoneN (after V ps) top t, blank, .A⟩
  | 0, _, _ => by
    have e : after 0 ps = ps := by
      unfold after
      rw [addV_zero]
      cases ps with
      | nil => rfl
      | cons p r => obtain ⟨b, M⟩ := p; rfl
    rw [e]; exact Reach.refl _
  | V + 1, ho, hg => by
    have ho' := ovf_succ ps V ho
    have hstep : incN (bump 2 (after V ps)) = some (after (V + 1) ps) := by
      unfold after
      have e := bump_addV V 0 ps
      rw [Nat.add_zero] at e
      rw [e, show 2 * (V + 1) = 2 * V + 2 by omega]
      exact addV_succ _ V (by rw [ovf_bump]; exact ho)
    have hg' : goodN (after V ps) top = true := by
      have := goodN_incN top _ _ hstep hg
      rwa [goodN_bump] at this
    exact (jump ps top t V ho' hg').seq (visitN _ _ top t hg' hstep)

end H172044
