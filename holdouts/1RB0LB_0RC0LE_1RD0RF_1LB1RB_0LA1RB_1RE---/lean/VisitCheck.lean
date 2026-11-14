import VisitLaw

/-!
# A checker for the visit law

Counts of visits are kept as a pair `e`, `c` that stands for `2^e - c` (`val`).  `scan` carries such a count through a
finite word, cell pattern by cell pattern, and returns the rewritten word; `hscan` decides (soundly, not completely)
that one of the visits halts.  `check k s0` runs `k` rounds from the word `s0` and then asks for a halting round.
Everything is proved against the abstract system of `VisitLaw`; the only thing left to a compiled run is the
evaluation of `check`.
-/

namespace VisitLaw

open TM

/-- The count `2^e - c`. -/
def val (e c : Nat) : Nat := 2 ^ e - c

/-- 0: the count is zero; 1: it is positive; 2: not decided (never happens in practice). -/
def sign (e c : Nat) : Nat :=
  if e < 30 then (if 2 ^ e ≤ c then 0 else 1) else if c < 2 ^ 30 then 1 else 2

theorem sign_zero {e c : Nat} (h : sign e c = 0) : val e c = 0 := by
  unfold sign at h; unfold val
  split at h
  · split at h
    · omega
    · cases h
  · split at h <;> cases h

theorem sign_pos {e c : Nat} (h : sign e c = 1) : 1 ≤ val e c := by
  unfold sign at h; unfold val
  split at h
  · split at h
    · cases h
    · omega
  · rename_i he
    split at h
    · have : 2 ^ 30 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · cases h

theorem val_double (e c : Nat) : val (e + 1) (2 * c) = 2 * val e c := by
  unfold val; rw [Nat.pow_succ]; omega

theorem val_hd (e c : Nat) : val (e - 1) (if e = 0 then 1 else (c + 1) / 2) = val e c / 2 := by
  unfold val
  cases e with
  | zero => simp; omega
  | succ k => simp [Nat.pow_succ]; omega

theorem val_hu (e c : Nat) : val (e - 1) (if e = 0 then c else c / 2) = (val e c + 1) / 2 := by
  unfold val
  cases e with
  | zero => simp; omega
  | succ k => simp [Nat.pow_succ]; omega

theorem val_pred (e c : Nat) : val e (c + 1) = val e c - 1 := by
  unfold val; omega

/-- The count is odd (for a positive count). -/
def oddc (e c : Nat) : Bool := if e = 0 then true else c % 2 == 1

theorem val_odd {e c : Nat} (h : 1 ≤ val e c) : (val e c % 2 == 1) = oddc e c := by
  unfold val at *; unfold oddc
  cases e with
  | zero =>
    have : 2 ^ 0 - c = 1 := by simp at h ⊢; omega
    rw [this]; rfl
  | succ k =>
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [hp] at h ⊢
    rcases Nat.mod_two_eq_zero_or_one c with e | e
    · have : (2 * 2 ^ k - c) % 2 = 0 := by omega
      simp [this, e]
    · have : (2 * 2 ^ k - c) % 2 = 1 := by omega
      simp [this, e]

theorem val_even {e c : Nat} (h : 1 ≤ val e c) : (val e c % 2 == 0) = !oddc e c := by
  rw [← val_odd h]
  rcases Nat.mod_two_eq_zero_or_one (val e c) with e | e <;> rw [e] <;> rfl

/-- The word does not start with `1 1`. -/
def guardB : List Bool → Bool
  | true :: true :: _ => false
  | _ => true

theorem guardB_sound {r : List Bool} (h : guardB r = true) : Guard (app r blank) := by
  intro ⟨h0, h1⟩
  match r, h, h0, h1 with
  | [], _, h0, _ => cases h0
  | [_], _, _, h1 => cases h1
  | true :: true :: _, h, _, _ => cases h
  | false :: _ :: _, _, h0, _ => cases h0
  | true :: false :: _, _, _, h1 => cases h1

def pad : List Bool := [false, false, false, false]

theorem app_pad (s : List Bool) : app (s ++ pad) blank = app s blank := by
  rw [← app_app]; simp [pad, cons_false_blank]

/-- Carry the count `2^e - c` through the word `s`; `acc` is the output so far, reversed.  The cells are taken off
one at a time so that the compiled code can reuse them. -/
def scan : Nat → Nat → Nat → List Bool → List Bool → Option (List Bool)
  | 0, _, _, _, _ => none
  | fuel + 1, e, c, s, acc =>
    match sign e c with
    | 0 => some (acc.reverseAux s)
    | 1 =>
      match s with
      | [] => scan fuel e c pad acc
      | a :: t =>
        match t with
        | [] => scan fuel e c (a :: pad) acc
        | b :: u =>
          match u with
          | [] => scan fuel e c (a :: b :: pad) acc
          | d :: r =>
            match a, b, d with
            | true, false, false =>
              scan fuel (e - 1) (if e = 0 then c else c / 2) r (false :: false :: (!oddc e c) :: acc)
            | true, true, false =>
              scan fuel (e - 1) (if e = 0 then c else c / 2) r (false :: false :: (!oddc e c) :: acc)
            | false, false, false =>
              scan fuel (e - 1) (if e = 0 then 1 else (c + 1) / 2) r (false :: false :: oddc e c :: acc)
            | true, false, true =>
              match r with
              | [] => scan fuel e c (true :: false :: true :: pad) acc
              | x :: r' =>
                if x then none
                else if guardB r' then scan fuel (e + 1) (2 * c) r' (false :: true :: false :: true :: acc)
                else none
            | true, true, true => none
            | false, b, d => scan fuel e (c + 1) (true :: b :: d :: r) acc
    | _ => none

theorem scan_sound : ∀ (fuel e c : Nat) (s acc out : List Bool), scan fuel e c s acc = some out →
    ∃ s', out = acc.reverseAux s' ∧ VS (val e c) (app s blank) (app s' blank) := by
  intro fuel
  induction fuel with
  | zero => intro e c s acc out h; simp [scan] at h
  | succ fuel ih =>
    intro e c s acc out h
    unfold scan at h
    split at h
    · rename_i hs
      rw [sign_zero hs]
      exact ⟨s, (Option.some.inj h).symm, .zero _⟩
    · rename_i hs
      have hp := sign_pos hs
      split at h
      · obtain ⟨s', rfl, hv⟩ := ih _ _ _ _ _ h
        exact ⟨s', rfl, (app_pad []) ▸ hv⟩
      · split at h
        · rename_i a t
          obtain ⟨s', rfl, hv⟩ := ih _ _ _ _ _ h
          exact ⟨s', rfl, (app_pad [a]) ▸ hv⟩
        · split at h
          · rename_i a t b u
            obtain ⟨s', rfl, hv⟩ := ih _ _ _ _ _ h
            exact ⟨s', rfl, (app_pad [a, b]) ▸ hv⟩
          · rename_i a t b u d r
            split at h
            · obtain ⟨s', rfl, hv⟩ := ih _ _ _ _ _ h
              rw [val_hu] at hv
              refine ⟨(!oddc e c) :: false :: false :: s', rfl, ?_⟩
              rw [← val_even hp]; exact law_H hv
            · obtain ⟨s', rfl, hv⟩ := ih _ _ _ _ _ h
              rw [val_hu] at hv
              refine ⟨(!oddc e c) :: false :: false :: s', rfl, ?_⟩
              rw [← val_even hp]; exact law_G hp hv
            · obtain ⟨s', rfl, hv⟩ := ih _ _ _ _ _ h
              rw [val_hd] at hv
              refine ⟨oddc e c :: false :: false :: s', rfl, ?_⟩
              rw [← val_odd hp]; exact law_Z hv
            · split at h
              · obtain ⟨s', rfl, hv⟩ := ih _ _ _ _ _ h
                exact ⟨s', rfl, (app_pad [true, false, true]) ▸ hv⟩
              · rename_i x r'
                split at h
                · cases h
                · rename_i hx
                  have hx' : x = false := by cases x <;> simp_all
                  subst hx'
                  split at h
                  · rename_i hg
                    obtain ⟨s', rfl, hv⟩ := ih _ _ _ _ _ h
                    rw [val_double] at hv
                    exact ⟨true :: false :: true :: false :: s', rfl, vs_L (guardB_sound hg) hv⟩
                  · cases h
            · cases h
            · obtain ⟨s', rfl, hv⟩ := ih _ _ _ _ _ h
              rw [val_pred] at hv
              exact ⟨s', rfl, law_0 hp hv⟩
    · cases h

/-- One of the `2^e - c` visits to the word `s` halts (sound, not complete). -/
def hscan : Nat → Nat → Nat → List Bool → Bool
  | 0, _, _, _ => false
  | fuel + 1, e, c, s =>
    match sign e c with
    | 1 =>
      match s with
      | true :: false :: true :: true :: _ => true
      | true :: false :: true :: false :: r => guardB r && hscan fuel (e + 1) (2 * c) r
      | true :: false :: false :: r => hscan fuel (e - 1) (if e = 0 then c else c / 2) r
      | true :: true :: false :: r => hscan fuel (e - 1) (if e = 0 then c else c / 2) r
      | false :: false :: false :: r => hscan fuel (e - 1) (if e = 0 then 1 else (c + 1) / 2) r
      | false :: a :: b :: d :: r => hscan fuel e (c + 1) (true :: a :: b :: d :: r)
      | _ => if s.length < 4 then hscan fuel e c (s ++ pad) else false
    | _ => false

theorem hscan_sound : ∀ (fuel e c : Nat) (s : List Bool), hscan fuel e c s = true →
    HVS (val e c) (app s blank) := by
  intro fuel
  induction fuel with
  | zero => intro e c s h; simp [hscan] at h
  | succ fuel ih =>
    intro e c s h
    unfold hscan at h
    split at h
    · rename_i hs
      have hp := sign_pos hs
      split at h
      · exact hvs_X hp _
      · rename_i r
        rw [Bool.and_eq_true] at h
        have hv := ih _ _ _ h.2
        rw [val_double] at hv
        exact hvs_L (guardB_sound h.1) hv
      · have hv := ih _ _ _ h
        rw [val_hu] at hv
        exact hvs_H hv
      · have hv := ih _ _ _ h
        rw [val_hu] at hv
        exact hvs_G hv
      · have hv := ih _ _ _ h
        rw [val_hd] at hv
        exact hvs_Z hv
      · have hv := ih _ _ _ h
        rw [val_pred] at hv
        exact hvs_0 hv
      · split at h
        · have hv := ih _ _ _ h
          rw [app_pad] at hv
          exact hv
        · cases h
    · cases h

/-! ## Rounds -/

def fuelR : Nat := 100000000

/-- One round on the word `s`: one visit to `1 0 s`. -/
def round (s : List Bool) : Option (List Bool) := scan fuelR 0 0 (true :: false :: s) []

/-- `k` rounds. -/
def iter : Nat → List Bool → Option (List Bool)
  | 0, s => some s
  | k + 1, s =>
    match round s with
    | some s' => iter k s'
    | none => none

/-- After `k` rounds from the word `s0`, the next round halts. -/
def check (k : Nat) (s0 : List Bool) : Bool :=
  match iter k s0 with
  | some s => hscan fuelR 0 0 (true :: false :: s)
  | none => false

theorem round_sound {s s' : List Bool} (h : round s = some s') :
    AV (cons true (cons false (app s blank))) (app s' blank) := by
  obtain ⟨t, rfl, hv⟩ := scan_sound _ _ _ _ _ _ h
  exact VS.one_inv hv

section Machine

variable {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q))
variable {V W : Tape → Tape → Prop} {VH WH : Tape → Prop}

theorem halts_of_reach {n : Nat} {c c' : Cfg Q} (h : steps δ n c = some c') (hh : Halts δ c') : Halts δ c := by
  obtain ⟨m, c'', e, hc⟩ := hh
  exact ⟨n + m, c'', steps_seq δ h e, hc⟩

/-- The machine halts if (1) its visits obey the law, (2) a round `LE s → LE s'` is one visit to `1 0 s`,
(3) it reaches `LE s0` and (4) the checker says that after `k` rounds the next round halts. -/
theorem halts_of_check (law : Law V W VH WH) (LE : Tape → Cfg Q) (c0 : Cfg Q)
    (hround : ∀ {s s' : Tape}, V (cons true (cons false s)) s' → ∃ n, steps δ n (LE s) = some (LE s'))
    (hhalt : ∀ {s : Tape}, VH (cons true (cons false s)) → Halts δ (LE s))
    (s0 : List Bool) (hstart : ∃ n, steps δ n c0 = some (LE (app s0 blank)))
    (k : Nat) (h : check k s0 = true) : Halts δ c0 := by
  have key : ∀ (k : Nat) (s s' : List Bool), iter k s = some s' →
      ∃ n, steps δ n (LE (app s blank)) = some (LE (app s' blank)) := by
    intro k
    induction k with
    | zero => intro s s' h; cases h; exact ⟨0, rfl⟩
    | succ k ih =>
      intro s s' h
      unfold iter at h
      split at h
      · rename_i t ht
        obtain ⟨n1, e1⟩ := hround (law.av (round_sound ht)).1
        obtain ⟨n2, e2⟩ := ih _ _ h
        exact ⟨n1 + n2, steps_seq δ e1 e2⟩
      · cases h
  unfold check at h
  split at h
  · rename_i s hs
    obtain ⟨n0, e0⟩ := hstart
    obtain ⟨n1, e1⟩ := key _ _ _ hs
    have ha : AH (cons true (cons false (app s blank))) := hvs_one (hscan_sound _ _ _ _ h)
    exact halts_of_reach δ (steps_seq δ e0 e1) (hhalt (law.ah ha).1)
  · cases h

end Machine

end VisitLaw
