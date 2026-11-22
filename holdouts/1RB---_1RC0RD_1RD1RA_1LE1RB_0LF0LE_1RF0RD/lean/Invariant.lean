import Orbit

/-!
# The junction machine does not get stuck where it is not supposed to

An invariant `Inv` of the junction machine `AS` (`Phase.lean`) that bounds the left string's value by what the
counts still to come will add.  Three forms:

* `JInv` (a J junction): the right side is one counter of value `Cv = c + 2^l val(H)` that runs on to `2^l tl H`,
  and the left string has room for twice the difference;
* `SInv` (plenty of room): room for `2^(l + |H| + 1)`, more than any run of the right side can use;
* `KInv` (a K junction before its first absorption): room for the counts up to the absorption, and the state right
  after the absorption satisfies `SInv`.

`step_inv`: from a state with `Inv`, `astep` never returns `stuck`; a `next` state has `Inv` again and a smaller
measure `mu`; a `done` result is a post-event configuration with `2 ≤ v < 2^(w+1)` and `d ≤ w`.  `arun_inv`: with
fuel above `mu`, `arun` returns such a `done`.
-/

namespace H140108

open TM

/-! ## Lists of bits as numbers -/

def valOf : List Bool → Nat
  | [] => 0
  | b :: H => (if b then 1 else 0) + 2 * valOf H

def lastT : List Bool → Bool
  | [] => false
  | [b] => b
  | _ :: b :: H => lastT (b :: H)

/-- `2^|H|` if the last digit is 1, `2^(|H|-1)` if it is 0: where a counter with these high digits stops. -/
def tl : List Bool → Nat
  | [] => 1
  | [b] => if b then 2 else 1
  | _ :: b :: H => 2 * tl (b :: H)

/-- The number of leading 0 digits. -/
def lz : List Bool → Nat
  | false :: H => lz H + 1
  | _ => 0

theorem tl_cons (b : Bool) {H : List Bool} (h : H ≠ []) : tl (b :: H) = 2 * tl H := by
  cases H with
  | nil => exact absurd rfl h
  | cons c T => rfl

theorem lastT_cons (b : Bool) {H : List Bool} (h : H ≠ []) : lastT (b :: H) = lastT H := by
  cases H with
  | nil => exact absurd rfl h
  | cons c T => rfl

theorem tl_pos : ∀ H : List Bool, 1 ≤ tl H
  | [] => Nat.le_refl _
  | [b] => by cases b <;> decide
  | _ :: b :: H => by have := tl_pos (b :: H); show 1 ≤ 2 * tl (b :: H); omega

theorem valOf_tl : ∀ (H : List Bool), H ≠ [] → valOf H + 1 ≤ tl H
  | [], h => absurd rfl h
  | [b], _ => by cases b <;> decide
  | a :: b :: H, _ => by
    have := valOf_tl (b :: H) (by simp)
    show (if a then 1 else 0) + 2 * valOf (b :: H) + 1 ≤ 2 * tl (b :: H)
    cases a <;> simp <;> omega

theorem valOf_le : ∀ (H : List Bool), valOf H + 1 ≤ 2 ^ H.length
  | [] => by decide
  | b :: H => by
    have := valOf_le H
    show (if b then 1 else 0) + 2 * valOf H + 1 ≤ 2 ^ (H.length + 1)
    rw [pow_succ']; cases b <;> simp <;> omega

theorem tl_le : ∀ (H : List Bool), tl H ≤ 2 ^ H.length
  | [] => by decide
  | [b] => by cases b <;> decide
  | a :: b :: H => by
    have := tl_le (b :: H)
    show 2 * tl (b :: H) ≤ 2 ^ ((b :: H).length + 1)
    rw [pow_succ']; omega

theorem valOf_ones_append (R : List Bool) : ∀ s : Nat,
    valOf (List.replicate s true ++ R) + 1 = 2 ^ s * (valOf R + 1)
  | 0 => by simp
  | s + 1 => by
    have := valOf_ones_append R s
    show (if true then 1 else 0) + 2 * valOf (List.replicate s true ++ R) + 1 = _
    rw [pow_succ', Nat.mul_assoc, ← this]; simp; omega

theorem tl_append (R : List Bool) (hR : R ≠ []) : ∀ B : List Bool, tl (B ++ R) = 2 ^ B.length * tl R
  | [] => by simp
  | b :: B => by
    show tl (b :: (B ++ R)) = _
    rw [tl_cons b (by simp [hR]), tl_append R hR B, List.length_cons, pow_succ']; rw [Nat.mul_assoc]

theorem lastT_append (R : List Bool) (hR : R ≠ []) : ∀ B : List Bool, lastT (B ++ R) = lastT R
  | [] => rfl
  | b :: B => by
    show lastT (b :: (B ++ R)) = _
    rw [lastT_cons b (by simp [hR]), lastT_append R hR B]

theorem lastT_ones : ∀ s : Nat, lastT (true :: List.replicate s true) = true
  | 0 => rfl
  | s + 1 => by
    show lastT (true :: true :: List.replicate s true) = true
    exact lastT_ones s

theorem tl_ones : ∀ s : Nat, tl (true :: List.replicate s true) = 2 ^ (s + 1)
  | 0 => rfl
  | s + 1 => by
    show 2 * tl (true :: List.replicate s true) = _
    rw [tl_ones s, pow_succ' (s + 1)]

/-! ## The invariant -/

def mu (s : AS) : Nat := 2 * s.H.length + (if s.c + 1 < 2 ^ s.l then 1 else 0)

/-- The counter is used up: a post-event configuration is next (`astep`'s `[]` cases succeed). -/
def EmptyOk (s : AS) : Prop :=
  (s.l = 0 ∧ s.v + 3 ≤ 2 ^ (s.w + 1)) ∨
  (0 < s.l ∧ s.c = 2 ^ (s.l - 1) ∧ s.v + 1 ≤ 2 ^ (s.w + 1) ∧ s.l ≤ s.w + 1 ∧ 2 ≤ s.v)

/-- The counter, when it stops, has at most `w + 1` digits. -/
def Bnd (s : AS) : Prop := s.l + s.H.length + (if lastT s.H then 1 else 0) ≤ s.w + 1

def JInv (s : AS) : Prop :=
  s.k = false ∧ s.c < 2 ^ s.l ∧ (s.H = [] → EmptyOk s) ∧
  (s.H ≠ [] → s.v + 2 * (2 ^ s.l * tl s.H) + 1 ≤ 2 ^ (s.w + 1) + 2 * (s.c + 2 ^ s.l * valOf s.H) ∧ Bnd s)

def SInv (s : AS) : Prop :=
  s.c < 2 ^ s.l ∧ (s.H = [] → EmptyOk s) ∧
  (s.H ≠ [] → s.v + 2 ^ (s.l + s.H.length + 1) + 1 ≤ 2 ^ (s.w + 1) + 2 * s.c ∧ Bnd s)

/-- The state right after an absorption of a counter with `l` digits (`astep`). -/
def absorbState (w v l : Nat) (H : List Bool) : AS :=
  if l % 2 = 0 then ⟨w + 3 * (l / 2) + 1, 2 ^ (3 * (l / 2)) * (1 + 2 * v), 0, 0, false, H⟩
  else ⟨w + 3 * (l / 2) + 3, 1 + 2 ^ (3 * (l / 2) + 2) * (1 + 2 * v), 0, 0, true, H⟩

/-- The counts before the absorption of a K state. -/
def kn (s : AS) : Nat := 2 ^ (s.l + lz s.H) - 1 - s.c

def KInv (s : AS) : Prop :=
  s.k = true ∧ s.c < 2 ^ s.l ∧ lz s.H < s.H.length ∧ s.v + 2 * kn s + 1 ≤ 2 ^ (s.w + 1) ∧
  SInv (absorbState s.w (s.v + 2 * kn s) (s.l + lz s.H) (s.H.drop (lz s.H + 1)))

def Inv (s : AS) : Prop := JInv s ∨ SInv s ∨ KInv s

theorem Inv.c_lt {s : AS} (h : Inv s) : s.c < 2 ^ s.l := by
  rcases h with h | h | h
  · exact h.2.1
  · exact h.1
  · exact h.2.1

theorem Inv.empty {w v l c : Nat} {k : Bool} (h : Inv ⟨w, v, l, c, k, []⟩) : EmptyOk ⟨w, v, l, c, k, []⟩ := by
  rcases h with h | h | h
  · exact h.2.2.1 rfl
  · exact h.2.1 rfl
  · exact absurd h.2.2.1 (by simp [lz])

/-! ## Absorption gives plenty of room -/

def fac (l : Nat) : Nat := if l % 2 = 0 then 2 ^ (3 * (l / 2)) else 2 ^ (3 * (l / 2) + 2)

theorem fac_pos (l : Nat) : 1 ≤ fac l := by
  unfold fac; split <;> exact pow_pos' _

theorem absorbS_fac (w v l : Nat) (H1 : List Bool)
    (hr : fac l * (2 * v + 1) + 2 ^ (H1.length + 1) + 2 ≤ fac l * 2 ^ (w + 2))
    (hb : H1.length + (if lastT H1 then 1 else 0) ≤ w + 2) : SInv (absorbState w v l H1) := by
  unfold absorbState
  unfold fac at hr
  split
  · rename_i he
    rw [if_pos he] at hr
    have e : 2 ^ (w + 3 * (l / 2) + 1 + 1) = 2 ^ (3 * (l / 2)) * 2 ^ (w + 2) := by
      rw [← Nat.pow_add]; congr 1; omega
    refine ⟨by simp, fun hH => Or.inl ⟨rfl, ?_⟩, fun _ => ⟨?_, ?_⟩⟩
    · subst hH; simp only [List.length_nil] at hr ⊢; rw [e]
      have : 2 ^ (3 * (l / 2)) * (1 + 2 * v) = 2 ^ (3 * (l / 2)) * (2 * v + 1) := by rw [Nat.add_comm 1]
      omega
    · show 2 ^ (3 * (l / 2)) * (1 + 2 * v) + 2 ^ (0 + H1.length + 1) + 1 ≤ 2 ^ (w + 3 * (l / 2) + 1 + 1) + 2 * 0
      rw [e, Nat.zero_add, Nat.add_comm 1 (2 * v)]; omega
    · show 0 + H1.length + (if lastT H1 then 1 else 0) ≤ w + 3 * (l / 2) + 1 + 1; omega
  · rename_i he
    rw [if_neg he] at hr
    have e : 2 ^ (w + 3 * (l / 2) + 3 + 1) = 2 ^ (3 * (l / 2) + 2) * 2 ^ (w + 2) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h4 : 2 ^ (3 * (l / 2) + 2) = 4 * 2 ^ (3 * (l / 2)) := by rw [Nat.pow_add]; omega
    refine ⟨by simp, fun hH => Or.inl ⟨rfl, ?_⟩, fun _ => ⟨?_, ?_⟩⟩
    · subst hH; simp only [List.length_nil] at hr ⊢; rw [e, Nat.add_comm 1 (2 * v)]; omega
    · show 1 + 2 ^ (3 * (l / 2) + 2) * (1 + 2 * v) + 2 ^ (0 + H1.length + 1) + 1 ≤ 2 ^ (w + 3 * (l / 2) + 3 + 1) + 2 * 0
      rw [e, Nat.zero_add, Nat.add_comm 1 (2 * v)]; omega
    · show 0 + H1.length + (if lastT H1 then 1 else 0) ≤ w + 3 * (l / 2) + 3 + 1; omega

theorem absorbS (w v l : Nat) (H1 : List Bool) (hr : 2 * v + 2 ^ (H1.length + 1) + 3 ≤ 2 ^ (w + 2))
    (hb : H1.length + (if lastT H1 then 1 else 0) ≤ w + 2) : SInv (absorbState w v l H1) := by
  refine absorbS_fac w v l H1 ?_ hb
  have := pow_pos' (H1.length + 1)
  obtain ⟨D, hD⟩ : ∃ D, 2 ^ (w + 2) = 2 * v + 1 + D := ⟨2 ^ (w + 2) - (2 * v + 1), by omega⟩
  rw [hD, show fac l * (2 * v + 1 + D) = fac l * (2 * v + 1) + fac l * D from Nat.mul_add _ _ _]
  have := Nat.le_mul_of_pos_left D (fac_pos l)
  omega

/-! ## The steps of the junction machine keep the invariant -/

theorem inv_count {w v l c : Nat} {k h : Bool} {H1 : List Bool} (hs : Inv ⟨w, v, l, c, k, h :: H1⟩)
    (hcl : c + 1 < 2 ^ l) :
    v + 2 * (2 ^ l - 1 - c) < 2 ^ (w + 1) ∧ Inv ⟨w, v + 2 * (2 ^ l - 1 - c), l, 2 ^ l - 1, k, h :: H1⟩ := by
  have hp := pow_pos' l
  rcases hs with ⟨hk, hc, -, hne⟩ | ⟨hc, -, hne⟩ | ⟨hk, hc, hlz, hroom, hpost⟩
  · obtain ⟨hm, hb⟩ := hne (by simp)
    simp only at hm hb hk hc
    have ht := Nat.mul_le_mul_left (2 ^ l) (valOf_tl (h :: H1) (by simp))
    rw [Nat.mul_add, Nat.mul_one] at ht
    refine ⟨by omega, Or.inl ⟨hk, by simp; omega, fun e => by simp at e, fun _ => ⟨?_, hb⟩⟩⟩
    show v + 2 * (2 ^ l - 1 - c) + 2 * (2 ^ l * tl (h :: H1)) + 1 ≤ 2 ^ (w + 1) + 2 * (2 ^ l - 1 + 2 ^ l * valOf (h :: H1))
    omega
  · obtain ⟨hm, hb⟩ := hne (by simp)
    simp only [List.length_cons] at hm hb hc
    have : 2 ^ (l + 1) ≤ 2 ^ (l + (H1.length + 1) + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_succ'] at this
    refine ⟨by omega, Or.inr (Or.inl ⟨by simp; omega, fun e => by simp at e, fun _ => ⟨?_, hb⟩⟩)⟩
    show v + 2 * (2 ^ l - 1 - c) + 2 ^ (l + (H1.length + 1) + 1) + 1 ≤ 2 ^ (w + 1) + 2 * (2 ^ l - 1)
    omega
  · simp only [kn] at hroom hpost
    simp only at hk hc hlz
    have : 2 ^ l ≤ 2 ^ (l + lz (h :: H1)) := Nat.pow_le_pow_right (by omega) (by omega)
    have e : v + 2 * (2 ^ l - 1 - c) + 2 * (2 ^ (l + lz (h :: H1)) - 1 - (2 ^ l - 1))
        = v + 2 * (2 ^ (l + lz (h :: H1)) - 1 - c) := by omega
    refine ⟨by omega, Or.inr (Or.inr ⟨hk, by simp; omega, hlz, ?_, ?_⟩)⟩
    · show v + 2 * (2 ^ l - 1 - c) + 2 * (2 ^ (l + lz (h :: H1)) - 1 - (2 ^ l - 1)) + 1 ≤ 2 ^ (w + 1)
      omega
    · show SInv (absorbState w (v + 2 * (2 ^ l - 1 - c) + 2 * (2 ^ (l + lz (h :: H1)) - 1 - (2 ^ l - 1)))
        (l + lz (h :: H1)) ((h :: H1).drop (lz (h :: H1) + 1)))
      rw [e]; exact hpost

theorem inv_carry0 {w v l c : Nat} {k : Bool} {H1 : List Bool} (hs : Inv ⟨w, v, l, c, k, false :: H1⟩)
    (hcf : c = 2 ^ l - 1) : v + 2 < 2 ^ (w + 1) ∧ Inv ⟨w, v + 2, l + 1, 2 ^ l, k, H1⟩ := by
  have hp := pow_pos' l
  have hpl : 2 ^ (l + 1) = 2 * 2 ^ l := pow_succ' l
  have hv0 : valOf (false :: H1) = 2 * valOf H1 := by simp [valOf]
  rcases hs with ⟨hk, hc, -, hne⟩ | ⟨hc, -, hne⟩ | ⟨hk, hc, hlz, hroom, hpost⟩
  · obtain ⟨hm, hb⟩ := hne (by simp)
    simp only [Bnd, List.length_cons] at hm hb hk
    rw [hv0] at hm
    by_cases hH : H1 = []
    · subst hH
      simp only [tl, Bool.false_eq_true, ↓reduceIte, valOf, lastT, List.length_nil] at hm hb
      refine ⟨by omega, Or.inl ⟨hk, by simp; omega, fun _ => Or.inr ⟨by simp, ?_, ?_, ?_, ?_⟩, fun e => absurd rfl e⟩⟩
      · show 2 ^ l = 2 ^ (l + 1 - 1); simp
      · show v + 2 + 1 ≤ 2 ^ (w + 1); omega
      · show l + 1 ≤ w + 1; omega
      · show 2 ≤ v + 2; omega
    · rw [tl_cons false hH, lastT_cons false hH] at *
      have ht := Nat.mul_le_mul_left (2 ^ l) (valOf_tl H1 hH)
      rw [Nat.mul_add, Nat.mul_one] at ht
      have e1 : 2 ^ l * (2 * tl H1) = 2 * (2 ^ l * tl H1) := Nat.mul_left_comm _ _ _
      have e2 : 2 ^ l * (2 * valOf H1) = 2 * (2 ^ l * valOf H1) := Nat.mul_left_comm _ _ _
      have e3 : 2 ^ (l + 1) * tl H1 = 2 * (2 ^ l * tl H1) := by rw [hpl, Nat.mul_assoc]
      have e4 : 2 ^ (l + 1) * valOf H1 = 2 * (2 ^ l * valOf H1) := by rw [hpl, Nat.mul_assoc]
      rw [e1, e2] at hm
      refine ⟨by omega, Or.inl ⟨hk, by simp; omega, fun e => absurd e hH, fun _ => ⟨?_, ?_⟩⟩⟩
      · show v + 2 + 2 * (2 ^ (l + 1) * tl H1) + 1 ≤ 2 ^ (w + 1) + 2 * (2 ^ l + 2 ^ (l + 1) * valOf H1)
        rw [e3, e4]; omega
      · show l + 1 + H1.length + (if lastT H1 then 1 else 0) ≤ w + 1; omega
  · obtain ⟨hm, hb⟩ := hne (by simp)
    simp only [Bnd, List.length_cons] at hm hb hc
    have h4 : 2 ^ (l + 2) ≤ 2 ^ (l + (H1.length + 1) + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h4' : 2 ^ (l + 2) = 4 * 2 ^ l := by rw [Nat.pow_add]; omega
    by_cases hH : H1 = []
    · subst hH
      simp only [lastT, Bool.false_eq_true, ↓reduceIte, List.length_nil] at hb
      refine ⟨by omega, Or.inr (Or.inl ⟨by simp; omega, fun _ => Or.inr ⟨by simp, ?_, ?_, ?_, ?_⟩, fun e => absurd rfl e⟩)⟩
      · show 2 ^ l = 2 ^ (l + 1 - 1); simp
      · show v + 2 + 1 ≤ 2 ^ (w + 1); omega
      · show l + 1 ≤ w + 1; omega
      · show 2 ≤ v + 2; omega
    · rw [lastT_cons false hH] at hb
      refine ⟨by omega, Or.inr (Or.inl ⟨by simp; omega, fun e => absurd e hH, fun _ => ⟨?_, ?_⟩⟩)⟩
      · show v + 2 + 2 ^ (l + 1 + H1.length + 1) + 1 ≤ 2 ^ (w + 1) + 2 * 2 ^ l
        rw [show l + 1 + H1.length + 1 = l + (H1.length + 1) + 1 by omega]; omega
      · show l + 1 + H1.length + (if lastT H1 then 1 else 0) ≤ w + 1; omega
  · simp only [kn, lz, List.length_cons] at hroom hpost hlz hk hc
    have h2 : 2 ^ (l + 1) ≤ 2 ^ (l + (lz H1 + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    have e : v + 2 + 2 * (2 ^ (l + 1 + lz H1) - 1 - 2 ^ l) = v + 2 * (2 ^ (l + (lz H1 + 1)) - 1 - c) := by
      rw [show l + 1 + lz H1 = l + (lz H1 + 1) by omega]; omega
    refine ⟨by omega, Or.inr (Or.inr ⟨hk, by simp; omega, by simp; omega, ?_, ?_⟩)⟩
    · show v + 2 + 2 * (2 ^ (l + 1 + lz H1) - 1 - 2 ^ l) + 1 ≤ 2 ^ (w + 1)
      omega
    · show SInv (absorbState w (v + 2 + 2 * (2 ^ (l + 1 + lz H1) - 1 - 2 ^ l)) (l + 1 + lz H1) (H1.drop (lz H1 + 1)))
      rw [e, show l + 1 + lz H1 = l + (lz H1 + 1) by omega]; exact hpost

theorem inv_absorb {w v l c : Nat} {H1 : List Bool} (hs : Inv ⟨w, v, l, c, true, true :: H1⟩)
    (hcf : c = 2 ^ l - 1) : SInv (absorbState w v l H1) := by
  have hp := pow_pos' l
  rcases hs with ⟨hk, -⟩ | ⟨hc, -, hne⟩ | ⟨hk, hc, hlz, hroom, hpost⟩
  · cases hk
  · obtain ⟨hm, hb⟩ := hne (by simp)
    simp only [Bnd, List.length_cons] at hm hb hc
    have hl1 : H1.length + (if lastT H1 then 1 else 0) ≤ w := by
      by_cases hH : H1 = []
      · subst hH; simp [lastT]
      · rw [lastT_cons true hH] at hb; omega
    refine absorbS w v l H1 ?_ (by omega)
    have hq := pow_pos' (H1.length + 1)
    have e1 : 2 ^ (l + (H1.length + 1) + 1) = 2 * (2 ^ l * 2 ^ (H1.length + 1)) := by
      rw [pow_succ', Nat.pow_add]
    have e2 : 2 ^ (w + 2) = 2 * 2 ^ (w + 1) := pow_succ' (w + 1)
    have m1 : 2 ^ (H1.length + 1) ≤ 2 ^ l * 2 ^ (H1.length + 1) := Nat.le_mul_of_pos_left _ hp
    have m2 : 2 * 2 ^ l ≤ 2 ^ l * 2 ^ (H1.length + 1) := by
      rw [Nat.mul_comm 2]; exact Nat.mul_le_mul_left _ (by rw [pow_succ']; have := pow_pos' H1.length; omega)
    omega
  · simp only [kn, lz, Nat.add_zero, List.drop_succ_cons, List.drop_zero] at hpost
    rw [show v + 2 * (2 ^ l - 1 - c) = v by omega] at hpost
    exact hpost

theorem inv_carryJ1 {w v l c : Nat} {H1 : List Bool} (hs : Inv ⟨w, v, l, c, false, true :: H1⟩)
    (hcf : c = 2 ^ l - 1) :
    v + 2 < 2 ^ (w + 1) ∧ Inv ⟨w, v + 2, l + leadOnes H1 + 2, 2 ^ (l + leadOnes H1 + 1), false,
      H1.drop (leadOnes H1 + 1)⟩ := by
  have hp := pow_pos' l
  obtain ⟨e1, e2⟩ := leadOnes_spec H1
  generalize hs' : leadOnes H1 = s at e1 e2
  have hps := pow_pos' s
  have hlt : 2 ^ (l + s + 1) < 2 ^ (l + s + 2) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpow : 2 ^ (l + s + 1) = 2 ^ l * 2 ^ (s + 1) := by rw [← Nat.pow_add, Nat.add_assoc]
  have hpow2 : 2 ^ (l + s + 2) = 2 * (2 ^ l * 2 ^ (s + 1)) := by rw [← hpow, ← pow_succ']
  have hle : 2 ^ l ≤ 2 ^ l * 2 ^ (s + 1) := Nat.le_mul_of_pos_right _ (pow_pos' _)
  rcases hs with ⟨hk, hc, -, hne⟩ | ⟨hc, -, hne⟩ | ⟨hk, -⟩
  · obtain ⟨hm, hb⟩ := hne (by simp)
    simp only [Bnd, List.length_cons] at hm hb hc
    rcases e2 with e2 | e2
    · -- the ones run to the end: the counter gains a digit
      rw [e2, List.append_nil] at e1
      have hd : H1.drop (s + 1) = [] := by rw [e1]; simp
      rw [e1] at hm hb
      have ev := valOf_ones_append [] (s + 1)
      simp only [List.append_nil, valOf, Nat.zero_add, Nat.mul_one] at ev
      rw [tl_ones] at hm
      rw [lastT_ones] at hb
      simp only [List.length_cons, List.length_replicate, ↓reduceIte] at hb
      have hm' : 2 ^ l * (valOf (true :: List.replicate s true) + 1) = 2 ^ l * 2 ^ (s + 1) := by
        rw [show true :: List.replicate s true = List.replicate (s + 1) true from rfl, ev]
      rw [Nat.mul_add, Nat.mul_one] at hm'
      rw [hd]
      refine ⟨by omega, Or.inl ⟨rfl, by simp; omega, fun _ => Or.inr ⟨by simp, ?_, ?_, ?_, ?_⟩, fun e => absurd rfl e⟩⟩
      · show 2 ^ (l + s + 1) = 2 ^ (l + s + 2 - 1); rfl
      · show v + 2 + 1 ≤ 2 ^ (w + 1); omega
      · show l + s + 2 ≤ w + 1; omega
      · show 2 ≤ v + 2; omega
    · -- the ones end at a 0
      generalize hR : H1.drop (s + 1) = R at e2
      rw [e2] at e1
      rw [e1] at hm hb
      have ev := valOf_ones_append (false :: R) (s + 1)
      have hHe : true :: (List.replicate s true ++ false :: R) = List.replicate (s + 1) true ++ false :: R := rfl
      rw [hHe] at hm hb
      have hv : valOf (List.replicate (s + 1) true ++ false :: R) + 1 = 2 ^ (s + 1) * (2 * valOf R + 1) := by
        rw [ev]; simp [valOf]
      have hm' : 2 ^ l * valOf (List.replicate (s + 1) true ++ false :: R) + 2 ^ l
          = 2 * (2 ^ l * 2 ^ (s + 1) * valOf R) + 2 ^ l * 2 ^ (s + 1) := by
        calc _ = 2 ^ l * (valOf (List.replicate (s + 1) true ++ false :: R) + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ = 2 ^ l * (2 ^ (s + 1) * (2 * valOf R + 1)) := by rw [hv]
          _ = _ := by grind
      by_cases hRn : R = []
      · subst hRn
        rw [show List.replicate (s + 1) true ++ [false] = List.replicate (s + 1) true ++ [false] from rfl,
          tl_append [false] (by simp), lastT_append [false] (by simp)] at *
        simp only [tl, Bool.false_eq_true, ↓reduceIte, Nat.mul_one, lastT, List.length_append,
          List.length_replicate, List.length_cons, List.length_nil, valOf, Nat.mul_zero, Nat.zero_add] at hm hb hm'
        have h3 : 2 ^ l * 2 ^ (s + 1) = 2 ^ (l + s + 1) := hpow.symm
        refine ⟨by omega, Or.inl ⟨rfl, by simp; omega, fun _ => Or.inr ⟨by simp, ?_, ?_, ?_, ?_⟩, fun e => absurd rfl e⟩⟩
        · show 2 ^ (l + s + 1) = 2 ^ (l + s + 2 - 1); rfl
        · show v + 2 + 1 ≤ 2 ^ (w + 1); omega
        · show l + s + 2 ≤ w + 1; omega
        · show 2 ≤ v + 2; omega
      · have hA : List.replicate (s + 1) true ++ false :: R = (List.replicate (s + 1) true ++ [false]) ++ R := by simp
        have htl : tl (List.replicate (s + 1) true ++ false :: R) = 2 * 2 ^ (s + 1) * tl R := by
          rw [hA, tl_append R hRn]; simp [pow_succ']
        rw [htl] at hm
        rw [hA, lastT_append R hRn] at hb
        simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at hm hb
        have f1 : 2 ^ l * (2 * 2 ^ (s + 1) * tl R) = 2 * (2 ^ l * 2 ^ (s + 1) * tl R) := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm]
        rw [f1] at hm
        have ht := Nat.mul_le_mul_left (2 ^ l * 2 ^ (s + 1)) (valOf_tl R hRn)
        rw [Nat.mul_add, Nat.mul_one] at ht
        refine ⟨by omega, Or.inl ⟨rfl, by simp; omega, fun e => absurd e hRn, fun _ => ⟨?_, ?_⟩⟩⟩
        · show v + 2 + 2 * (2 ^ (l + s + 2) * tl R) + 1 ≤ 2 ^ (w + 1) + 2 * (2 ^ (l + s + 1) + 2 ^ (l + s + 2) * valOf R)
          rw [hpow2, hpow]
          have g1 : 2 * (2 ^ l * 2 ^ (s + 1)) * tl R = 2 * (2 ^ l * 2 ^ (s + 1) * tl R) := Nat.mul_assoc _ _ _
          have g2 : 2 * (2 ^ l * 2 ^ (s + 1)) * valOf R = 2 * (2 ^ l * 2 ^ (s + 1) * valOf R) := Nat.mul_assoc _ _ _
          rw [g1, g2]; omega
        · show l + s + 2 + R.length + (if lastT R then 1 else 0) ≤ w + 1; omega
  · obtain ⟨hm, hb⟩ := hne (by simp)
    simp only [Bnd, List.length_cons] at hm hb hc
    have h4 : 2 ^ (l + 1) ≤ 2 ^ (l + (H1.length + 1) + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_succ'] at h4
    rcases e2 with e2 | e2
    · rw [e2, List.append_nil] at e1
      have hd : H1.drop (s + 1) = [] := by rw [e1]; simp
      have hlen : H1.length = s := by rw [e1]; simp
      rw [e1, show true :: List.replicate s true = true :: List.replicate s true from rfl, lastT_ones] at hb
      simp only [List.length_replicate, ↓reduceIte] at hb
      rw [hd]
      refine ⟨by omega, Or.inr (Or.inl ⟨by simp; omega, fun _ => Or.inr ⟨by simp, ?_, ?_, ?_, ?_⟩, fun e => absurd rfl e⟩)⟩
      · show 2 ^ (l + s + 1) = 2 ^ (l + s + 2 - 1); rfl
      · show v + 2 + 1 ≤ 2 ^ (w + 1); omega
      · show l + s + 2 ≤ w + 1; omega
      · show 2 ≤ v + 2; omega
    · generalize hR : H1.drop (s + 1) = R at e2
      rw [e2] at e1
      have hlen : H1.length = s + 1 + R.length := by rw [e1]; simp; omega
      by_cases hRn : R = []
      · subst hRn
        have hlast : lastT (true :: H1) = false := by
          rw [e1, show true :: (List.replicate s true ++ [false]) = List.replicate (s + 1) true ++ [false] from rfl,
            lastT_append [false] (by simp)]; rfl
        rw [hlast] at hb
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil] at hb hlen
        refine ⟨by omega, Or.inr (Or.inl ⟨by simp; omega, fun _ => Or.inr ⟨by simp, ?_, ?_, ?_, ?_⟩, fun e => absurd rfl e⟩)⟩
        · show 2 ^ (l + s + 1) = 2 ^ (l + s + 2 - 1); rfl
        · show v + 2 + 1 ≤ 2 ^ (w + 1); omega
        · show l + s + 2 ≤ w + 1; omega
        · show 2 ≤ v + 2; omega
      · have hlast : lastT (true :: H1) = lastT R := by
          rw [e1, show true :: (List.replicate s true ++ false :: R)
            = (List.replicate (s + 1) true ++ [false]) ++ R by simp [List.replicate_succ], lastT_append R hRn]
        rw [hlast] at hb
        refine ⟨by omega, Or.inr (Or.inl ⟨by simp; omega, fun e => absurd e hRn, fun _ => ⟨?_, ?_⟩⟩)⟩
        · show v + 2 + 2 ^ (l + s + 2 + R.length + 1) + 1 ≤ 2 ^ (w + 1) + 2 * 2 ^ (l + s + 1)
          rw [show l + s + 2 + R.length + 1 = l + (H1.length + 1) + 1 by omega]; omega
        · show l + s + 2 + R.length + (if lastT R then 1 else 0) ≤ w + 1; omega
  · cases hk

/-! ## The run -/

theorem mu_absorb (w v l : Nat) (H1 : List Bool) : mu (absorbState w v l H1) = 2 * H1.length := by
  unfold absorbState; split <;> simp [mu]

theorem step_inv (s : AS) (hs : Inv s) :
    (∃ s', astep s = .next s' ∧ Inv s' ∧ mu s' < mu s) ∨
    (∃ d w v, astep s = .done d w v ∧ 2 ≤ v ∧ v < 2 ^ (w + 1) ∧ d ≤ w) := by
  obtain ⟨w, v, l, c, k, H⟩ := s
  have hc := hs.c_lt
  simp only at hc
  cases H with
  | nil =>
    right
    rcases hs.empty with ⟨hl, hr⟩ | ⟨hl, hcc, hr, hlw, hv2⟩
    · simp only at hl hr
      refine ⟨0, w, v + 2, ?_, by omega, by omega, by omega⟩
      simp only [astep, hl, ↓reduceIte, show v + 2 < 2 ^ (w + 1) by omega]
    · simp only at hl hcc hr hlw hv2
      refine ⟨l - 1, w, v, ?_, hv2, by omega, by omega⟩
      simp only [astep, show l ≠ 0 by omega, ↓reduceIte, hcc]
  | cons h H1 =>
    left
    by_cases hcl : c + 1 < 2 ^ l
    · obtain ⟨hg, hi⟩ := inv_count hs hcl
      refine ⟨_, ?_, hi, ?_⟩
      · simp only [astep, hcl, ↓reduceIte, hg]
      · simp only [mu, List.length_cons, hcl, ↓reduceIte]
        rw [if_neg (by omega)]; omega
    · have hcf : c = 2 ^ l - 1 := by omega
      subst hcf
      have hn : ¬ (2 ^ l - 1 + 1 < 2 ^ l) := by omega
      cases h with
      | false =>
        obtain ⟨hg, hi⟩ := inv_carry0 hs rfl
        refine ⟨_, ?_, hi, ?_⟩
        · simp only [astep, hn, ↓reduceIte, hg]
        · simp only [mu, List.length_cons, hn, ↓reduceIte]; split <;> omega
      | true =>
        cases k with
        | true =>
          refine ⟨absorbState w v l H1, ?_, Or.inr (Or.inl (inv_absorb hs rfl)), ?_⟩
          · simp only [astep, hn, ↓reduceIte, Bool.true_eq_false]
            unfold absorbState
            split <;> rfl
          · rw [mu_absorb]; simp only [mu, List.length_cons, hn, ↓reduceIte]; omega
        | false =>
          obtain ⟨hg, hi⟩ := inv_carryJ1 hs rfl
          refine ⟨_, ?_, hi, ?_⟩
          · simp only [astep, hn, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, hg]
          · simp only [mu, List.length_cons, hn, ↓reduceIte, List.length_drop]; split <;> omega

theorem arun_inv : ∀ (n : Nat) (s : AS), Inv s → mu s < n →
    ∃ d w v, arun n s = .done d w v ∧ 2 ≤ v ∧ v < 2 ^ (w + 1) ∧ d ≤ w
  | 0, _, _, h => absurd h (by omega)
  | n + 1, s, hs, hm => by
    rcases step_inv s hs with ⟨s', he, hs', hm'⟩ | ⟨d, w, v, he, hb⟩
    · obtain ⟨d, w, v, hr, hb⟩ := arun_inv n s' hs' (by omega)
      exact ⟨d, w, v, by simp only [arun, he]; exact hr, hb⟩
    · exact ⟨d, w, v, by simp only [arun, he], hb⟩

/-! ## The counter never shrinks -/

theorem leadOnes_le : ∀ H : List Bool, leadOnes H ≤ H.length
  | [] => Nat.le_refl _
  | false :: _ => Nat.zero_le _
  | true :: H => by have := leadOnes_le H; simp [leadOnes]; omega

theorem astep_mono {s s' : AS} (h : astep s = .next s') :
    s.w < s'.w ∨ (s.w = s'.w ∧ s.l + s.H.length ≤ s'.l + s'.H.length) := by
  obtain ⟨w, v, l, c, k, H⟩ := s
  unfold astep at h
  cases H with
  | nil => simp only at h; split at h <;> (split at h <;> cases h)
  | cons hd H1 =>
    simp only at h
    split at h
    · split at h
      · cases h; right; simp
      · cases h
    · split at h
      · split at h
        · split at h
          · cases h; right; simp; omega
          · cases h
        · split at h
          · split at h
            · cases h; left; simp; omega
            · cases h; left; simp; omega
          · split at h
            · cases h; right
              have := leadOnes_le H1
              simp only [List.length_cons, List.length_drop, true_and]; omega
            · cases h
      · cases h

theorem astep_mono_done {s : AS} {d w v : Nat} (h : astep s = .done d w v) :
    s.w = w ∧ s.l + s.H.length ≤ d + 1 := by
  obtain ⟨w0, v0, l, c, k, H⟩ := s
  unfold astep at h
  cases H with
  | nil =>
    simp only at h
    split at h
    · split at h
      · cases h; simp; omega
      · cases h
    · split at h
      · cases h; simp; omega
      · cases h
  | cons hd H1 =>
    simp only at h
    split at h
    · split at h <;> cases h
    · split at h
      · split at h
        · split at h <;> cases h
        · split at h
          · split at h <;> cases h
          · split at h <;> cases h
      · cases h

theorem arun_mono : ∀ (n : Nat) (s : AS) {d w v : Nat}, arun n s = .done d w v →
    s.w < w ∨ (s.w = w ∧ s.l + s.H.length ≤ d + 1)
  | 0, _, _, _, _, h => by cases h
  | n + 1, s, d, w, v, h => by
    unfold arun at h
    split at h
    · rename_i s' hs
      have h1 := astep_mono hs
      have h2 := arun_mono n s' h
      omega
    · exact Or.inr (astep_mono_done h)

end H140108
