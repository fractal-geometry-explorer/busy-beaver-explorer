/-! The second-overflow cascade of the counter model, and the one way it can make a corner.

For 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- and 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---.

This is a copy, in Lean, of the model step `f` of `coq/SOC23Model.v` (same configurations, same
cases), with the arithmetic half of `coq/SOC23Match.v`. The link to the machines is in Coq:
`halts_iff_corner` (SOC23Corner.v) says that each machine halts from blank tape iff the orbit of
`f` from `cfgL 2 0 5` reaches a corner `cfgL len 0 (2^len)`. Here, for the model alone:

* `doom_step`: a configuration is *doomed* when its plain countdown ends at a corner
  (`cfgL len k n` with `k + n = 2^len`, `cfgR len k n` with `k + n + 1 = 2^len`). The only step of
  `f` that makes a doomed configuration out of one that is not doomed is rule R5 (a shifted counter
  `cfgS1` with an odd number `h = 2a+1` of digits running out), and only when the unread rest `m`
  satisfies `m + 1 = (2D+1) * 2^(3a+3)`, `D = 2^len - 1 - k`.
* `corner_iff_r5`: the orbit from `cfgL 2 0 5` reaches a corner iff it reaches such an R5
  configuration. -/

namespace SOC23Cascade

inductive Config where
  | cfgL (len k n : Nat)
  | cfgR (len k n : Nat)
  | cfgS0 (len k h n m : Nat)
  | cfgS1 (len k h n m : Nat)
open Config

/-- `m = (x*2+1)*2^i`, computed with fuel as in SOC23Model.v. -/
def splitGo : Nat → Nat → Nat → Nat × Nat
  | 0, _, _ => (0, 0)
  | fuel + 1, n, i => if n % 2 = 0 then splitGo fuel (n / 2) (i + 1) else (n / 2, i)

def split (m : Nat) : Nat × Nat := splitGo m m 0

theorem splitGo_spec : ∀ fuel n i, n ≠ 0 → n ≤ fuel →
    n * 2 ^ i = ((splitGo fuel n i).1 * 2 + 1) * 2 ^ (splitGo fuel n i).2
  | 0, n, _, h0, hf => by omega
  | fuel + 1, n, i, h0, hf => by
    unfold splitGo
    split
    · have ih := splitGo_spec fuel (n / 2) (i + 1) (by omega) (by omega)
      rw [← ih, Nat.pow_succ]
      have : n = n / 2 * 2 := by omega
      conv => lhs; rw [this]
      rw [Nat.mul_assoc, Nat.mul_comm 2 (2 ^ i)]
    · simp only
      have : n = n / 2 * 2 + 1 := by omega
      conv => lhs; rw [this]

theorem split_spec (m : Nat) (h : m ≠ 0) : m = ((split m).1 * 2 + 1) * 2 ^ (split m).2 := by
  have := splitGo_spec m m 0 h (Nat.le_refl m)
  simp only [Nat.pow_zero, Nat.mul_one] at this
  exact this

/-- One step of the model, `f` of SOC23Model.v; `none` exactly at a corner. -/
def f : Config → Option Config
  | cfgL len 0 m =>
    if m = 2 ^ len then none
    else some (cfgS0 len (2 ^ len - 1) (split m).2 ((2 ^ (split m).2 - 1) * 2) (split m).1)
  | cfgL len (k + 1) m => some (cfgR len k m)
  | cfgR len k m => some (cfgL len k (m + 1))
  | cfgS0 len k h (n + 1) m => some (cfgS0 len (k - 1) h n m)
  | cfgS0 len k h 0 m =>
    if h % 2 = 0 then
      if m = 0 then some (cfgR (len + 1 + h / 2 * 3) ((k * 2 + 1) * 2 ^ (h / 2 * 3) - 1) 1)
      else some (cfgS1 (len + 1 + h / 2 * 3) ((k * 2 + 1) * 2 ^ (h / 2 * 3) - 1)
        (split m).2 ((2 ^ (split m).2 - 1) * 2) (split m).1)
    else
      if m = 0 then some (cfgR (len + 1 + (h / 2 * 3 + 2)) ((k * 2 + 1) * 2 ^ (h / 2 * 3 + 2) - 1) 0)
      else some (cfgS0 (len + 1 + (h / 2 * 3 + 2)) ((k * 2 + 1) * 2 ^ (h / 2 * 3 + 2) - 1)
        (split m).2 ((2 ^ (split m).2 - 1) * 2 + 1) (split m).1)
  | cfgS1 len k h (n + 1) m => some (cfgS1 len (k - 1) h n m)
  | cfgS1 len k h 0 m =>
    if h % 2 = 0 then
      if m = 0 then some (cfgR (len + 1 + (h / 2 * 3 + 2)) ((k * 2 + 1) * 2 ^ (h / 2 * 3 + 2) - 1) 0)
      else if m % 2 = 0 then
        some (cfgS1 (len + 1 + (h / 2 * 3 + 2)) ((k * 2 + 1) * 2 ^ (h / 2 * 3 + 2) - 1)
          (split (m / 2)).2 ((2 ^ (split (m / 2)).2 - 1) * 2 + 1) (split (m / 2)).1)
      else
        some (cfgS0 (len + 1 + (h / 2 * 3 + 1)) ((k * 2 + 1) * 2 ^ (h / 2 * 3 + 1) - 1)
          (split (m + 1)).2 ((2 ^ (split (m + 1)).2 - 1) * 2) (split (m + 1)).1)
    else some (cfgR (len + 1 + (h / 2 * 3 + 3)) ((k * 2 + 1) * 2 ^ (h / 2 * 3 + 3)) m)

/-- The invariant P of SOC23Model.v. -/
def P : Config → Prop
  | cfgL len k n => 1 ≤ len ∧ k < 2 ^ len ∧ 2 ≤ k + n ∧ k + n < 2 ^ len * 2
  | cfgR len k n => 1 ≤ len ∧ k < 2 ^ len ∧ 2 ≤ k + n + 1 ∧ k + n + 1 < 2 ^ len * 2
  | cfgS0 len k h n m => 1 ≤ len ∧ n + m ≤ k ∧ k < 2 ^ len ∧ n < 2 ^ (h + 1)
  | cfgS1 len k h n m => 1 ≤ len ∧ n + m ≤ k ∧ k < 2 ^ len ∧ n < 2 ^ (h + 1)

def doomed : Config → Prop
  | cfgL len k n => k + n = 2 ^ len
  | cfgR len k n => k + n + 1 = 2 ^ len
  | _ => False

/-- Rule R5 with the unread rest matching the deficit. -/
def r5match : Config → Prop
  | cfgS1 len k h 0 m => h % 2 = 1 ∧ m + 1 = (2 * (2 ^ len - 1 - k) + 1) * 2 ^ (h / 2 * 3 + 3)
  | _ => False

/-- The one configuration outside R5 whose blank end is doomed; never reached (`bad0_step`). -/
def bad0 : Config → Prop
  | cfgS0 len k 0 0 0 => k = 2 ^ len - 1
  | _ => False

theorem pow_pos' (n : Nat) : 0 < 2 ^ n := Nat.pow_pos (by decide)

theorem big_pow (len s : Nat) : 2 ^ (len + 1 + s) = 2 ^ len * 2 * 2 ^ s := by
  rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]

/-- An odd number times `2^s` is never `2^(len+1+s)`. -/
theorem odd_pow_ne (len k s : Nat) : (k * 2 + 1) * 2 ^ s ≠ 2 ^ (len + 1 + s) := by
  intro e
  rw [big_pow] at e
  have := Nat.eq_of_mul_eq_mul_right (pow_pos' s) e
  omega

theorem odd_pos (k s : Nat) : 1 ≤ (k * 2 + 1) * 2 ^ s := Nat.mul_pos (by omega) (pow_pos' s)

/-- Blank end with right counter 0 (rules R2, R3): never doomed. -/
theorem blank0 (len k s : Nat) : ¬ ((k * 2 + 1) * 2 ^ s - 1 + 0 + 1 = 2 ^ (len + 1 + s)) := by
  intro e
  have := odd_pos k s
  exact odd_pow_ne len k s (by omega)

/-- Blank end with right counter 1 (rule R1): doomed only for s = 0 and k = 2^len - 1. -/
theorem blank1 (len k s : Nat) (e : (k * 2 + 1) * 2 ^ s - 1 + 1 + 1 = 2 ^ (len + 1 + s)) :
    s = 0 ∧ k = 2 ^ len - 1 := by
  have := odd_pos k s
  cases s with
  | zero =>
    simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero] at e
    rw [Nat.pow_succ] at e
    exact ⟨rfl, by omega⟩
  | succ a =>
    exfalso
    rw [show len + 1 + (a + 1) = (len + 1 + a) + 1 by omega, Nat.pow_succ, Nat.pow_succ, ← Nat.mul_assoc] at e
    rw [Nat.pow_succ, ← Nat.mul_assoc] at this
    generalize (k * 2 + 1) * 2 ^ a = q at e this
    generalize 2 ^ (len + 1 + a) = r at e
    omega

/-- Rule R5: doomed exactly when the unread rest matches the deficit. -/
theorem r5eq (len k s m : Nat) (hk : k < 2 ^ len) :
    (k * 2 + 1) * 2 ^ s + m + 1 = 2 ^ (len + 1 + s) ↔
    m + 1 = (2 * (2 ^ len - 1 - k) + 1) * 2 ^ s := by
  rw [big_pow, show 2 * (2 ^ len - 1 - k) + 1 = 2 ^ len * 2 - (k * 2 + 1) by omega, Nat.sub_mul]
  have : (k * 2 + 1) * 2 ^ s ≤ 2 ^ len * 2 * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
  generalize (k * 2 + 1) * 2 ^ s = a at this ⊢
  generalize 2 ^ len * 2 * 2 ^ s = b at this ⊢
  omega

theorem doom_step (x y : Config) (hP : P x) (hb : ¬ bad0 x) (hf : f x = some y) (hd : doomed y) :
    doomed x ∨ r5match x := by
  match x, hP, hb, hf with
  | cfgL len 0 m, _, _, hf =>
    simp only [f] at hf; split at hf
    · cases hf
    · cases hf; exact absurd hd id
  | cfgL len (k + 1) m, _, _, hf =>
    simp only [f, Option.some.injEq] at hf; subst hf; simp only [doomed] at hd ⊢; left; omega
  | cfgR len k m, _, _, hf =>
    simp only [f, Option.some.injEq] at hf; subst hf; simp only [doomed] at hd ⊢; left; omega
  | cfgS0 len k h (n + 1) m, _, _, hf =>
    simp only [f, Option.some.injEq] at hf; subst hf; exact absurd hd id
  | cfgS0 len k h 0 m, hP, hb, hf =>
    simp only [P] at hP
    simp only [f] at hf
    split at hf <;> split at hf <;> simp only [Option.some.injEq] at hf <;> subst hf <;>
      simp only [doomed] at hd <;> try exact absurd hd id
    · -- rule R1 on an empty rest: doomed only for h = 0 and k = 2^len - 1, which is bad0
      exfalso
      rename_i hh hm
      subst hm
      obtain ⟨ha, hk⟩ := blank1 len k (h / 2 * 3) hd
      have h0 : h = 0 := by omega
      subst h0
      exact hb hk
    · -- rule R2 on an empty rest
      exact absurd hd (blank0 len k _)
  | cfgS1 len k h (n + 1) m, _, _, hf =>
    simp only [f, Option.some.injEq] at hf; subst hf; exact absurd hd id
  | cfgS1 len k h 0 m, hP, hb, hf =>
    simp only [P] at hP
    simp only [f] at hf
    split at hf
    · split at hf
      · simp only [Option.some.injEq] at hf; subst hf; simp only [doomed] at hd
        exact absurd hd (blank0 len k _)
      · split at hf <;> simp only [Option.some.injEq] at hf <;> subst hf <;> exact absurd hd id
    · -- rule R5
      rename_i hh
      simp only [Option.some.injEq] at hf; subst hf; simp only [doomed] at hd
      right; simp only [r5match]
      exact ⟨by omega, (r5eq len k _ m hP.2.2.1).1 hd⟩

theorem bad0_inv (x : Config) (h : bad0 x) : ∃ len, x = cfgS0 len (2 ^ len - 1) 0 0 0 := by
  match x, h with
  | cfgS0 len k 0 0 0, h => simp only [bad0] at h; subst h; exact ⟨len, rfl⟩

theorem bad0_step (x y : Config) (hP : P x) (hf : f x = some y) : ¬ bad0 y := by
  intro hb
  obtain ⟨l, rfl⟩ := bad0_inv y hb
  match x, hP, hf with
  | cfgL len 0 m, hP, hf =>
    simp only [P] at hP
    simp only [f] at hf; split at hf
    · cases hf
    · simp only [Option.some.injEq, cfgS0.injEq] at hf
      obtain ⟨_, _, hi, _, hx⟩ := hf
      have := split_spec m (by omega)
      rw [hi, hx] at this
      simp at this; omega
  | cfgL len (k + 1) m, _, hf => simp [f] at hf
  | cfgR len k m, _, hf => simp [f] at hf
  | cfgS0 len k h (n + 1) m, hP, hf =>
    simp only [P] at hP
    simp only [f, Option.some.injEq, cfgS0.injEq] at hf
    obtain ⟨rfl, h2, -, -, -⟩ := hf
    omega
  | cfgS0 len k h 0 m, _, hf =>
    simp only [f] at hf
    split at hf <;> split at hf <;> simp only [Option.some.injEq, cfgS0.injEq, reduceCtorEq] at hf
    obtain ⟨-, -, -, hn, -⟩ := hf
    omega
  | cfgS1 len k h (n + 1) m, _, hf => simp [f] at hf
  | cfgS1 len k h 0 m, _, hf =>
    simp only [f] at hf
    split at hf
    · split at hf
      · simp at hf
      · split at hf
        · simp at hf
        · rename_i hm _
          simp only [Option.some.injEq, cfgS0.injEq] at hf
          obtain ⟨_, _, hi, _, hx⟩ := hf
          have := split_spec (m + 1) (by omega)
          rw [hi, hx] at this
          simp at this; omega
    · simp at hf

/-- `P` is kept by every step (the arithmetic half of `f_spec` in SOC23Model.v, which Coq proves
together with the machine steps; it is assumed here, see `iter_P`). -/
def iter : Nat → Config → Option Config
  | 0, x => some x
  | j + 1, x => match f x with
    | some y => iter j y
    | none => none

theorem iter_add (a b : Nat) (x : Config) :
    iter (a + b) x = (match iter a x with | some y => iter b y | none => none) := by
  induction a generalizing x with
  | zero => simp [iter]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [iter]
    cases f x with
    | none => rfl
    | some y => exact ih y

theorem doomed_R : ∀ k len n, k + n + 1 = 2 ^ len →
    iter (k * 2 + 1) (cfgR len k n) = some (cfgL len 0 (2 ^ len))
  | 0, len, n, h => by simp only [iter, f]; congr 2; omega
  | k + 1, len, n, h => by
    rw [show (k + 1) * 2 + 1 = (k * 2 + 1) + 1 + 1 by omega]
    simp only [iter, f]
    exact doomed_R k len (n + 1) (by omega)

theorem r5_corner (x : Config) (hP : P x) (hr : r5match x) :
    ∃ j len, iter j x = some (cfgL len 0 (2 ^ len)) := by
  match x, hP, hr with
  | cfgS1 len k h 0 m, hP, hr =>
    simp only [P] at hP
    simp only [r5match] at hr
    obtain ⟨ho, hm⟩ := hr
    refine ⟨((k * 2 + 1) * 2 ^ (h / 2 * 3 + 3)) * 2 + 1 + 1, len + 1 + (h / 2 * 3 + 3), ?_⟩
    simp only [iter, f, show ¬ (h % 2 = 0) by omega, ite_false]
    exact doomed_R _ _ _ ((r5eq len k _ m hP.2.2.1).2 hm)

/-- Walking back along an orbit whose steps keep `P`: a doomed configuration is reached only
through an R5 match (or the start is already doomed). The hypothesis `hP` is what `f_spec`
proves in Coq. -/
theorem doom_back (hP : ∀ x y, P x → f x = some y → P y) :
    ∀ j x z, P x → ¬ bad0 x → iter j x = some z → doomed z →
      doomed x ∨ ∃ i w, iter i x = some w ∧ r5match w
  | 0, x, z, _, _, h, hd => by simp only [iter, Option.some.injEq] at h; subst h; exact Or.inl hd
  | j + 1, x, z, hx, hb, h, hd => by
    simp only [iter] at h
    cases hf : f x with
    | none => rw [hf] at h; cases h
    | some y =>
      rw [hf] at h
      rcases doom_back hP j y z (hP x y hx hf) (bad0_step x y hx hf) h hd with hy | ⟨i, w, hw, hr⟩
      · rcases doom_step x y hx hb hf hy with hx' | hr
        · exact Or.inl hx'
        · exact Or.inr ⟨0, x, rfl, hr⟩
      · refine Or.inr ⟨i + 1, w, ?_, hr⟩
        simp only [iter, hf]; exact hw

theorem iter_P (hP : ∀ x y, P x → f x = some y → P y) :
    ∀ j x y, P x → iter j x = some y → P y
  | 0, x, y, hx, h => by simp only [iter, Option.some.injEq] at h; subst h; exact hx
  | j + 1, x, y, hx, h => by
    simp only [iter] at h
    cases hf : f x with
    | none => rw [hf] at h; cases h
    | some z => rw [hf] at h; exact iter_P hP j z y (hP x z hx hf) h

/-- The orbit from `cfgL 2 0 5` reaches a corner iff it reaches an R5 match. With Coq's
`halts_iff_corner` (and `f_spec` for `hP`) this is `halts_iff_r5_match` of SOC23Match.v. -/
theorem corner_iff_r5 (hP : ∀ x y, P x → f x = some y → P y) :
    (∃ j len, iter j (cfgL 2 0 5) = some (cfgL len 0 (2 ^ len))) ↔
    (∃ j x, iter j (cfgL 2 0 5) = some x ∧ r5match x) := by
  have h0 : P (cfgL 2 0 5) := by simp only [P]; decide
  constructor
  · rintro ⟨j, len, h⟩
    rcases doom_back hP j _ _ h0 (by simp [bad0]) h (by simp [doomed]) with hd | hr
    · simp only [doomed] at hd; exact absurd hd (by decide)
    · exact hr
  · rintro ⟨j, x, hx, hr⟩
    obtain ⟨i, len, hi⟩ := r5_corner x (iter_P hP j _ x h0 hx) hr
    exact ⟨j + i, len, by rw [iter_add, hx]; exact hi⟩

end SOC23Cascade
