import Machine
import Rules

/-!
# 1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF: the run as a counter with a carry wave

The twin of `1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF` (the same tapes at the same moments, other states and
slightly different step counts); this file is that machine's `Wave.lean` with the states changed and a different
run back to the right end (state C crossing the digits).

Written by hand on top of the generated `Rules.lean`.  The tape is a list of *digits* (blocks of 1s, each followed
by one 0).  Lists are written nearest the head first.

* `S0 ds` is `0^inf 1^dₙ 0 … 1^d₁ 0 1^d₀ 0 1^14 0 1^7 0 1^6 0 1^4 0 A> 1 0^inf` for `ds = [d₀, d₁, …, dₙ]`:
  the head at the right end, four fixed low digits.
* `W a rs ps` is the *carry wave* standing on a digit with `a` ones:
  `… 1^r₁ 0 1^r₀ 0 1^a B> 1 1 0 1^p₀ 0 1^p₁ 0 … 1^14 0 1^7 0 1^6 0 1^4 0 1^2 0^inf`
  (`rs` the digits to its left, `ps` the digits it has already written to its right).

One cycle (`cycle`, 5009 steps) takes `S0 (x :: rs)` to `W (x + 61) rs []`.  Then the wave moves left:

* on an odd `a ≥ 3` it leaves the digit `a / 2 + 1` behind and moves on with `y + a / 2` (`y` the next digit);
* on an even `a ≥ 2` it stops: the digit becomes `a / 2 + 3`, its left neighbour grows by `a / 2`, and the head
  runs back to the right end, to the next `S0`;
* at the left end of the tape there is no next digit (`y = 0`); there `a = 1` halts (`W_one_halts`).

`next` is this map on digit lists; `halts_iff` says that the machine halts from blank tape exactly when iterating
`next` from the digits `[26, 13, 9, 6]` (reached at step 6053) ends in `none`, i.e. when a wave reaches the left end
of the tape with `a = 1`.  This happens exactly when the value the wave carries onto the leftmost digit is
`2^t - 1`.
-/

namespace H41157

open TM

set_option maxRecDepth 20000

/-! ## Tapes and configurations -/

/-- Digits nearest first, each followed (outward) by one 0; then blank tape. -/
def LT : List Nat → Tape
  | [] => blank
  | d :: ds => rep d [true] (cons false (LT ds))

/-- The fixed right end during a wave: `1^14 0 1^7 0 1^6 0 1^4 0 1^2 0^inf`. -/
def Tt : Tape :=
  rep 14 [true] (cons false (rep 7 [true] (cons false (rep 6 [true] (cons false (rep 4 [true] (cons false
    (rep 2 [true] blank))))))))

/-- The digits the wave has written to its right (nearest first), then `Tt`. -/
def RT : List Nat → Tape
  | [] => Tt
  | p :: ps => rep p [true] (cons false (RT ps))

/-- The start of a cycle: the head at the right end on a 1, the digits `ds` left of four fixed digits. -/
def S0 (ds : List Nat) : Config := ⟨cons false (LT (4 :: 6 :: 7 :: 14 :: ds)), cons true blank, .A⟩

/-- The carry wave on a digit with `a` ones, digits `rs` to its left and `ps` written to its right. -/
def W (a : Nat) (rs ps : List Nat) : Config :=
  ⟨rep a [true] (cons false (LT rs)), cons true (cons true (cons false (RT ps))), .B⟩

/-- The zigzag inside a digit: `L 0 1^p 0 A> 1^n 0 0 1^r 0 R`. -/
def Z (p n r : Nat) (L R : Tape) : Config :=
  ⟨cons false (rep p [true] (cons false L)), rep n [true] (cons false (cons false (rep r [true] (cons false R)))), .A⟩

/-- The run to the right: `… 0 1^m C> 0 R`, the digit `m` still growing by the cell under the head. -/
def Cc (m : Nat) (ds : List Nat) (R : Tape) : Config := ⟨rep m [true] (cons false (LT ds)), cons false R, .C⟩

def Reach (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reach.trans {a b c : Config} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂; exact ⟨n + m, steps_seq H41157.trans hn hm⟩

theorem Reach.of_steps {n : Nat} {a b : Config} (h : steps n a = some b) : Reach a b := ⟨n, h⟩

theorem rep_t_cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s

/-! ## The pieces, in the shapes above -/

theorem cycle' (x : Nat) (rs : List Nat) : steps 5009 (S0 (x :: rs)) = some (W (x + 61) rs []) :=
  cycle x (LT rs)

theorem w2z' (q y : Nat) (L R : Tape) :
    Reach ⟨rep (q + 2) [true] (cons false (rep y [true] (cons false L))), cons true (cons true (cons false R)), .B⟩
      (Z (y + 1) q 1 L R) :=
  Reach.of_steps (w2z q y L R)

/-- One zigzag: two cells of the digit go, one to each side. -/
theorem zig (p m r : Nat) (L R : Tape) : Reach (Z p (m + 2) r L R) (Z (p + 1) m (r + 1) L R) := by
  cases m with
  | zero => exact Reach.of_steps (zigB p r L R)
  | succ q => exact Reach.of_steps (zigA p r q L R)

theorem zigs (i : Nat) : ∀ (p n r : Nat) (L R : Tape), Reach (Z p (n + 2 * i) r L R) (Z (p + i) n (r + i) L R) := by
  induction i with
  | zero => intro p n r L R; exact ⟨0, rfl⟩
  | succ i ih =>
    intro p n r L R
    have e : n + 2 * (i + 1) = (n + 2 * i) + 2 := by omega
    rw [e]
    have h := (zig p (n + 2 * i) r L R).trans (ih (p + 1) n (r + 1) L R)
    rw [show p + 1 + i = p + (i + 1) by omega, show r + 1 + i = r + (i + 1) by omega] at h
    exact h

theorem zend1' (p r : Nat) (L R : Tape) :
    Reach (Z p 1 r L R) ⟨rep p [true] (cons false L), cons true (cons true (cons false (rep (r + 1) [true] (cons false R)))), .B⟩ :=
  Reach.of_steps (zend1 p r L R)

theorem zend0' (p r : Nat) (rs : List Nat) (R : Tape) :
    Reach (Z p 0 r (LT rs) R) (Cc (r + 2) (p :: rs) R) := by
  have h := zend0 p r (LT rs) R
  rw [rep_t_cons, rep_t_cons] at h
  exact Reach.of_steps h

theorem cs' (m d : Nat) (ds : List Nat) (R : Tape) :
    Reach (Cc m ds (rep (d + 2) [true] (cons false R))) (Cc (d + 1) ((m + 1) :: ds) R) := by
  have h := cs d (rep m [true] (cons false (LT ds))) R
  rw [rep_t_cons] at h
  exact Reach.of_steps h

/-- The run through the digits the wave wrote, back to the start of a cycle. -/
theorem sweep (ps : List Nat) : ∀ (ds : List Nat) (m : Nat), (∀ p ∈ ps, 2 ≤ p) →
    Reach (Cc m ds (RT ps)) (S0 (ps.reverse ++ (m + 1) :: ds)) := by
  induction ps with
  | nil =>
    intro ds m _
    exact Reach.of_steps (cfin (rep m [true] (cons false (LT ds))))
  | cons p ps ih =>
    intro ds m hp
    obtain ⟨g, rfl⟩ : ∃ g, p = g + 2 := ⟨p - 2, by have := hp p (by simp); omega⟩
    have h1 := cs' m g ds (RT ps)
    have h2 := ih ((m + 1) :: ds) (g + 1) (fun q hq => hp q (by simp [hq]))
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact h1.trans h2

/-! ## The wave on one digit -/

/-- An odd digit `2j+3`: the wave leaves `j+2` behind and moves to the next digit, which grows by `j+1`. -/
theorem W_odd (j y : Nat) (rs ps : List Nat) : Reach (W (2 * j + 3) (y :: rs) ps) (W (y + j + 1) rs ((j + 2) :: ps)) := by
  have h1 := w2z' (2 * j + 1) y (LT rs) (RT ps)
  have h2 := zigs j (y + 1) 1 1 (LT rs) (RT ps)
  rw [show 1 + 2 * j = 2 * j + 1 by omega] at h2
  have h3 := zend1' (y + 1 + j) (1 + j) (LT rs) (RT ps)
  have h := (h1.trans h2).trans h3
  rw [show y + 1 + j = y + j + 1 by omega, show 1 + j + 1 = j + 2 by omega] at h
  exact h

/-- An even digit `2j+2`: the digit becomes `j+4`, its left neighbour grows by `j+1`, back to `S0`. -/
theorem W_even (j y : Nat) (rs ps : List Nat) (hp : ∀ p ∈ ps, 2 ≤ p) :
    Reach (W (2 * j + 2) (y :: rs) ps) (S0 (ps.reverse ++ (j + 4) :: (y + j + 1) :: rs)) := by
  have h1 := w2z' (2 * j) y (LT rs) (RT ps)
  have h2 := zigs j (y + 1) 0 1 (LT rs) (RT ps)
  rw [show 0 + 2 * j = 2 * j by omega] at h2
  have h12 := h1.trans h2
  rw [show y + j + 1 = y + 1 + j by omega, show j + 4 = 1 + j + 2 + 1 by omega]
  have h3 := zend0' (y + 1 + j) (1 + j) rs (RT ps)
  exact (h12.trans h3).trans (sweep ps _ _ hp)

/-- At the left end of the tape the next digit is `0`. -/
theorem W_nil (a : Nat) (ps : List Nat) : W a [] ps = W a [0] ps := by
  simp only [W, LT, rep_zero, cons_false_blank]

theorem halts_of_reach {c c' : Config} (h : Reach c c') (h' : Halts trans c') : Halts trans c := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, c'', hm, hs⟩ := h'
  exact ⟨n + m, c'', steps_seq H41157.trans hn hm, hs⟩

/-- `W 1` at the left end halts: E reads a 0 five steps later. -/
theorem W_one_halts (ps : List Nat) (hp : ∀ p ∈ ps, 2 ≤ p) : Halts trans (W 1 [] ps) := by
  obtain ⟨g, R, hR⟩ : ∃ g R, RT ps = rep (g + 2) [true] (cons false R) := by
    cases ps with
    | nil => exact ⟨12, _, rfl⟩
    | cons p ps =>
      obtain ⟨g, rfl⟩ : ∃ g, p = g + 2 := ⟨p - 2, by have := hp p (by simp); omega⟩
      exact ⟨g, RT ps, rfl⟩
  have e : W 1 [] ps = ⟨cons true blank, cons true (cons true (cons false (rep (g + 2) [true] (cons false R)))), .B⟩ := by
    simp only [W, LT, hR, cons_false_blank]; rfl
  rw [e]
  exact ⟨5, _, halt1 g R, rfl⟩

/-! ## The map on digit lists -/

/-- The wave at the left end of the tape (no digit further left): `none` is a halt. -/
def waveL (a : Nat) (ps : List Nat) : Option (List Nat) :=
  if _h1 : a = 1 then none
  else if h2 : a % 2 = 1 then waveL (a / 2) ((a / 2 + 1) :: ps)
  else some (ps.reverse ++ [a / 2 + 3, a / 2])
termination_by a
decreasing_by omega

/-- The wave on the digit `a`, digits `rs` to its left, `ps` written to its right. -/
def wave : Nat → List Nat → List Nat → Option (List Nat)
  | a, [], ps => waveL a ps
  | a, y :: rs, ps =>
    if a % 2 = 1 then wave (y + a / 2) rs ((a / 2 + 1) :: ps)
    else some (ps.reverse ++ (a / 2 + 3) :: (y + a / 2) :: rs)

/-- One cycle: the low digit `x` gains 48 and the wave starts on it. -/
def next : List Nat → Option (List Nat)
  | [] => none
  | x :: rs => wave (x + 61) rs []

/-- Digits of a cycle start: at least one, all positive. -/
def Inv (ds : List Nat) : Prop := ds ≠ [] ∧ ∀ d ∈ ds, 1 ≤ d

theorem inv_out (ps : List Nat) (u v : Nat) (rs : List Nat) (hp : ∀ p ∈ ps, 2 ≤ p) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : ∀ y ∈ rs, 1 ≤ y) : Inv (ps.reverse ++ u :: v :: rs) := by
  refine ⟨by simp, fun d hd => ?_⟩
  simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hd
  rcases hd with hd | rfl | rfl | hd
  · have := hp d hd; omega
  · exact hu
  · exact hv
  · exact hr d hd

theorem waveL_some (a : Nat) : ∀ (ps ds : List Nat), 1 ≤ a → (∀ p ∈ ps, 2 ≤ p) → waveL a ps = some ds →
    Reach (W a [] ps) (S0 ds) ∧ Inv ds := by
  induction a using Nat.strongRecOn with
  | _ a ih =>
  intro ps ds ha hp h
  unfold waveL at h
  by_cases h1 : a = 1
  · simp [h1] at h
  by_cases h2 : a % 2 = 1
  · simp only [h1, h2, dite_false, dite_true] at h
    obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j + 3 := ⟨a / 2 - 1, by omega⟩
    have e : (2 * j + 3) / 2 = j + 1 := by omega
    rw [e] at h
    have hp' : ∀ p ∈ (j + 1 + 1) :: ps, 2 ≤ p := by
      intro p hp2; simp only [List.mem_cons] at hp2; rcases hp2 with rfl | hp2
      · omega
      · exact hp p hp2
    obtain ⟨r, i⟩ := ih (j + 1) (by omega) _ ds (by omega) hp' h
    refine ⟨?_, i⟩
    have h0 := W_odd j 0 [] ps
    rw [← W_nil, show 0 + j + 1 = j + 1 by omega] at h0
    exact h0.trans r
  · simp only [h1, h2, dite_false] at h
    obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j + 2 := ⟨a / 2 - 1, by omega⟩
    have e : (2 * j + 2) / 2 = j + 1 := by omega
    rw [e] at h
    cases h
    have h0 := W_even j 0 [] ps hp
    rw [← W_nil, show 0 + j + 1 = j + 1 by omega, show j + 4 = j + 1 + 3 by omega] at h0
    exact ⟨h0, inv_out ps _ _ [] hp (by omega) (by omega) (by simp)⟩

theorem waveL_none (a : Nat) : ∀ (ps : List Nat), 1 ≤ a → (∀ p ∈ ps, 2 ≤ p) → waveL a ps = none →
    Halts trans (W a [] ps) := by
  induction a using Nat.strongRecOn with
  | _ a ih =>
  intro ps ha hp h
  unfold waveL at h
  by_cases h1 : a = 1
  · subst h1; exact W_one_halts ps hp
  by_cases h2 : a % 2 = 1
  · simp only [h1, h2, dite_false, dite_true] at h
    obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j + 3 := ⟨a / 2 - 1, by omega⟩
    have e : (2 * j + 3) / 2 = j + 1 := by omega
    rw [e] at h
    have hp' : ∀ p ∈ (j + 1 + 1) :: ps, 2 ≤ p := by
      intro p hp2; simp only [List.mem_cons] at hp2; rcases hp2 with rfl | hp2
      · omega
      · exact hp p hp2
    have hh := ih (j + 1) (by omega) _ (by omega) hp' h
    have h0 := W_odd j 0 [] ps
    rw [← W_nil, show 0 + j + 1 = j + 1 by omega] at h0
    exact halts_of_reach h0 hh
  · simp [h1, h2] at h

theorem wave_some (rs : List Nat) : ∀ (a : Nat) (ps ds : List Nat), 2 ≤ a → (∀ y ∈ rs, 1 ≤ y) →
    (∀ p ∈ ps, 2 ≤ p) → wave a rs ps = some ds → Reach (W a rs ps) (S0 ds) ∧ Inv ds := by
  induction rs with
  | nil => intro a ps ds ha _ hp h; exact waveL_some a ps ds (by omega) hp h
  | cons y rs ih =>
    intro a ps ds ha hr hp h
    have hy : 1 ≤ y := hr y (by simp)
    have hr' : ∀ z ∈ rs, 1 ≤ z := fun z hz => hr z (by simp [hz])
    simp only [wave] at h
    by_cases h2 : a % 2 = 1
    · simp only [h2, ite_true] at h
      obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j + 3 := ⟨a / 2 - 1, by omega⟩
      have e : (2 * j + 3) / 2 = j + 1 := by omega
      rw [e] at h
      have hp' : ∀ p ∈ (j + 1 + 1) :: ps, 2 ≤ p := by
        intro p hp2; simp only [List.mem_cons] at hp2; rcases hp2 with rfl | hp2
        · omega
        · exact hp p hp2
      obtain ⟨r, i⟩ := ih (y + (j + 1)) _ ds (by omega) hr' hp' h
      have h0 := W_odd j y rs ps
      rw [show y + j + 1 = y + (j + 1) by omega] at h0
      exact ⟨h0.trans r, i⟩
    · simp only [h2] at h
      obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j + 2 := ⟨a / 2 - 1, by omega⟩
      have e : (2 * j + 2) / 2 = j + 1 := by omega
      rw [e] at h
      cases h
      have h0 := W_even j y rs ps hp
      rw [show y + j + 1 = y + (j + 1) by omega, show j + 4 = j + 1 + 3 by omega] at h0
      exact ⟨h0, inv_out ps _ _ rs hp (by omega) (by omega) hr'⟩

theorem wave_none (rs : List Nat) : ∀ (a : Nat) (ps : List Nat), 2 ≤ a → (∀ y ∈ rs, 1 ≤ y) →
    (∀ p ∈ ps, 2 ≤ p) → wave a rs ps = none → Halts trans (W a rs ps) := by
  induction rs with
  | nil => intro a ps ha _ hp h; exact waveL_none a ps (by omega) hp h
  | cons y rs ih =>
    intro a ps ha hr hp h
    have hy : 1 ≤ y := hr y (by simp)
    have hr' : ∀ z ∈ rs, 1 ≤ z := fun z hz => hr z (by simp [hz])
    simp only [wave] at h
    by_cases h2 : a % 2 = 1
    · simp only [h2, ite_true] at h
      obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j + 3 := ⟨a / 2 - 1, by omega⟩
      have e : (2 * j + 3) / 2 = j + 1 := by omega
      rw [e] at h
      have hp' : ∀ p ∈ (j + 1 + 1) :: ps, 2 ≤ p := by
        intro p hp2; simp only [List.mem_cons] at hp2; rcases hp2 with rfl | hp2
        · omega
        · exact hp p hp2
      have hh := ih (y + (j + 1)) _ (by omega) hr' hp' h
      have h0 := W_odd j y rs ps
      rw [show y + j + 1 = y + (j + 1) by omega] at h0
      exact halts_of_reach h0 hh
    · simp [h2] at h

/-- One cycle: from `S0 ds` to the next `S0`, at least one step later. -/
theorem next_some (ds ds' : List Nat) (hi : Inv ds) (h : next ds = some ds') :
    (∃ n, 1 ≤ n ∧ steps n (S0 ds) = some (S0 ds')) ∧ Inv ds' := by
  obtain ⟨hne, hpos⟩ := hi
  match ds, hne, hpos, h with
  | x :: rs, _, hpos, h =>
    obtain ⟨⟨m, hm⟩, i⟩ := wave_some rs (x + 61) [] ds' (by omega) (fun y hy => hpos y (by simp [hy]))
      (by simp) h
    exact ⟨⟨5009 + m, by omega, steps_seq H41157.trans (cycle' x rs) hm⟩, i⟩

theorem next_none (ds : List Nat) (hi : Inv ds) (h : next ds = none) : Halts trans (S0 ds) := by
  obtain ⟨hne, hpos⟩ := hi
  match ds, hne, hpos, h with
  | x :: rs, _, hpos, h =>
    exact halts_of_reach (Reach.of_steps (cycle' x rs))
      (wave_none rs (x + 61) [] (by omega) (fun y hy => hpos y (by simp [hy])) (by simp) h)

/-! ## From blank tape -/

/-- The digits at the `k`-th cycle start (`none` once a wave has halted the machine). -/
def iter : Nat → Option (List Nat)
  | 0 => some [26, 13, 9, 6]
  | k + 1 => (iter k).bind next

theorem start' : steps 6053 init = some (S0 [26, 13, 9, 6]) := by
  show steps 6053 ⟨blank, blank, .A⟩ = some (S0 [26, 13, 9, 6])
  simp only [S0, LT, rep_succ, rep_zero, app_cons, app_nil, cons_false_blank]
  exact start

theorem reach (k : Nat) : ∀ ds, iter k = some ds → Inv ds ∧ ∃ n, k ≤ n ∧ steps n init = some (S0 ds) := by
  induction k with
  | zero =>
    intro ds h; cases h
    exact ⟨⟨by simp, by simp⟩, 6053, by omega, start'⟩
  | succ k ih =>
    intro ds h
    simp only [iter] at h
    cases hk : iter k with
    | none => rw [hk] at h; cases h
    | some ds0 =>
      rw [hk] at h
      obtain ⟨i0, n, hn, hs⟩ := ih ds0 hk
      obtain ⟨⟨m, hm, hs'⟩, i⟩ := next_some ds0 ds i0 h
      exact ⟨i, n + m, by omega, steps_seq H41157.trans hs hs'⟩

/-- **The machine halts from blank tape exactly when the digit iteration reaches `none`**, i.e. when a carry
wave arrives at the left end of the tape with a single 1. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ k, iter k = none := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hno => ?_
    have hall : ∀ k, ∃ ds, iter k = some ds := by
      intro k
      cases hk : iter k with
      | none => exact absurd ⟨k, hk⟩ hno
      | some ds => exact ⟨ds, rfl⟩
    apply not_halts_of_forall H41157.trans _ hh
    apply forall_of_unbounded H41157.trans (fun m => ∃ c', steps m init = some c')
    · intro n
      obtain ⟨ds, hds⟩ := hall n
      obtain ⟨_, m, hm, hs⟩ := reach n ds hds
      exact ⟨m, hm, _, hs⟩
    · intro m hm; exact hm
  · rintro ⟨k, hk⟩
    induction k with
    | zero => simp [iter] at hk
    | succ k ih =>
      simp only [iter] at hk
      cases hk' : iter k with
      | none => exact ih hk'
      | some ds =>
        rw [hk'] at hk
        obtain ⟨i, n, _, hs⟩ := reach k ds hk'
        exact halts_of_reach (Reach.of_steps hs) (next_none ds i hk)

end H41157
