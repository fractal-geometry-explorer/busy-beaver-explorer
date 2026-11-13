import Rules
import TM.Fin

/-! # The doubling rounds of 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA

* `S x` is the reset configuration `0^inf 1^x 1110 B> 0^inf`; the run from blank tape is in `S 13` after 110 steps
  (`blank_to_S13`).
* `P k m R` is `0^inf F> 0 0 (10)^k 1^m R`: a block of k pairs at the left wall and m ones after it.
* `S_to_P`: `S (x + 6)` reaches `P 3 (x + 6) (0 1 0^inf)`.
* `double`: for k ≥ 2 and m ≥ 2k + 3, `P k m R` reaches `P (2k + 3) (m − 2k − 3) R`: the block of pairs doubles
  (plus 3) and eats as many ones. Proved from `dbl_intro`, k − 1 zig-zag rounds (`zig`, by induction) and `dbl_end`.
* `chain`: so the rounds go on as long as the ones last: `P k m R` reaches `P (kseq k t) (mseq k m t) R`, with
  `kseq k t + 3 = 2^t (k + 3)`, while each round finds at least 2·kseq + 3 ones.

What happens when the ones run out (m < 2k + 3, the overflow) and how the machine gets back to `S (f x)` is not
proved here; see the README. -/

namespace H90097

open TM

/-- The reset configuration `0^inf 1^x 1110 B> 0^inf`. -/
def S (x : Nat) : Config := ⟨cons false (cons true (cons true (cons true (rep x [true] blank)))), blank, .B⟩

/-- A doubling round's start: `0^inf F> 0 0 (10)^k 1^m R`. -/
def P (k m : Nat) (R : Tape) : Config := ⟨blank, cons false (cons false (rep k [true, false] (rep m [true] R))), .F⟩

theorem ones_cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s

theorem pairs_cons (n : Nat) (s : Tape) : rep n [true, false] (cons true (cons false s)) = rep (n + 1) [true, false] s :=
  rep_app_comm n [true, false] s

theorem quads_cons (i : Nat) (s : Tape) :
    cons true (rep i [true, true, true, true] (cons true (cons true (cons true s)))) = rep (i + 1) [true, true, true, true] s := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show cons true (cons true (cons true (cons true (cons true (rep i [true, true, true, true] (cons true (cons true (cons true s)))))))) = _
    rw [ih]; rfl

theorem dquads (i : Nat) (s : Tape) : rep i [true, false, true, false] s = rep (2 * i) [true, false] s := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have e : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
    rw [e, rep_succ, ih]; rfl

theorem halts_free_reach {c₁ c₂ c₃ : Config} (h₁ : ∃ t, steps t c₁ = some c₂) (h₂ : ∃ t, steps t c₂ = some c₃) :
    ∃ t, steps t c₁ = some c₃ := by
  obtain ⟨a, ha⟩ := h₁; obtain ⟨b, hb⟩ := h₂; exact ⟨a + b, steps_seq trans ha hb⟩

/-- z zig-zag rounds: z pairs of the left block move into the block of fours, 2z ones are eaten on the right. -/
theorem zigs (z : Nat) : ∀ (i J m : Nat) (L R : Tape),
    ∃ t, steps t ⟨rep i [true, true, true, true] (rep (J + z) [false, true] L),
        cons true (cons false (rep (m + 2 * z) [true] R)), .F⟩ =
      some ⟨rep (i + z) [true, true, true, true] (rep J [false, true] L), cons true (cons false (rep m [true] R)), .F⟩ := by
  induction z with
  | zero => intro i J m L R; exact ⟨0, rfl⟩
  | succ z ih =>
    intro i J m L R
    have h1 := zig i (J + z) (m + 2 * z) L R
    rw [quads_cons] at h1
    obtain ⟨t, h2⟩ := ih (i + 1) J m L R
    have e1 : J + (z + 1) = J + z + 1 := by omega
    have e2 : m + 2 * (z + 1) = m + 2 * z + 2 := by omega
    have e3 : i + 1 + z = i + (z + 1) := by omega
    rw [e3] at h2
    rw [e1, e2]
    exact ⟨_, steps_seq trans h1 h2⟩

/-- **A doubling round.** `P (j+2) (m + 2j + 7) R` reaches `P (2j + 7) m R`. -/
theorem double_j (j m : Nat) (R : Tape) : ∃ t, steps t (P (j + 2) (m + 2 * j + 7) R) = some (P (2 * j + 7) m R) := by
  have h1 := dbl_intro j (m + 2 * j + 1) R
  have e0 : m + 2 * j + 1 + 6 = m + 2 * j + 7 := by omega
  rw [e0] at h1
  have rot : cons false (rep (j + 1) [true, false] (cons true (cons true (cons true (cons true (cons true (cons true blank)))))))
      = rep 0 [true, true, true, true] (rep (0 + (j + 1)) [false, true]
          (cons false (cons true (cons true (cons true (cons true (cons true (cons true blank)))))))) := by
    rw [Nat.zero_add]
    exact rep_rotate (j + 1) [false] [true, false] [false, true] rfl _
  rw [rot] at h1
  have e1 : m + 2 * j + 1 + 3 = (m + 2) + 2 * (j + 1) := by omega
  rw [e1] at h1
  obtain ⟨t2, h2⟩ := zigs (j + 1) 0 0 (m + 2) (cons false (cons true (cons true (cons true (cons true (cons true
    (cons true blank))))))) R
  rw [Nat.zero_add] at h1 h2
  have h3 := dbl_end (j + 1) m R
  have e3 : cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false
      (rep (j + 1) [true, false, true, false] (cons true (cons false (rep m [true] R)))))))))))
      = rep (2 * j + 7) [true, false] (rep m [true] R) := by
    rw [dquads, pairs_cons]
    have : 2 * (j + 1) + 1 + 4 = 2 * j + 7 := by omega
    rw [← this]; rfl
  rw [e3] at h3
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩

/-- **A doubling round**, for k ≥ 2 and m ≥ 2k + 3: `P k m R` reaches `P (2k + 3) (m − (2k + 3)) R`. -/
theorem double (k m : Nat) (R : Tape) (hk : 2 ≤ k) (hm : 2 * k + 3 ≤ m) :
    ∃ t, steps t (P k m R) = some (P (2 * k + 3) (m - (2 * k + 3)) R) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  obtain ⟨t, h⟩ := double_j j (m - (2 * (j + 2) + 3)) R
  have e1 : m - (2 * (j + 2) + 3) + 2 * j + 7 = m := by omega
  have e2 : 2 * j + 7 = 2 * (j + 2) + 3 := by omega
  rw [e1, e2] at h
  exact ⟨t, h⟩

/-- The block sizes along a chain of doubling rounds. -/
def kseq (k : Nat) : Nat → Nat
  | 0 => k
  | t + 1 => 2 * kseq k t + 3

/-- The ones left along a chain of doubling rounds. -/
def mseq (k m : Nat) : Nat → Nat
  | 0 => m
  | t + 1 => mseq k m t - (2 * kseq k t + 3)

theorem kseq_ge (k : Nat) (hk : 2 ≤ k) (t : Nat) : 2 ≤ kseq k t := by
  induction t with
  | zero => exact hk
  | succ t ih => simp only [kseq]; omega

theorem kseq_closed (k t : Nat) : kseq k t + 3 = 2 ^ t * (k + 3) := by
  induction t with
  | zero => simp [kseq]
  | succ t ih =>
    simp only [kseq]
    rw [Nat.pow_succ]
    have : 2 * kseq k t + 3 + 3 = 2 * (kseq k t + 3) := by omega
    rw [this, ih]
    ac_rfl

/-- **A chain of doubling rounds**, as long as every round finds enough ones. -/
theorem chain (k m : Nat) (R : Tape) (hk : 2 ≤ k) (t : Nat)
    (hm : ∀ s, s < t → 2 * kseq k s + 3 ≤ mseq k m s) :
    ∃ n, steps n (P k m R) = some (P (kseq k t) (mseq k m t) R) := by
  induction t with
  | zero => exact ⟨0, rfl⟩
  | succ t ih =>
    obtain ⟨a, ha⟩ := ih (fun s hs => hm s (by omega))
    obtain ⟨b, hb⟩ := double (kseq k t) (mseq k m t) R (kseq_ge k hk t) (hm t (by omega))
    exact ⟨a + b, steps_seq trans ha hb⟩

/-- From the reset configuration the first doubling round starts with k = 3. -/
theorem S_to_P (x : Nat) : ∃ t, steps t (S (x + 6)) = some (P 3 (x + 6) (cons false (cons true blank))) := by
  have h := reset_start x
  have e : rep (x + 2) [true] (cons true (cons true (cons true (cons true (cons false (cons true blank))))))
      = rep (x + 6) [true] (cons false (cons true blank)) := by
    rw [ones_cons, ones_cons, ones_cons, ones_cons]
  rw [e] at h
  exact ⟨_, h⟩

/-- The run from blank tape is in the reset configuration `S 13` after 110 steps. -/
theorem blank_to_S13 : steps 110 init = some (S 13) := by
  have h := blank_reaches trans (q := .A) (n := 110)
    (c := ⟨[false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true], [], .B⟩)
    (by decide)
  exact h

/-- The first doubling chain of the run: S 13 → P(3, 13) → P(9, 4), where the ones run out (4 < 21). -/
theorem first_chain : ∃ t, steps t init = some (P 9 4 (cons false (cons true blank))) := by
  obtain ⟨a, ha⟩ := S_to_P 7
  obtain ⟨b, hb⟩ := double 3 13 (cons false (cons true blank)) (by omega) (by omega)
  exact ⟨110 + (a + b), steps_seq trans blank_to_S13 (steps_seq trans ha hb)⟩

/-- The chain from k = 3 in closed form: while 12·2^t ≤ m + 3t + 12, all rounds up to t find enough ones, and
after t rounds m + 3t + 12 − 12·2^t ones are left. -/
theorem chain3_closed (m : Nat) (t : Nat) (h : 12 * 2 ^ t ≤ m + 3 * t + 12) :
    (∀ s, s < t → 2 * kseq 3 s + 3 ≤ mseq 3 m s) ∧ mseq 3 m t + 12 * 2 ^ t = m + 3 * t + 12 := by
  induction t with
  | zero => exact ⟨fun s hs => absurd hs (by omega), by simp [mseq]⟩
  | succ t ih =>
    have hp : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
    have ha : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    rw [hp] at h
    obtain ⟨hc, hm⟩ := ih (by omega)
    have hk := kseq_closed 3 t
    have ct : 2 * kseq 3 t + 3 ≤ mseq 3 m t := by omega
    refine ⟨fun s hs => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
      · exact hc s hs
      · subst hs; exact ct
    · simp only [mseq]; rw [hp]; omega

/-- **The doubling phase from a reset.** If 12·2^t ≤ x + 3t + 18, then `S (x + 6)` reaches
`P (6·2^t − 3) (x + 3t + 18 − 12·2^t) (0 1 0^inf)`: t doubling rounds, the block of pairs 3, 9, 21, 45, … The rounds
stop at the first t with 24·2^t > x + 3t + 21 (the ones no longer last), where the overflow begins. -/
theorem S_rounds (x t : Nat) (h : 12 * 2 ^ t ≤ x + 3 * t + 18) :
    ∃ n, steps n (S (x + 6)) = some (P (6 * 2 ^ t - 3) (x + 3 * t + 18 - 12 * 2 ^ t) (cons false (cons true blank))) := by
  obtain ⟨hc, hm⟩ := chain3_closed (x + 6) t (by omega)
  obtain ⟨a, ha⟩ := S_to_P x
  obtain ⟨b, hb⟩ := chain 3 (x + 6) (cons false (cons true blank)) (by omega) t hc
  have hk := kseq_closed 3 t
  have e1 : kseq 3 t = 6 * 2 ^ t - 3 := by omega
  have e2 : mseq 3 (x + 6) t = x + 3 * t + 18 - 12 * 2 ^ t := by omega
  rw [e1, e2] at hb
  exact ⟨a + b, steps_seq trans ha hb⟩

end H90097
