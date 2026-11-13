import Base

/-!
# The recursive counter of 1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA

`K n c R` is the tape right of the head in `B> 0 1^(2n+1) 0 1^c R`.  A *frame* is the word `0 1 1` left of the head.
The main theorem `rule_G`: for every `k ≥ 1`, `r`, `c ≥ k` and all tapes `L`, `R`,

    L 0 0 (0 1 1)^r  B> 0 1^(2k+1) 0 1^c R   reaches   L B> 0 1^(2(r+k+1)+1) 0 1^(c+r) R.

With `r = 0` this is the counter step `M_k`: `0 0 B>0 1^(2k+1) 0 1^c` becomes `B>0 1^(2k+3) 0 1^c`, two cells to the
left, whenever `c ≥ k`.  It is proved by strong induction on `k` from the five rules of `Base.lean`:
`M_k` (k ≥ 2) is `ruleP`, then `M_1, ..., M_(k-2)`, then `G(1, k-1)`; `G(r, k)` the same with `G(r+1, k-1)` last;
`G(r+1, 1)` is `ruleX0`, `r+1` times `ruleY`, then `ruleZ`; `G(0, 1)` is `ruleM1`.
The step counts are not stated here (they are exponential in `k`; `py/hybrid.py` computes them).
-/

namespace H54294

open TM

/-- `a` reaches `b` in some number of steps. -/
def Reach (a b : Cfg St) : Prop := ∃ t, steps t a = some b

theorem Reach.trans' {a b c : Cfg St} (h1 : Reach a b) (h2 : Reach b c) : Reach a c := by
  obtain ⟨t1, h1⟩ := h1
  obtain ⟨t2, h2⟩ := h2
  exact ⟨t1 + t2, TM.steps_seq trans h1 h2⟩

theorem Reach.refl' (a : Cfg St) : Reach a a := ⟨0, rfl⟩

theorem reach_of {t : Nat} {a b : Cfg St} (h : steps t a = some b) : Reach a b := ⟨t, h⟩

/-- A frame `0 1 1`, as it is read going left from the head. -/
abbrev F : List Bool := [true, true, false]

/-- `0 1^(2n+1) 0 1^c R`, the head on the first 0. -/
def K (n c : Nat) (R : Tape) : Tape := cons false (rep (2 * n + 1) [true] (cons false (rep c [true] R)))

theorem ones_add (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s :=
  (rep_add a b [true] s).symm

theorem ones_succ (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl

theorem ones3 (n : Nat) (s : Tape) : cons true (cons true (cons true (rep n [true] s))) = rep (n + 3) [true] s :=
  rfl

theorem zeros_two (m : Nat) (s : Tape) :
    rep (2 * (m + 1)) [false] s = cons false (cons false (rep (2 * m) [false] s)) := by
  have e : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  rw [e]; rfl

/-- `L (0 1 1)^t 0 1^(2s+2) D> 0 1^c R` reaches `L 0 1^(2s+2+2t) D> 0 1^(c+t) R` (`ruleY`, `t` times). -/
theorem rule_Yn (t : Nat) : ∀ (s c : Nat) (L R : Tape),
    Reach ⟨rep (2 * s + 2) [true] (cons false (rep t F L)), cons false (rep c [true] R), .D⟩
      ⟨rep (2 * s + 2 + 2 * t) [true] (cons false L), cons false (rep (c + t) [true] R), .D⟩ := by
  induction t with
  | zero => intro s c L R; exact Reach.refl' _
  | succ t ih =>
    intro s c L R
    have h1 := ruleY c s (rep t F L) R
    have e1 : rep (2 * s) [true] (cons true (cons true (cons true (cons true (cons false (rep t F L))))))
        = rep (2 * (s + 1) + 2) [true] (cons false (rep t F L)) := by
      rw [show cons true (cons true (cons true (cons true (cons false (rep t F L)))))
          = rep 4 [true] (cons false (rep t F L)) from rfl, ones_add,
        show 2 * s + 4 = 2 * (s + 1) + 2 by omega]
    rw [e1, ones_succ] at h1
    refine Reach.trans' (reach_of h1) ?_
    have h2 := ih (s + 1) (c + 1) L R
    rw [show 2 * (s + 1) + 2 + 2 * t = 2 * s + 2 + 2 * (t + 1) by omega,
      show c + 1 + t = c + (t + 1) by omega] at h2
    exact h2

/-- `G(r+1, 1)`: `L 0 0 (0 1 1)^(r+1) B> 0 1^3 0 1^(c+1) R` reaches `L B> 0 1^(2r+7) 0 1^(c+r+2) R`. -/
theorem rule_X (r c : Nat) (L R : Tape) :
    Reach ⟨rep (r + 1) F (cons false (cons false L)), K 1 (c + 1) R, .B⟩
      ⟨L, K (r + 3) (c + 1 + (r + 1)) R, .B⟩ := by
  have h1 := ruleX0 c (rep r F (cons false (cons false L))) R
  refine Reach.trans' (reach_of h1) ?_
  have h2 := rule_Yn (r + 1) 1 c (cons false (cons false L)) R
  refine Reach.trans' (b := ⟨rep (2 * 1 + 2 + 2 * (r + 1)) [true] (cons false (cons false (cons false L))),
    cons false (rep (c + (r + 1)) [true] R), .D⟩) ?_ ?_
  · exact h2
  · have h3 := ruleZ (c + (r + 1)) (r + 2) L R
    rw [show 2 * (r + 2) + 2 = 2 * 1 + 2 + 2 * (r + 1) by omega] at h3
    simp only [ones_succ] at h3
    rw [show 2 * (r + 2) + 1 + 1 + 1 = 2 * (r + 3) + 1 by omega,
      show c + (r + 1) + 1 = c + 1 + (r + 1) by omega] at h3
    exact reach_of h3

/-- `ruleP` in the `K` notation: `L B> 0 1^(2i+5) 0 1^(c+1) R` reaches `L 0 1 1 0^(2i) B> 0 1^3 0 1^c R`. -/
theorem rule_P (i c : Nat) (L R : Tape) :
    Reach ⟨L, K (i + 2) (c + 1) R, .B⟩ ⟨rep (2 * i) [false] (app F L), K 1 c R, .B⟩ := by
  have h := ruleP c i L R
  unfold K
  rw [show 2 * (i + 2) + 1 = 2 * i + 5 by omega]
  exact reach_of h

/-- The counter step `M_j` at block value `c`, for every left tape. -/
def MStep (j c : Nat) : Prop :=
  ∀ L R : Tape, Reach ⟨cons false (cons false L), K j c R, .B⟩ ⟨L, K (j + 1) c R, .B⟩

/-- `m` counter steps in a row: `L 0^(2m) B> 0 1^(2a+1) 0 1^c R` reaches `L B> 0 1^(2(a+m)+1) 0 1^c R`. -/
theorem chain (m : Nat) : ∀ (a c : Nat) (L R : Tape), (∀ j, a ≤ j → j < a + m → MStep j c) →
    Reach ⟨rep (2 * m) [false] L, K a c R, .B⟩ ⟨L, K (a + m) c R, .B⟩ := by
  induction m with
  | zero => intro a c L R _; exact Reach.refl' _
  | succ m ih =>
    intro a c L R hM
    rw [zeros_two]
    refine Reach.trans' (hM a (Nat.le_refl a) (by omega) (rep (2 * m) [false] L) R) ?_
    have h := ih (a + 1) c L R (fun j h1 h2 => hM j (by omega) (by omega))
    rw [show a + 1 + m = a + (m + 1) by omega] at h
    exact h

/-- The statement of `G(r, k)` for all `r` and all `c ≥ k`. -/
def GStmt (k : Nat) : Prop :=
  ∀ r c : Nat, k ≤ c → ∀ L R : Tape,
    Reach ⟨rep r F (cons false (cons false L)), K k c R, .B⟩ ⟨L, K (r + k + 1) (c + r) R, .B⟩

theorem mstep_of_G {j : Nat} (h : GStmt j) (c : Nat) (hc : j ≤ c) : MStep j c := by
  intro L R
  have h' := h 0 c hc L R
  rw [show 0 + j + 1 = j + 1 by omega, show c + 0 = c by omega] at h'
  exact h'

/-- **The recursion.** For every `k ≥ 1`, `r`, `c ≥ k`: `L 0 0 (0 1 1)^r B> 0 1^(2k+1) 0 1^c R` reaches
`L B> 0 1^(2(r+k+1)+1) 0 1^(c+r) R`.  With `r = 0`, the counter step `M_k`. -/
theorem rule_G (k : Nat) (hk : 1 ≤ k) : GStmt k := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro r c hc L R
    match k, r, c with
    | 1, 0, c' + 1 => exact reach_of (ruleM1 c' L R)
    | 1, r' + 1, c' + 1 => exact rule_X r' c' L R
    | i + 2, r, c' + 1 =>
      refine Reach.trans' (rule_P i c' (rep r F (cons false (cons false L))) R) ?_
      have hch := chain i 1 c' (rep (r + 1) F (cons false (cons false L))) R
        (fun j h1 h2 => mstep_of_G (ih j (by omega) h1) c' (by omega))
      refine Reach.trans' hch ?_
      have hg := ih (i + 1) (by omega) (by omega) (r + 1) c' (by omega) L R
      rw [show r + 1 + (i + 1) + 1 = r + (i + 2) + 1 by omega,
        show c' + (r + 1) = c' + 1 + r by omega] at hg
      rw [show 1 + i = i + 1 by omega]
      exact hg

/-- The counter step: `L 0 0 B> 0 1^(2k+1) 0 1^c R` reaches `L B> 0 1^(2k+3) 0 1^c R` whenever `1 ≤ k ≤ c`. -/
theorem rule_M (k c : Nat) (hk : 1 ≤ k) (hc : k ≤ c) (L R : Tape) :
    Reach ⟨cons false (cons false L), K k c R, .B⟩ ⟨L, K (k + 1) c R, .B⟩ :=
  mstep_of_G (rule_G k hk) c hc L R

end H54294
