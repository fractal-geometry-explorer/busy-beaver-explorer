import Rules

/-!
# The general rule C of the sample map, for all parameters

Samples: `K(x, m, s)` = `0^inf 1^4 0 (10)^x 1^m C>s 0^inf` (the head in state C on the cell `s` at the right end).
Rule C of the map says: if `m = 2n+1` is odd and `x >= n+3`, then

* `K(x, 2n+1, 0)` reaches `K(x-n-3, 4n+9, 0)`, and
* `K(x, 2n+1, 1)` reaches `K(x-n-3, 4n+8, 1)`.

The run goes through the frames `Q0 i j k` / `Q1 i j k` (head in E in the middle of the tape, see below): a start
piece (`ph1_0` / `ph1_1` in `Rules.lean`), then one cycle `cyc_0` / `cyc_1` per pair `10` on the right, which moves a
`10` from the left `(10)^i` block into the ones (proved here for any number of cycles by induction), then an end piece
`fin_0` / `fin_1`.  Written by hand on top of the generated `Rules.lean`.
-/

namespace H26350

open TM

/-- `c` reaches `c'` in some number of ordinary steps. -/
def Reach (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reach.join {a b c : Config} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c :=
  let ⟨n, hn⟩ := h₁
  let ⟨m, hm⟩ := h₂
  ⟨n + m, steps_seq trans hn hm⟩

theorem reach_of {n : Nat} {c c' c'' : Config} (h : steps n c = some c') (e : c' = c'') : Reach c c'' :=
  ⟨n, e ▸ h⟩

/-- `c` reaches `c'` in at least one step. -/
def Adv (c c' : Config) : Prop := ∃ n, 0 < n ∧ steps n c = some c'

theorem adv_of {n : Nat} {c c' c'' : Config} (h : steps n c = some c') (hn : 0 < n) (e : c' = c'') : Adv c c'' :=
  ⟨n, hn, e ▸ h⟩

theorem Adv.join {a b c : Config} (h₁ : Adv a b) (h₂ : Reach b c) : Adv a c :=
  let ⟨n, hn, h⟩ := h₁
  let ⟨m, hm⟩ := h₂
  ⟨n + m, by omega, steps_seq trans h hm⟩

/-- The sample `K(x, 2n+1, s)`. -/
def Kodd (x n : Nat) (s : Bool) : Config :=
  ⟨rep n [true, true] (cons true (rep x [false, true] (cons false (rep 4 [true] blank)))), cons s blank, .C⟩

/-- The sample `K(x, 2n, s)`. -/
def Keven (x n : Nat) (s : Bool) : Config :=
  ⟨rep n [true, true] (rep x [false, true] (cons false (rep 4 [true] blank))), cons s blank, .C⟩

/-- `0^inf 1^4 0 (10)^i (11)^j E>1 1 1 0 (10)^k 1 1 0 0^inf`. -/
def Q0 (i j k : Nat) : Config :=
  ⟨rep j [true, true] (rep i [false, true] (cons false (rep 4 [true] blank))),
   cons true (cons true (cons true (cons false (rep k [true, false] (cons true (cons true (cons false blank))))))),
   .E⟩

/-- `0^inf 1^4 0 (10)^i (11)^j E>1 1 1 0 (10)^k 0^inf`. -/
def Q1 (i j k : Nat) : Config :=
  ⟨rep j [true, true] (rep i [false, true] (cons false (rep 4 [true] blank))),
   cons true (cons true (cons true (cons false (rep k [true, false] blank)))), .E⟩

theorem ones_rot (n : Nat) (Z : Tape) : cons true (rep n [true, true] Z) = rep n [true, true] (cons true Z) :=
  rep_rotate n [true] [true, true] [true, true] rfl Z

theorem two_in (j : Nat) (Z : Tape) :
    cons true (cons true (rep j [true, true] (cons true (cons true Z)))) = rep (j + 2) [true, true] Z :=
  congrArg (app [true, true]) (rep_app_comm j [true, true] Z)

theorem four_in (j : Nat) (Y : Tape) :
    cons true (cons true (cons true (cons true (cons true (rep j [true, true]
      (cons true (cons true (cons true (cons true Y))))))))) = rep (j + 4) [true, true] (cons true Y) := by
  have a : rep j [true, true] (cons true (cons true (cons true (cons true Y)))) = rep (j + 2) [true, true] Y :=
    (rep_app_comm j [true, true] (app [true, true] Y)).trans (rep_app_comm (j + 1) [true, true] Y)
  rw [a]
  exact congrArg (fun T => cons true (cons true (cons true (cons true T)))) (ones_rot (j + 2) Y)

theorem cyc0 (i j k : Nat) : Reach (Q0 (i + 1) j (k + 1)) (Q0 i (j + 2) k) :=
  reach_of (cyc_0 i j k) (by unfold Q0; rw [two_in]; rfl)

theorem cyc1 (i j k : Nat) : Reach (Q1 (i + 1) j (k + 1)) (Q1 i (j + 2) k) :=
  reach_of (cyc_1 i j k) (by unfold Q1; rw [two_in]; rfl)

/-- `t` cycles at once (s = 0). -/
theorem cycN0 (t : Nat) : ∀ i j k, Reach (Q0 (i + t) j (k + t)) (Q0 i (j + 2 * t) k) := by
  induction t with
  | zero => intro i j k; exact ⟨0, rfl⟩
  | succ t ih =>
    intro i j k
    have h := ih i (j + 2) k
    rw [show j + 2 + 2 * t = j + 2 * (t + 1) by omega] at h
    exact (cyc0 (i + t) j (k + t)).join h

/-- `t` cycles at once (s = 1). -/
theorem cycN1 (t : Nat) : ∀ i j k, Reach (Q1 (i + t) j (k + t)) (Q1 i (j + 2 * t) k) := by
  induction t with
  | zero => intro i j k; exact ⟨0, rfl⟩
  | succ t ih =>
    intro i j k
    have h := ih i (j + 2) k
    rw [show j + 2 + 2 * t = j + 2 * (t + 1) by omega] at h
    exact (cyc1 (i + t) j (k + t)).join h

theorem e1 (n : Nat) :
    cons true (rep n [false, true] (cons true blank)) = rep n [true, false] (cons true (cons true (cons false blank))) := by
  rw [cons_false_blank]
  exact rep_rotate n [true] [false, true] [true, false] rfl _

theorem e2 (n : Nat) : cons true (rep n [false, true] blank) = rep (n + 1) [true, false] blank := by
  show app [true] (rep n [false, true] blank) = _
  rw [rep_rotate n [true] [false, true] [true, false] rfl blank, ← rep_app_comm]
  exact congrArg (rep n [true, false]) (by show cons true blank = cons true (cons false blank); rw [cons_false_blank])

/-- Rule C, head on 0: `K(i+n+3, 2n+1, 0)` reaches (in at least one step) `K(i, 4n+9, 0)`. -/
theorem ruleC0 (i n : Nat) : Adv (Kodd (i + n + 3) n false) (Kodd i (2 * n + 4) false) := by
  have a : Adv (Kodd (i + n + 3) n false) (Q0 (i + 2 + n) 0 n) :=
    adv_of (ph1_0 n (i + n + 1)) (by omega) (by
      unfold Q0
      rw [e1, show i + 2 + n = (i + n + 1) + 1 by omega]
      rfl)
  have b := cycN0 n (i + 2) 0 0
  rw [Nat.zero_add, Nat.zero_add] at b
  have hf := fin_0 i (2 * n)
  have c : Reach (Q0 (i + 2) (2 * n) 0) (Kodd i (2 * n + 4) false) := by
    refine reach_of hf ?_
    unfold Kodd
    rw [four_in, congrArg (cons false) cons_false_blank]
  exact a.join (b.join c)

/-- Rule C, head on 1: `K(i+n+3, 2n+1, 1)` reaches (in at least one step) `K(i, 4n+8, 1)`. -/
theorem ruleC1 (i n : Nat) : Adv (Kodd (i + n + 3) n true) (Keven i (2 * n + 4) true) := by
  have a : Adv (Kodd (i + n + 3) n true) (Q1 (i + 1 + (n + 1)) 0 (n + 1)) :=
    adv_of (ph1_1 n (i + n + 1)) (by omega) (by
      unfold Q1
      rw [e2, show i + 1 + (n + 1) = (i + n + 1) + 1 by omega]
      rfl)
  have b := cycN1 (n + 1) (i + 1) 0 0
  rw [Nat.zero_add, Nat.zero_add] at b
  have hf := fin_1 i (2 * (n + 1))
  have c : Reach (Q1 (i + 1) (2 * (n + 1)) 0) (Keven i (2 * n + 4) true) := by
    refine reach_of hf ?_
    unfold Keven
    rw [two_in, congrArg (cons true) cons_false_blank,
      show 2 * (n + 1) + 2 = 2 * n + 4 by omega]
  exact a.join (b.join c)

end H26350
