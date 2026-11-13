import Rules

/-!
# 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE halts if and only if a Collatz-like orbit hits zero

The rules of `Rules.lean` (one pass each, proved by `bbtools.symtm`) are chained here by induction into whole
phases, and the phases into one round of the machine:

* `X K m` is the machine in state D at the left end of the tape `(10)^K 1^m` (blank beyond);
* a *doubling* takes `X K m` to `X (2K+4) (m-2K-6)` when `m ≥ 2K+6` (`double`);
* when `m` is even with `2 ≤ m < 2K+6` the round ends at `X 1 (2K+3m+2)` (`finish`);
* when `m = 0` the machine halts (`halt_zero`).

`phase K m` is that map as a function (`none` for a halt), `next N = phase 1 N`, and the run from blank tape reaches
`X 1 22` after 208 steps.  So the machine halts from blank tape if and only if the orbit of 22 under `next` reaches
`none` (`halts_iff`).  Nothing here says whether it does: that is the open question, now about a map on numbers.
-/

namespace H167198

open TM

/-- `c` reaches `c'` in at least one step. -/
def Reaches (c c' : Config) : Prop := ∃ n, 0 < n ∧ steps n c = some c'

theorem Reaches.tr {a b c : Config} (h₁ : Reaches a b) (h₂ : Reaches b c) : Reaches a c := by
  obtain ⟨n, hn, h⟩ := h₁
  obtain ⟨m, hm, h'⟩ := h₂
  exact ⟨n + m, by omega, steps_seq trans h h'⟩

theorem reaches_of {n : Nat} {c c' : Config} (h : steps n c = some c') (hn : 0 < n) : Reaches c c' := ⟨n, hn, h⟩

/-- State D at the left end of `(10)^K 1^m`. -/
def X (K m : Nat) : Config := ⟨blank, rep K [true, false] (rep m [true] blank), .D⟩

/-- State D at the left end of `0 0 (10)^x 1^y`. -/
def Y (x y : Nat) : Config := ⟨blank, cons false (cons false (rep x [true, false] (rep y [true] blank))), .D⟩

/-- `1 (01)^b 0` is `(10)^(b+1)`. -/
theorem rot10 (b : Nat) (S : Tape) :
    cons true (rep b [false, true] (cons false S)) = rep (b + 1) [true, false] S := by
  have h := rep_rotate b [true] [false, true] [true, false] rfl (cons false S)
  simp only [app] at h
  rw [h]
  exact rep_app_comm b [true, false] S

/-- The left part `1 (10)^k` written nearest first. -/
theorem rot01 (k : Nat) : rep k [false, true] (cons false (cons true blank)) = rep (k + 1) [false, true] blank :=
  rep_app_comm k [false, true] blank

/-- `(11)^b 1` is `1^(2b+1)`. -/
theorem ones2 (b : Nat) (S : Tape) : rep b [true, true] S = rep (2 * b) [true] S := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [show 2 * (b + 1) = (2 * b) + 1 + 1 by omega, rep_succ, ih]
    show cons true (cons true _) = app [true] (app [true] (rep (2 * b) [true] S))
    rfl

theorem ones_succ (n : Nat) (S : Tape) : rep n [true] (cons true S) = rep (n + 1) [true] S :=
  rep_app_comm n [true] S

/-- The zigzag of a doubling, `j` times. -/
theorem inner_iter (j : Nat) : ∀ (a b c : Nat) (L R : Tape),
    ∃ n, steps n ⟨cons true (rep (a + j) [false, true] L),
        cons false (cons false (rep b [true, false] (rep (c + 2 * j) [true] R))), .A⟩ =
      some ⟨cons true (rep a [false, true] L), cons false (cons false (rep (b + 2 * j) [true, false] (rep c [true] R))), .A⟩ := by
  induction j with
  | zero => intro a b c L R; exact ⟨0, rfl⟩
  | succ j ih =>
    intro a b c L R
    have h1 := inner (a + j) b (c + 2 * j) L R
    rw [rot10] at h1
    have h1' : steps (4 * b + 8) ⟨cons true (rep (a + (j + 1)) [false, true] L),
        cons false (cons false (rep b [true, false] (rep (c + 2 * (j + 1)) [true] R))), .A⟩ =
        some ⟨cons true (rep (a + j) [false, true] L),
          cons false (cons false (cons true (cons false (rep (b + 1) [true, false] (rep (c + 2 * j) [true] R))))), .A⟩ := by
      rw [show a + (j + 1) = a + j + 1 by omega, show c + 2 * (j + 1) = c + 2 * j + 2 by omega]
      exact h1
    obtain ⟨n2, h2⟩ := ih a (b + 2) c L R
    have e : (rep (b + 2) [true, false] (rep (c + 2 * j) [true] R)) =
        cons true (cons false (rep (b + 1) [true, false] (rep (c + 2 * j) [true] R))) := rfl
    rw [e, show b + 2 + 2 * j = b + 2 * (j + 1) by omega] at h2
    exact ⟨_, steps_seq trans h1' h2⟩

/-- A doubling: `(10)^(K+1) 1^(c+2K+8)` becomes `(10)^(2K+6) 1^c`. -/
theorem double (K c : Nat) : Reaches (X (K + 1) (c + 2 * K + 8)) (X (2 * K + 6) c) := by
  have h1 := dstart (c + 2 * K + 6) K blank
  rw [rot01, show c + 2 * K + 6 + 2 = c + 2 * K + 8 by omega] at h1
  obtain ⟨n2, h2⟩ := inner_iter (K + 1) 0 0 (c + 4) blank blank
  rw [show 0 + (K + 1) = K + 1 by omega, show c + 4 + 2 * (K + 1) = c + 2 * K + 6 by omega,
    show 0 + 2 * (K + 1) = 2 * K + 2 by omega] at h2
  have h3 := dend (2 * K + 2) c blank
  have e3 : cons true (cons false (cons true (cons false (cons true (cons false
      (rep (2 * K + 2) [true, false] (cons true (cons false (rep c [true] blank))))))))) =
      rep (2 * K + 6) [true, false] (rep c [true] blank) := by
    have := rep_app_comm (2 * K + 2) [true, false] (rep c [true] blank)
    simp only [app] at this
    rw [this]; rfl
  rw [e3] at h3
  have h12 := steps_seq trans h1 h2
  have h123 := steps_seq trans h12 h3
  exact reaches_of h123 (by omega)

/-- A halt: `(10)^K` with no 1s, `K ≥ 1`. -/
theorem halt_zero (k : Nat) : Halts trans (X (k + 1) 0) := by
  refine ⟨2 * k + 4, _, tohalt k, ?_⟩
  rfl

/-- `0 0 (10)^x 1^(y+2j)` becomes `0 0 (10)^(x+2j) 1^y`. -/
theorem transfer_iter (j : Nat) : ∀ x y : Nat, ∃ n, steps n (Y x (y + 2 * j)) = some (Y (x + 2 * j) y) := by
  induction j with
  | zero => intro x y; exact ⟨0, rfl⟩
  | succ j ih =>
    intro x y
    have h1 := transfer x (y + 2 * j) blank
    rw [rot10] at h1
    have e : rep (x + 2) [true, false] (rep (y + 2 * j) [true] blank) =
        cons true (cons false (rep (x + 1) [true, false] (rep (y + 2 * j) [true] blank))) := rfl
    obtain ⟨n, hn⟩ := ih (x + 2) y
    refine ⟨4 * x + 10 + n, ?_⟩
    have h1' : steps (4 * x + 10) (Y x (y + 2 * (j + 1))) = some (Y (x + 2) (y + 2 * j)) := by
      unfold Y
      rw [show y + 2 * (j + 1) = y + 2 * j + 2 by omega, e]
      exact h1
    rw [show x + 2 * (j + 1) = x + 2 + 2 * j by omega]
    exact steps_seq trans h1' hn

/-- The end of a round: `0 0 (10)^x 1` unfolds to `10 1^(2x+6)`. -/
theorem final' (x : Nat) : Reaches (Y x 1) (X 1 (2 * x + 6)) := by
  have h := final x
  have e : cons true (cons false (cons true (cons true (cons true (cons true
      (rep x [true, true] (cons true (cons true blank)))))))) = rep 1 [true, false] (rep (2 * x + 6) [true] blank) := by
    rw [ones2, ones_succ, ones_succ]
    show _ = cons true (cons false (rep (2 * x + 6) [true] blank))
    rw [show 2 * x + 6 = (2 * x + 1 + 1) + 1 + 1 + 1 + 1 by omega]
    rfl
  rw [e] at h
  exact reaches_of h (by omega)

/-- The remainder of a doubling phase: `(10)^(k+1) 1^(2i+2)` with `i ≤ k+2` ends at `0 0 (10)^(k+2-i) 1^(4i+1)`. -/
theorem remainder (k i : Nat) (hi : i ≤ k + 2) : Reaches (X (k + 1) (2 * i + 2)) (Y (k + 2 - i) (4 * i + 1)) := by
  have h1 := dstart (2 * i) k blank
  rw [rot01] at h1
  -- h1 : X (k+1) (2i+2) reaches  left (10)^(k+1) 1,  right 0 0 1^(2i)
  have hX : X (k + 1) (2 * i + 2) = ⟨blank, rep (k + 1) [true, false] (rep (2 * i + 2) [true] blank), .D⟩ := rfl
  by_cases hik : i ≤ k
  · -- the 1s run out first: i zigzags, then p2a with k+1-i pairs on the left
    -- left after h1 is cons true (rep (k+1) ...); inner_iter needs a + i = k + 1 with a = k + 1 - i
    obtain ⟨n2, h2'⟩ := inner_iter i (k + 1 - i) 0 0 blank blank
    rw [show k + 1 - i + i = k + 1 by omega, show 0 + 2 * i = 2 * i by omega] at h2'
    have h3 := p2a (k - i) (2 * i)
    rw [show k - i + 1 = k + 1 - i by omega] at h3
    have e3 : cons false (cons false (cons true (rep (k + 1 - i) [false, true] (cons false
        (rep (2 * i) [true, true] (cons true blank)))))) =
        cons false (cons false (rep (k + 2 - i) [true, false] (rep (4 * i + 1) [true] blank))) := by
      rw [rot10, ones2, ones_succ, show k + 1 - i + 1 = k + 2 - i by omega, show 2 * (2 * i) + 1 = 4 * i + 1 by omega]
    rw [e3] at h3
    have h12 := steps_seq trans h1 h2'
    have h123 := steps_seq trans h12 h3
    exact reaches_of h123 (by omega)
  · by_cases hik1 : i = k + 1
    · -- the 1s and the left pairs run out together: p2b
      subst hik1
      obtain ⟨n2, h2⟩ := inner_iter (k + 1) 0 0 0 blank blank
      rw [show 0 + (k + 1) = k + 1 by omega, show 0 + 2 * (k + 1) = 2 * (k + 1) by omega] at h2
      have h3 := p2b (2 * (k + 1))
      have e3 : cons false (cons false (cons true (cons false (rep (2 * (k + 1)) [true, true] (cons true blank))))) =
          cons false (cons false (rep (k + 2 - (k + 1)) [true, false] (rep (4 * (k + 1) + 1) [true] blank))) := by
        rw [ones2, ones_succ, show k + 2 - (k + 1) = 1 by omega, show 2 * (2 * (k + 1)) + 1 = 4 * (k + 1) + 1 by omega]
        rfl
      rw [e3] at h3
      have h12 := steps_seq trans h1 h2
      have h123 := steps_seq trans h12 h3
      exact reaches_of h123 (by omega)
    · -- two 1s are left when the left pairs run out: p2c
      have hik2 : i = k + 2 := by omega
      subst hik2
      obtain ⟨n2, h2⟩ := inner_iter (k + 1) 0 0 2 blank blank
      rw [show 0 + (k + 1) = k + 1 by omega, show 2 + 2 * (k + 1) = 2 * (k + 2) by omega] at h2
      have h3 := p2c (2 * (k + 1))
      have e2 : rep (2 * (k + 1)) [true, false] (rep 2 [true] blank) =
          rep (2 * (k + 1)) [true, false] (cons true (cons true blank)) := rfl
      rw [show 0 + 2 * (k + 1) = 2 * (k + 1) by omega, e2] at h2
      have e3 : cons false (cons false (cons true (cons true (cons true (cons true
          (rep (2 * (k + 1)) [true, true] (cons true blank))))))) =
          cons false (cons false (rep (k + 2 - (k + 2)) [true, false] (rep (4 * (k + 2) + 1) [true] blank))) := by
        rw [ones2, ones_succ, show k + 2 - (k + 2) = 0 by omega,
          show 4 * (k + 2) + 1 = (2 * (2 * (k + 1)) + 1) + 1 + 1 + 1 + 1 by omega]
        rfl
      rw [e3] at h3
      have h12 := steps_seq trans h1 h2
      have h123 := steps_seq trans h12 h3
      exact reaches_of h123 (by omega)

/-- The whole end of a round: `(10)^K 1^m`, `K ≥ 1`, `m` even, `2 ≤ m < 2K+6`, reaches `10 1^(2K+3m+2)`. -/
theorem finish (K m : Nat) (hK : 1 ≤ K) (hm : m % 2 = 0) (h2 : 2 ≤ m) (h3 : m < 2 * K + 6) :
    Reaches (X K m) (X 1 (2 * K + 3 * m + 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = 2 * i + 2 := ⟨(m - 2) / 2, by omega⟩
  have h1 := remainder k i (by omega)
  obtain ⟨n, hn⟩ := transfer_iter (2 * i) (k + 2 - i) 1
  rw [show 1 + 2 * (2 * i) = 4 * i + 1 by omega] at hn
  have h4 := final' (k + 2 - i + 2 * (2 * i))
  rw [show 2 * (k + 2 - i + 2 * (2 * i)) + 6 = 2 * (k + 1) + 3 * (2 * i + 2) + 2 by omega] at h4
  obtain ⟨a, ha, h1⟩ := h1
  exact Reaches.tr ⟨a + n, by omega, steps_seq trans h1 hn⟩ h4

/-- The map of one doubling phase: `none` is a halt, `some N` is the next round's `X 1 N`. -/
def phase (K m : Nat) : Option Nat :=
  if m = 0 then none
  else if 2 * K + 6 ≤ m then phase (2 * K + 4) (m - (2 * K + 6))
  else some (2 * K + 3 * m + 2)
termination_by m
decreasing_by omega

/-- What `phase` says, the machine does. -/
theorem phase_spec (m : Nat) : ∀ K : Nat, 1 ≤ K → m % 2 = 0 →
    (phase K m = none → Halts trans (X K m)) ∧
    (∀ N, phase K m = some N → Reaches (X K m) (X 1 N) ∧ N % 2 = 0) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro K hK hm
    by_cases h0 : m = 0
    · subst h0
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      refine ⟨fun _ => halt_zero k, fun N hN => ?_⟩
      rw [phase] at hN; simp at hN
    · by_cases hb : 2 * K + 6 ≤ m
      · have hp : phase K m = phase (2 * K + 4) (m - (2 * K + 6)) := by
          rw [phase]; simp [h0, hb]
        obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
        have hd := double k (m - (2 * (k + 1) + 6))
        rw [show m - (2 * (k + 1) + 6) + 2 * k + 8 = m by omega,
          show 2 * k + 6 = 2 * (k + 1) + 4 by omega] at hd
        have ih' := ih (m - (2 * (k + 1) + 6)) (by omega) (2 * (k + 1) + 4) (by omega) (by omega)
        rw [hp]
        refine ⟨fun h => ?_, fun N h => ?_⟩
        · obtain ⟨n, -, hn⟩ := hd
          obtain ⟨n', c', h1, h2⟩ := ih'.1 h
          exact ⟨n + n', c', steps_seq trans hn h1, h2⟩
        · obtain ⟨hr, he⟩ := ih'.2 N h
          exact ⟨Reaches.tr hd hr, he⟩
      · have hp : phase K m = some (2 * K + 3 * m + 2) := by
          rw [phase]; simp [h0, hb]
        rw [hp]
        refine ⟨fun h => (by cases h), fun N h => ?_⟩
        cases h
        exact ⟨finish K m hK hm (by omega) (by omega), by omega⟩

/-- One round: from `10 1^N` to `10 1^(next N)`. -/
def next (N : Nat) : Option Nat := phase 1 N

/-- The orbit of 22: `orbit i` is the value after `i` rounds, `none` once a round has halted. -/
def orbit : Nat → Option Nat
  | 0 => some 22
  | i + 1 => (orbit i).bind next

/-- From blank tape the machine reaches `10 1^22` in state D after 208 steps. -/
theorem blank_to_X22 : steps 208 init = some (X 1 22) := by
  have h := blank_reaches trans (n := 208) (q := St.A) (c := ⟨[], true :: false :: List.replicate 22 true, .D⟩)
    (by decide +kernel)
  exact h.trans rfl

theorem orbit_reach : ∀ i N, orbit i = some N → N % 2 = 0 ∧ ∃ n, i ≤ n ∧ steps n init = some (X 1 N) := by
  intro i
  induction i with
  | zero => intro N h; cases h; exact ⟨rfl, 208, by omega, blank_to_X22⟩
  | succ i ih =>
    intro N h
    simp only [orbit] at h
    cases hi : orbit i with
    | none => rw [hi] at h; cases h
    | some M =>
      rw [hi] at h
      obtain ⟨hM, n, hn, hs⟩ := ih M hi
      obtain ⟨hr, hN⟩ := (phase_spec M 1 (Nat.le_refl 1) hM).2 N h
      obtain ⟨n', hn', hs'⟩ := hr
      exact ⟨hN, n + n', by omega, steps_seq trans hs hs'⟩

/-- **The reduction.** The machine halts from blank tape if and only if the orbit of 22 under `next` reaches `none`,
that is, some doubling phase starts with no 1s left. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ i, orbit i = none := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno0
    have hno : ∀ i, orbit i ≠ none := fun i h => hno0 ⟨i, h⟩
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun n => ∃ i N, orbit i = some N ∧ i ≤ n ∧ steps n init = some (X 1 N))
    · intro n
      cases hN : orbit n with
      | none => exact absurd hN (hno n)
      | some N =>
      obtain ⟨-, m, hm, hs⟩ := orbit_reach n N hN
      exact ⟨m, by omega, n, N, hN, hm, hs⟩
    · rintro m ⟨i, N, -, -, hs⟩
      exact ⟨_, hs⟩
  · rintro ⟨i, hi⟩
    induction i with
    | zero => cases hi
    | succ i ih =>
      simp only [orbit] at hi
      cases ho : orbit i with
      | none => exact ih ho
      | some M =>
        rw [ho] at hi
        obtain ⟨hM, n, -, hs⟩ := orbit_reach i M ho
        obtain ⟨n', c', h1, h2⟩ := (phase_spec M 1 (Nat.le_refl 1) hM).1 hi
        exact ⟨n + n', c', steps_seq trans hs h1, h2⟩

end H167198
