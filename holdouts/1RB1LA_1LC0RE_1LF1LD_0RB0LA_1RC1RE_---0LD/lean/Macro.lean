import Rules

/-!
# Space Needle: the macro machine on (b, c)

`X b c` is the tape `0^∞ A>0 1^b 0 0 1^c 0^∞`.  From blank tape the machine reaches `X 3 1` (`r_init`), and from
`X b c` with `c ≥ 1`:

* `(0, c)        → (c + 2, 1)`
* `(1, c)`        halts (F reads a 0 twelve steps later),
* `(2k + 2, c)   → (5k + c + 7, 1)`
* `(2k + 3, c)   → (k, k + c + 4)`

(mxdys's rules).  Every rule is proved for all values of the parameters, from the shift rules of `Rules.lean` and
three inductions: the bouncer (`bounce`), the zig-zag (`zigs`) and the shift of a block (`shifts`).  So the machine
halts from blank tape exactly when the orbit of (3, 1) under `g` reaches b = 1 (`halts_iff`).
-/

namespace H101957

open TM

/-- `c'` is reachable from `c` in some number of steps. -/
def Reach (c c' : Config) : Prop := ∃ n, steps n c = some c'

/-- `c'` is reachable from `c` in at least one step. -/
def Reach1 (c c' : Config) : Prop := ∃ n, steps (n + 1) c = some c'

theorem reach_refl (c : Config) : Reach c c := ⟨0, rfl⟩

theorem reach_trans {a b c : Config} : Reach a b → Reach b c → Reach a c
  | ⟨n, h⟩, ⟨m, h'⟩ => ⟨n + m, steps_seq trans h h'⟩

theorem reach1_trans {a b c : Config} : Reach1 a b → Reach b c → Reach1 a c
  | ⟨n, h⟩, ⟨m, h'⟩ => ⟨n + m, by
      have := steps_seq trans h h'
      rw [show n + 1 + m = n + m + 1 by omega] at this
      exact this⟩

theorem reach_of_reach1 {a b : Config} : Reach1 a b → Reach a b
  | ⟨n, h⟩ => ⟨n + 1, h⟩

theorem reach1_of {n : Nat} {a b : Config} (hn : 0 < n) (h : steps n a = some b) : Reach1 a b :=
  ⟨n - 1, by rw [Nat.sub_add_cancel hn]; exact h⟩

abbrev T : List Bool := [true]

theorem repT_cons (n : Nat) (s : Tape) : rep n T (cons true s) = rep (n + 1) T s := rep_app_comm n [true] s

theorem repT_rep (a b : Nat) (s : Tape) : rep a T (rep b T s) = rep (a + b) T s := (rep_add a b T s).symm

/-! ## The three inductions -/

/-- The bouncer: `L 0 1^(2j+m+1) C>0 R` becomes `L 1^j 0 1^(m+1) C>0 1^j R`. -/
theorem bounce (j : Nat) : ∀ (m : Nat) (L R : Tape),
    Reach ⟨rep (2 * j + m + 1) T (cons false L), cons false R, .C⟩
      ⟨rep (m + 1) T (cons false (rep j T L)), cons false (rep j T R), .C⟩ := by
  induction j with
  | zero => intro m L R; simpa using reach_refl _
  | succ j ih =>
    intro m L R
    have h2 := ih m (cons true L) (cons true R)
    rw [repT_cons, repT_cons] at h2
    rw [show 2 * (j + 1) + m + 1 = 2 * j + m + 3 by omega]
    exact reach_trans ⟨_, r_cyc (2 * j + m) L R⟩ h2

theorem zigstep (k : Nat) (L R : Tape) :
    Reach ⟨L, cons false (rep (k + 1) T (cons false (cons true R))), .A⟩
      ⟨cons true L, cons false (rep k T (cons false (cons true R))), .A⟩ := by
  cases k with
  | zero => exact ⟨_, r_zig0 L R⟩
  | succ k => exact ⟨_, r_zig k L R⟩

/-- The zig-zag: `L A>0 1^(j+r) 0 1 R` becomes `L 1^j A>0 1^r 0 1 R`. -/
theorem zigs (j : Nat) : ∀ (r : Nat) (L R : Tape),
    Reach ⟨L, cons false (rep (j + r) T (cons false (cons true R))), .A⟩
      ⟨rep j T L, cons false (rep r T (cons false (cons true R))), .A⟩ := by
  induction j with
  | zero => intro r L R; simpa using reach_refl _
  | succ j ih =>
    intro r L R
    have h2 := ih r (cons true L) R
    rw [repT_cons] at h2
    rw [show j + 1 + r = (j + r) + 1 by omega]
    exact reach_trans (zigstep (j + r) L R) h2

theorem sendstep (k : Nat) (R : Tape) :
    Reach ⟨rep (k + 1) T blank, cons false (cons false (cons true R)), .A⟩
      ⟨blank, cons false (rep k T (cons false (cons true (cons true (cons true R))))), .A⟩ := by
  cases k with
  | zero => exact ⟨_, r_send0 R⟩
  | succ k => exact ⟨_, r_send k R⟩

/-- One shift: `0^∞ A>0 1^(a+1) 0 1^(b+1) R` becomes `0^∞ A>0 1^a 0 1^(b+3) R`, one cell further left. -/
theorem scycle (a b : Nat) (R : Tape) :
    Reach ⟨blank, cons false (rep (a + 1) T (cons false (rep (b + 1) T R))), .A⟩
      ⟨blank, cons false (rep a T (cons false (rep (b + 3) T R))), .A⟩ :=
  reach_trans (zigs (a + 1) 0 blank (rep b T R)) (sendstep a (rep b T R))

/-- `a` shifts: `0^∞ A>0 1^a 0 1^(b+1) R` becomes `0^∞ A>0 0 1^(2a+b+1) R`. -/
theorem shifts (a : Nat) : ∀ (b : Nat) (R : Tape),
    Reach ⟨blank, cons false (rep a T (cons false (rep (b + 1) T R))), .A⟩
      ⟨blank, cons false (cons false (rep (2 * a + b + 1) T R)), .A⟩ := by
  induction a with
  | zero => intro b R; simpa using reach_refl _
  | succ a ih =>
    intro b R
    have h2 := ih (b + 2) R
    rw [show 2 * a + (b + 2) + 1 = 2 * (a + 1) + b + 1 by omega] at h2
    exact reach_trans (scycle a b R) h2

/-! ## The macro rules -/

/-- `0^∞ A>0 1^b 0 0 1^c 0^∞`. -/
def X (b c : Nat) : Config := ⟨blank, cons false (rep b T (cons false (cons false (rep c T blank)))), .A⟩

theorem init_X : steps 45 init = some (X 3 1) := by
  have h := r_init
  rw [cons_false_blank] at h
  exact h

theorem even_rule (k c : Nat) : Reach1 (X (2 * k + 2) c) (X (5 * k + c + 7) 1) := by
  have h1 : Reach1 (X (2 * k + 2) c)
      ⟨rep (2 * k + 1 + 1) T (cons false (cons true blank)), cons false (rep c T blank), .C⟩ :=
    reach1_of (by omega) (r_start (2 * k + 1) (rep c T blank))
  have h2 := bounce k 1 (cons true blank) (rep c T blank)
  rw [repT_cons, repT_rep] at h2
  -- after the bouncer: 0^∞ 1^(k+1) 0 1 1 C>0 1^(k+c)
  have h3 : Reach ⟨rep (1 + 1) T (cons false (rep (k + 1) T blank)), cons false (rep (k + c) T blank), .C⟩
      ⟨blank, cons false (rep k T (cons false (rep (1 + 1) T (cons false (rep (k + c + 1) T blank))))), .A⟩ := by
    cases k with
    | zero =>
      have e := r_endE0 (rep c T blank)
      simp only [Nat.zero_add]
      exact ⟨_, e⟩
    | succ k =>
      have e := r_endE k (rep (k + 1 + c) T blank)
      rw [show k + 1 + c + 1 = (k + 1 + c) + 1 by omega]
      exact ⟨_, e⟩
  have h4 := shifts k 1 (cons false (rep (k + c + 1) T blank))
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at h4
  have h5 : Reach ⟨blank, cons false (cons false (rep (2 * k + 2) T (cons false (rep (k + c + 1) T blank)))), .A⟩
      ⟨blank, cons false (rep (2 * k + 3) T (cons false (rep (k + c + 1) T blank))), .A⟩ := by
    have e := r_dmid (2 * k + 1) (rep (k + c) T blank)
    rw [cons_false_blank] at e
    exact ⟨_, e⟩
  have h6 := shifts (2 * k + 3) (k + c) blank
  have h7 : Reach ⟨blank, cons false (cons false (rep (2 * (2 * k + 3) + (k + c) + 1) T blank)), .A⟩
      (X (5 * k + c + 7) 1) := by
    have e := r_dend (5 * k + c + 5)
    rw [cons_false_blank] at e
    rw [show 2 * (2 * k + 3) + (k + c) + 1 = 5 * k + c + 5 + 2 by omega]
    exact ⟨_, e⟩
  exact reach1_trans h1 (reach_trans h2 (reach_trans h3 (reach_trans h4 (reach_trans h5 (reach_trans h6 h7)))))

theorem odd_rule (k c : Nat) : Reach1 (X (2 * k + 3) c) (X k (k + c + 4)) := by
  have h1 : Reach1 (X (2 * k + 3) c)
      ⟨rep (2 * k + 2 + 1) T (cons false (cons true blank)), cons false (rep c T blank), .C⟩ :=
    reach1_of (by omega) (r_start (2 * k + 2) (rep c T blank))
  have h2 := bounce (k + 1) 0 (cons true blank) (rep c T blank)
  rw [repT_cons, repT_rep, show 2 * (k + 1) + 0 + 1 = 2 * k + 2 + 1 by omega] at h2
  have h3 : Reach ⟨rep (0 + 1) T (cons false (rep (k + 1 + 1) T blank)), cons false (rep (k + 1 + c) T blank), .C⟩
      (X k (k + c + 4)) := by
    cases k with
    | zero =>
      have e := r_endO0 (rep (0 + 1 + c) T blank)
      rw [show 0 + c + 4 = (0 + 1 + c) + 3 by omega]
      exact ⟨_, e⟩
    | succ k =>
      have e := r_endO k (rep (k + 1 + 1 + c) T blank)
      rw [show k + 1 + c + 4 = (k + 1 + 1 + c) + 3 by omega]
      exact ⟨_, e⟩
  exact reach1_trans h1 (reach_trans h2 h3)

theorem zero_rule (c : Nat) : Reach1 (X 0 (c + 1)) (X (c + 3) 1) := by
  have h1 : Reach1 (X 0 (c + 1)) ⟨blank, cons false (cons false (rep (c + 1 + 2) T blank)), .A⟩ :=
    reach1_of (by omega) (r_zero c)
  have e := r_dend (c + 1)
  rw [cons_false_blank] at e
  exact reach1_trans h1 ⟨_, e⟩

/-- `(1, c)` halts: twelve steps later F reads a 0. -/
theorem halt_rule (c : Nat) : ∃ n c', steps n (X 1 c) = some c' ∧ step c' = none :=
  ⟨12, _, r_halt (rep c T blank), rfl⟩

/-! ## The map -/

/-- mxdys's map on (b, c); `(1, c)` is the halting configuration and is left fixed. -/
def g : Nat × Nat → Nat × Nat
  | (0, c) => (c + 2, 1)
  | (1, c) => (1, c)
  | (b + 2, c) => if b % 2 = 0 then (5 * (b / 2) + c + 7, 1) else (b / 2, b / 2 + c + 4)

theorem g_zero (c : Nat) : g (0, c) = (c + 2, 1) := rfl

theorem g_even (k c : Nat) : g (2 * k + 2, c) = (5 * k + c + 7, 1) := by
  simp only [g]; rw [if_pos (by omega), show 2 * k / 2 = k by omega]

theorem g_odd (k c : Nat) : g (2 * k + 1 + 2, c) = (k, k + c + 4) := by
  simp only [g]; rw [if_neg (by omega), show (2 * k + 1) / 2 = k by omega]

theorem g_step (b c : Nat) (hb : b ≠ 1) (hc : 1 ≤ c) :
    Reach1 (X b c) (X (g (b, c)).1 (g (b, c)).2) ∧ 1 ≤ (g (b, c)).2 := by
  match b, hb with
  | 0, _ =>
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    refine ⟨?_, by simp [g]⟩
    simpa [g, show c' + 1 + 2 = c' + 3 by omega] using zero_rule c'
  | b + 2, _ =>
    rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
    · obtain ⟨k, rfl⟩ : ∃ k, b = 2 * k := ⟨b / 2, by omega⟩
      rw [g_even]
      exact ⟨even_rule k c, Nat.le_refl _⟩
    · obtain ⟨k, rfl⟩ : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
      rw [g_odd]
      refine ⟨?_, by omega⟩
      rw [show 2 * k + 1 + 2 = 2 * k + 3 by omega]
      exact odd_rule k c

/-- The orbit of (3, 1). -/
def orbit : Nat → Nat × Nat
  | 0 => (3, 1)
  | n + 1 => g (orbit n)

theorem orbit_succ (n : Nat) : orbit (n + 1) = g (orbit n) := rfl

theorem exists_min (P : Nat → Prop) : ∀ n, P n → ∃ n0, P n0 ∧ ∀ i < n0, ¬ P i := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h : ∃ i < n, P i
    · obtain ⟨i, hi, hpi⟩ := h
      exact ih i hi hpi
    · exact ⟨n, hn, fun i hi hpi => h ⟨i, hi, hpi⟩⟩

theorem orbit_reach (n : Nat) (h : ∀ i < n, (orbit i).1 ≠ 1) :
    ∃ m, n ≤ m ∧ steps m init = some (X (orbit n).1 (orbit n).2) ∧ 1 ≤ (orbit n).2 := by
  induction n with
  | zero => exact ⟨45, by omega, init_X, by simp [orbit]⟩
  | succ n ih =>
    obtain ⟨m, hm, hs, hc⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨⟨k, hk⟩, hc'⟩ := g_step _ _ (h n (by omega)) hc
    refine ⟨m + (k + 1), by omega, ?_, ?_⟩
    · rw [orbit_succ]; exact steps_seq trans hs hk
    · rw [orbit_succ]; exact hc'

/-- **The reduction.** Space Needle halts from blank tape exactly when the orbit of (3, 1) under `g` reaches a
configuration with b = 1. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, (orbit n).1 = 1 := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hno => ?_
    have hall : ∀ n, (orbit n).1 ≠ 1 := fun n hn => hno ⟨n, hn⟩
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun m => ∃ c', steps m init = some c')
    · intro n
      obtain ⟨m, hm, hs, _⟩ := orbit_reach n (fun i _ => hall i)
      exact ⟨m, hm, _, hs⟩
    · intro m hm; exact hm
  · rintro ⟨n, hn⟩
    obtain ⟨n0, h0, hmin⟩ := exists_min (fun n => (orbit n).1 = 1) n hn
    obtain ⟨m, _, hs, _⟩ := orbit_reach n0 hmin
    obtain ⟨k, c', hk, hstep⟩ := halt_rule (orbit n0).2
    rw [h0] at hs
    exact ⟨m + k, c', steps_seq trans hs hk, hstep⟩

end H101957
