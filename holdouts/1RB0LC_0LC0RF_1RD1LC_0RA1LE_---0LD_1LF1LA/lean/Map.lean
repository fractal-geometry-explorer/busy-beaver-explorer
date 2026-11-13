import Rules

/-!
# 1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA halts exactly when a three-counter map reaches its halting case

Every time the head, in state D, stands at the left end of the tape, the tape reads

    X a b c  =  D> 0 0 1^a 0 1^b (01)^c        (blank beyond, on both sides).

`next` is the map from one such moment to the next (`Rules.lean` proves each case), and the run from blank tape
reaches `X 1 1 4` after 138 steps.  So the machine halts from blank tape if and only if iterating `next` from
`(1, 1, 4)` reaches its halting case `(2, b, 0)` with `b` odd (`halts_iff`).  On the states the run visits, `next`
never takes its `stuck` case (`inv`), which only lists the shapes the rules do not cover.
-/

namespace H74998

open TM

/-- The tape at the moments the head, in state D, is at the left end. -/
def X (a b c : Nat) : Config :=
  ⟨blank, cons false (cons false (rep a [true] (cons false (rep b [true] (rep c [false, true] blank))))), .D⟩

/-- What one round does. -/
inductive Res where
  | ok (a b c : Nat)
  | halt
  | stuck

/-- The map between two visits of the left end (`a ≥ 3`: the 1s move from the first block to the second, two for
three; `a = 1` or `2`: the second block becomes the first, and one or three of the `01` pairs are spent; `a = 2`
with no pair left: the pairs are refilled from half the second block, or the machine halts if that block is odd). -/
def next : Nat → Nat → Nat → Res
  | a + 4, b, c => .ok (a + 2) (b + 3) c
  | 3, b, c => .ok 1 (b + 3) c
  | 1, b + 3, c + 1 => .ok (b + 4) 4 c
  | 1, 1, c + 1 => .ok 2 4 c
  | 1, b + 3, 0 => .ok (b + 4) 3 0
  | 2, b, c + 3 => .ok (b + 6) 4 c
  | 2, b, 2 => .ok (b + 6) 3 0
  | 2, b, 1 => .ok (b + 5) 3 0
  | 2, b, 0 => if b % 2 = 0 then .ok 1 1 (b / 2 + 1) else .halt
  | _, _, _ => .stuck

theorem rep_true_snoc (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s

theorem rep_two (k : Nat) (s : Tape) : rep k [true, true] s = rep (2 * k) [true] s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, rep_succ, rep_succ, rep_succ, ih]
    rfl

theorem tail_pairs (k : Nat) :
    cons false (rep k [true, false] (cons true (cons false blank))) = rep (k + 1) [false, true] blank := by
  have h := rep_rotate k [false] [true, false] [false, true] rfl (cons true (cons false blank))
  simp only [app_cons, app_nil] at h
  rw [h]
  have e := rep_app_comm k [false, true] (cons false blank)
  simp only [app_cons, app_nil] at e
  rw [e, cons_false_blank]

/-- Each `ok` case is a run of the machine, of at least one step. -/
theorem next_ok {a b c a' b' c' : Nat} (h : next a b c = .ok a' b' c') :
    ∃ n, steps (n + 1) (X a b c) = some (X a' b' c') := by
  match a, b, c, h with
  | a + 4, b, c, h => injection h with h1 h2 h3; subst h1 h2 h3; refine ⟨4 * a + 20, ?_⟩; have r := r_big a b (rep c [false, true] blank); simp only [X, rep_succ, app_cons, app_nil] at r ⊢; refine steps_congr trans ?_ r; omega
  | 3, b, c, h => injection h with h1 h2 h3; subst h1 h2 h3; refine ⟨16, ?_⟩; have r := r_three b (rep c [false, true] blank); simp only [X, rep_succ, rep_zero, app_cons, app_nil] at r ⊢; refine steps_congr trans ?_ r; omega
  | 2, b, c + 3, h =>
    injection h with h1 h2 h3; subst h1 h2 h3; refine ⟨4 * b + 49, ?_⟩; have r := r_two3 b c; rw [rep_true_snoc] at r; simp only [X, rep_succ, rep_zero, app_cons, app_nil] at r ⊢; refine steps_congr trans ?_ r; omega
  | 2, b, 2, h =>
    injection h with h1 h2 h3; subst h1 h2 h3; refine ⟨4 * b + 49, ?_⟩; have r := r_two2 b; rw [rep_true_snoc] at r; simp only [X, rep_succ, rep_zero, app_cons, app_nil] at r ⊢; refine steps_congr trans ?_ r; omega
  | 2, b, 1, h => injection h with h1 h2 h3; subst h1 h2 h3; refine ⟨4 * b + 45, ?_⟩; have r := r_two1 b; simp only [X, rep_succ, rep_zero, app_cons, app_nil] at r ⊢; refine steps_congr trans ?_ r; omega
  | 2, b, 0, h =>
    simp only [next] at h
    split at h
    · injection h with h1 h2 h3; subst h1 h2 h3
      obtain ⟨k, rfl⟩ : ∃ k, b = 2 * k := ⟨b / 2, by omega⟩
      have r := r_two0e k
      rw [rep_two, tail_pairs] at r
      rw [show 2 * k / 2 + 1 = k + 1 by omega]
      refine ⟨8 * k + 30, ?_⟩
      simp only [X, rep_succ, rep_zero, app_cons, app_nil] at r ⊢; refine steps_congr trans ?_ r; omega
    · cases h
  | 1, b + 3, c + 1, h => injection h with h1 h2 h3; subst h1 h2 h3; refine ⟨4 * b + 33, ?_⟩; have r := r_one b c; simp only [X, rep_succ, rep_zero, app_cons, app_nil] at r ⊢; refine steps_congr trans ?_ r; omega
  | 1, b + 3, 0, h => injection h with h1 h2 h3; subst h1 h2 h3; refine ⟨4 * b + 33, ?_⟩; have r := r_one0 b; simp only [X, rep_succ, rep_zero, app_cons, app_nil] at r ⊢; refine steps_congr trans ?_ r; omega
  | 1, 1, c + 1, h => injection h with h1 h2 h3; subst h1 h2 h3; refine ⟨25, ?_⟩; have r := r_one_b1 c; simp only [X, rep_succ, rep_zero, app_cons, app_nil] at r ⊢; refine steps_congr trans ?_ r; omega
  | 1, 1, 0, h => cases h
  | 1, 2, _, h => cases h
  | 1, 0, _, h => cases h
  | 0, _, _, h => cases h

/-- The `halt` case is a halt of the machine. -/
theorem next_halt {a b c : Nat} (h : next a b c = .halt) : Halts trans (X a b c) := by
  match a, b, c, h with
  | a + 4, b, c, h => cases h
  | 3, b, c, h => cases h
  | 2, b, c + 3, h => cases h
  | 2, b, 2, h => cases h
  | 2, b, 1, h => cases h
  | 2, b, 0, h =>
    simp only [next] at h
    split at h
    · cases h
    · obtain ⟨k, rfl⟩ : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
      have r := r_two0o k
      rw [rep_two] at r
      exact ⟨_, _, r, rfl⟩
  | 1, b + 3, c + 1, h => cases h
  | 1, b + 3, 0, h => cases h
  | 1, 1, c + 1, h => cases h
  | 1, 1, 0, h => cases h
  | 1, 2, _, h => cases h
  | 1, 0, _, h => cases h
  | 0, _, _, h => cases h

/-- The run of the map from `(1, 1, 4)`. -/
def orbit : Nat → Res
  | 0 => .ok 1 1 4
  | k + 1 =>
    match orbit k with
    | .ok a b c => next a b c
    | r => r

/-- The shapes the run visits: `a ≥ 1`, and `b ≥ 3` unless `a = b = 1` and a pair is left. -/
def Good : Res → Prop
  | .ok a b c => 1 ≤ a ∧ (3 ≤ b ∨ (a = 1 ∧ b = 1 ∧ 1 ≤ c))
  | .halt => True
  | .stuck => False

theorem next_good {a b c : Nat} (h : Good (.ok a b c)) : Good (next a b c) := by
  obtain ⟨ha, hb⟩ := h
  match a, b, c, ha, hb with
  | a + 4, b, c, _, _ => simp only [next, Good]; omega
  | 3, b, c, _, _ => simp only [next, Good]; omega
  | 2, b, c + 3, _, _ => simp only [next, Good]; omega
  | 2, b, 2, _, _ => simp only [next, Good]; omega
  | 2, b, 1, _, _ => simp only [next, Good]; omega
  | 2, b, 0, _, _ =>
    simp only [next]
    split
    · simp [Good]
    · trivial
  | 1, b + 3, c + 1, _, _ => simp only [next, Good]; omega
  | 1, b + 3, 0, _, _ => simp only [next, Good]; omega
  | 1, 1, c + 1, _, _ => simp only [next, Good]; omega
  | 1, 1, 0, _, hb => omega
  | 1, 2, _, _, hb => omega
  | 1, 0, _, _, hb => omega
  | 0, _, _, ha, _ => omega

theorem orbit_succ (k : Nat) : orbit (k + 1) =
    (match orbit k with | .ok a b c => next a b c | r => r) := rfl

theorem orbit_good (k : Nat) : Good (orbit k) := by
  induction k with
  | zero => simp [orbit, Good]
  | succ k ih =>
    rw [orbit_succ]
    cases e : orbit k with
    | ok a b c => rw [e] at ih; exact next_good ih
    | halt => trivial
    | stuck => rw [e] at ih; exact ih.elim

/-- The run from blank tape reaches `X 1 1 4` after 138 steps. -/
theorem init_X : steps 138 init = some (X 1 1 4) := by
  have h := blank_reaches trans (n := 138) (q := St.A)
    (c := ⟨[], [false, false, true, false, true, false, true, false, true, false, true, false, true, false], .D⟩)
    (by decide +kernel)
  show TM.steps trans 138 (blankCfg St.A) = _
  rw [h]
  simp only [FCfg.toCfg, X, app, rep, cons_false_blank]

/-- While the orbit is `ok`, the machine follows it: the k-th state is reached after at least k steps. -/
theorem orbit_run (k : Nat) : ∀ a b c, orbit k = .ok a b c → ∃ n, k ≤ n ∧ steps n init = some (X a b c) := by
  induction k with
  | zero => intro a b c h; simp [orbit] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨138, by omega, init_X⟩
  | succ k ih =>
    intro a b c h
    rw [orbit_succ] at h
    cases e : orbit k with
    | ok a0 b0 c0 =>
      rw [e] at h
      obtain ⟨n, hn, hs⟩ := ih a0 b0 c0 e
      obtain ⟨m, hm⟩ := next_ok h
      exact ⟨n + (m + 1), by omega, steps_seq trans hs hm⟩
    | halt => rw [e] at h; cases h
    | stuck => rw [e] at h; cases h

/-- **The machine halts from blank tape if and only if the orbit of `(1, 1, 4)` under `next` reaches `halt`.** -/
theorem halts_iff : HaltsFromBlank ↔ ∃ k, orbit k = .halt := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hno => ?_
    have hok : ∀ k, ∃ a b c, orbit k = .ok a b c := by
      intro k
      have g := orbit_good k
      cases e : orbit k with
      | ok a b c => exact ⟨a, b, c, rfl⟩
      | halt => exact absurd ⟨k, e⟩ hno
      | stuck => rw [e] at g; exact g.elim
    apply not_halts_of_forall trans (c := init) _ hh
    apply forall_of_unbounded trans (fun m => ∃ a b c, steps m init = some (X a b c))
    · intro n
      obtain ⟨a, b, c, e⟩ := hok n
      obtain ⟨m, hm, hs⟩ := orbit_run n a b c e
      exact ⟨m, hm, a, b, c, hs⟩
    · rintro m ⟨a, b, c, hs⟩; exact ⟨_, hs⟩
  · rintro ⟨k, hk⟩
    induction k with
    | zero => simp [orbit] at hk
    | succ k ih =>
      rw [orbit_succ] at hk
      cases e : orbit k with
      | ok a b c =>
        rw [e] at hk
        obtain ⟨n, _, hs⟩ := orbit_run k a b c e
        obtain ⟨m, c', h1, h2⟩ := next_halt hk
        exact ⟨n + m, c', steps_seq trans hs h1, h2⟩
      | halt => exact ih e
      | stuck => rw [e] at hk; cases hk

end H74998
