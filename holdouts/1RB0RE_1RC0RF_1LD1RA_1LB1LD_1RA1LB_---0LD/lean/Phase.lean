import Rules

/-!
# 1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD: the rounds of a phase

A phase starts at the left end of the tape: `0^inf B> 0 1 0^X T`, a single 1, a gap of X zeros, then the tail T (a
list of short blocks).  Each round the block of ones grows by six and the marker `000 1111` moves four cells into
the gap; here, for every gap X = 4k + r + 7 ≥ 24, the phase reaches `0^inf 1 C> (11)^(3k+3) 000 1111 0^r T`, the
point where the marker has eaten the gap and the head is about to meet the tail with r ∈ {1, 3} zeros left.
-/

namespace H66128

open TM

/-- `c` reaches `c'` in some number of steps. -/
def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches.trans {a b c : Config} (h₁ : Reaches a b) (h₂ : Reaches b c) : Reaches a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, steps_seq H66128.trans hn hm⟩

/-- `0^inf 1 C> (11)^m 000 1111 R`: the head at the left end, the block of ones, the marker, then `R`. -/
def W (m : Nat) (R : Tape) : Config :=
  ⟨cons true blank, rep m [true, true] (app [false, false, false, true, true, true, true] R), .C⟩

theorem one_rot (m : Nat) (s : Tape) : cons true (rep m [true, true] s) = rep m [true, true] (cons true s) :=
  rep_rotate m [true] [true, true] [true, true] rfl s

theorem round' (n : Nat) (R : Tape) : Reaches (W (n + 1) (rep 4 [false] R)) (W (n + 4) R) := by
  refine ⟨6 * n + 50, ?_⟩
  have h := round n R
  have e : W (n + 4) R = ⟨cons true blank, cons true (cons true (cons true (cons true (cons true (rep n [true, true]
      (cons true (cons true (cons true (app [false, false, false, true, true, true, true] R))))))))), .C⟩ := by
    have e2 : ∀ s : Tape, cons true (cons true (cons true (cons true (cons true (rep n [true, true]
        (cons true (cons true (cons true s)))))))) = rep (n + 4) [true, true] s := by
      intro s
      have : rep n [true, true] (cons true (cons true (cons true s))) = rep (n + 1) [true, true] (cons true s) :=
        rep_app_comm n [true, true] (cons true s)
      rw [this]
      simp only [one_rot]
      show rep (n + 1) [true, true] (app [true, true] (app [true, true] (app [true, true] s))) = _
      rw [rep_app_comm, rep_app_comm, rep_app_comm]
    simp only [W]
    rw [e2]
  rw [e]
  exact h

theorem rounds (k : Nat) : ∀ n R, Reaches (W (n + 1) (rep (4 * k) [false] R)) (W (n + 1 + 3 * k) R) := by
  induction k with
  | zero => intro n R; exact ⟨0, rfl⟩
  | succ k ih =>
    intro n R
    have e : rep (4 * (k + 1)) [false] R = rep 4 [false] (rep (4 * k) [false] R) := by
      rw [show 4 * (k + 1) = 4 + 4 * k by omega, rep_add]
    rw [e]
    have h2 := ih (n + 3) R
    rw [show n + 3 + 1 + 3 * k = n + 1 + 3 * (k + 1) by omega] at h2
    exact (round' n _).trans h2

/-- The rounds of a phase: from `0^inf B> 0 1 0^(4k+r+7) R` (gap at least 24) to the end of the gap. -/
theorem phase (k r : Nat) (R : Tape) (h : 17 ≤ 4 * k + r) :
    Reaches ⟨blank, cons false (cons true (rep (4 * k + r + 7) [false] R)), .B⟩ (W (3 * k + 3) (rep r [false] R)) := by
  have hn : 4 * k + r + 7 = (4 * k + r - 17) + 24 := by omega
  have hn' : (4 * k + r - 17) + 17 = 4 * k + r := by omega
  generalize 4 * k + r - 17 = n at hn hn'
  have h1 : Reaches ⟨blank, cons false (cons true (rep (4 * k + r + 7) [false] R)), .B⟩
      (W 3 (rep (n + 17) [false] R)) := ⟨_, by rw [hn]; exact start n R⟩
  have e : rep (n + 17) [false] R = rep (4 * k) [false] (rep r [false] R) := by
    rw [← rep_add, hn']
  rw [e] at h1
  have h2 := rounds k 2 (rep r [false] R)
  rw [show 2 + 1 + 3 * k = 3 * k + 3 by omega] at h2
  exact h1.trans h2

end H66128
