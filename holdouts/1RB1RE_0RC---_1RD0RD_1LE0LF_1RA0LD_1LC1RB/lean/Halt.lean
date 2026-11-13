import Macro
import Ternary

/-! # 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB: the drain, iterated, and the way it halts

The drain configuration D(A,B) is `1^A (01)^B 0 C> 0 Z` (left tape `Dl A B L`).  `drain` iterates `m_sweep`:
k sweeps take D(A+2k,B) to D(A,B+2k) and use 2k cells of 0s to the right, whatever lies beyond.

The machine halts only when B reads a 1 (`step_none_iff`).  `halt_001`: state E running right over pairs `01` into
`0 0 1` halts, whatever is around.  `drain_halts`: so an odd drain D(2k+1,B) whose 0s to the right number exactly
2k+3 before the next 1 halts: after k sweeps it is D(1,B+2k) (`m_end1`), E runs over B+2k+3 pairs into `0 0 1`.
This is how the run would halt: a drain inside a gap of 0s that ends exactly three cells short of the block to its
right.  `start_halts_gap3` is the smallest case (the run from scratch inside a gap of three 0s). -/

namespace H8002

open TM

/-- The left tape of a drain: `L 1^A (01)^B 0`, nearest the head first. -/
def Dl (A B : Nat) (L : Tape) : Tape := cons false (rep B [true, false] (rep A [true] L))

theorem rot10 (b : Nat) (X : Tape) : cons true (rep b [false, true] X) = rep b [true, false] (cons true X) :=
  rep_rotate b [true] [false, true] [true, false] rfl X

/-- One sweep in drain form. -/
theorem sweep_D (a b : Nat) (L R : Tape) :
    steps (6 * b + 16) ⟨Dl (a + 3) b L, cons false (cons false R), .C⟩ = some ⟨Dl (a + 1) (b + 2) L, R, .C⟩ := by
  have h := m_sweep b (rep a [true] L) R
  have e : cons true (rep b [false, true] (cons false (cons true (cons false (cons true (rep a [true] L))))))
      = rep (b + 2) [true, false] (rep (a + 1) [true] L) := by
    rw [rot10, rep_add]; rfl
  rw [e] at h
  exact h

/-- k sweeps: D(A+1+2k,B) with 2k 0s at the head becomes D(A+1,B+2k). -/
theorem drain (k : Nat) : ∀ (a b : Nat) (L R : Tape),
    ∃ t, steps t ⟨Dl (a + 1 + 2 * k) b L, rep (2 * k) [false] R, .C⟩ = some ⟨Dl (a + 1) (b + 2 * k) L, R, .C⟩ := by
  induction k with
  | zero => intro a b L R; exact ⟨0, rfl⟩
  | succ k ih =>
    intro a b L R
    have e1 : a + 1 + 2 * (k + 1) = (a + 2 * k) + 3 := by omega
    have e2 : rep (2 * (k + 1)) [false] R = cons false (cons false (rep (2 * k) [false] R)) := by
      have : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [this, rep_succ, rep_succ]; rfl
    have h1 := sweep_D (a + 2 * k) b L (rep (2 * k) [false] R)
    obtain ⟨t, h2⟩ := ih a (b + 2) L R
    have e3 : a + 2 * k + 1 = a + 1 + 2 * k := by omega
    have e4 : b + 2 + 2 * k = b + 2 * (k + 1) := by omega
    rw [e3] at h1
    rw [e4] at h2
    rw [e2, e1]
    exact ⟨_, steps_seq trans h1 h2⟩

/-- E runs right over pairs `01`, turning them into `11`. -/
theorem e_run (n : Nat) (L R : Tape) :
    steps (n * 2) ⟨L, rep n [false, true] R, .E⟩ = some ⟨rep n [true, true] L, R, .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ :=
    fun _ _ => rfl
  exact cross_r trans c0 n L R

/-- **E over pairs `01` into `0 0 1` halts** (E0 -> A, A0 -> B, B reads the 1). -/
theorem halt_001 (n : Nat) (L R : Tape) :
    Halts trans ⟨L, rep n [false, true] (cons false (cons false (cons true R))), .E⟩ := by
  refine ⟨n * 2 + 2, ⟨cons true (cons true (rep n [true, true] L)), cons true R, .B⟩, ?_, rfl⟩
  have h1 := e_run n L (cons false (cons false (cons true R)))
  have h2 : steps 2 ⟨rep n [true, true] L, cons false (cons false (cons true R)), .E⟩
      = some ⟨cons true (cons true (rep n [true, true] L)), cons true R, .B⟩ := rfl
  exact steps_seq trans h1 h2

/-- `m_end1` in drain form. -/
theorem end1_D (b : Nat) (R : Tape) :
    steps (2 * b + 6) ⟨Dl 1 b blank, cons false (cons false R), .C⟩ = some ⟨blank, rep (b + 3) [false, true] R, .E⟩ := by
  have h := m_end1 b R
  have e : cons false (cons true (cons false (cons true (cons false (rep b [true, false] (cons true R))))))
      = rep (b + 3) [false, true] R := by
    rw [shift01, ← rep_app_comm, ← rep_app_comm]; rfl
  rw [e] at h
  exact h

/-- **An odd drain three 0s short of a 1 halts.**  D(2k+1,B), blank to the left, with exactly 2k+3 cells of 0
after the head cell and then a 1: after k sweeps it is D(1,B+2k), then T(B+2k+3) runs into `0 0 1`. -/
theorem drain_halts (k b : Nat) (R : Tape) :
    Halts trans ⟨Dl (1 + 2 * k) b blank,
      rep (2 * k) [false] (cons false (cons false (cons false (cons false (cons true R))))), .C⟩ := by
  obtain ⟨t, h1⟩ := drain k 0 b blank (cons false (cons false (cons false (cons false (cons true R)))))
  rw [show 0 + 1 + 2 * k = 1 + 2 * k by omega, show (0 : Nat) + 1 = 1 by rfl] at h1
  have h2 := end1_D (b + 2 * k) (cons false (cons false (cons true R)))
  obtain ⟨n, c', h3, h4⟩ := halt_001 (b + 2 * k + 3) blank R
  exact ⟨_, c', steps_seq trans h1 (steps_seq trans h2 h3), h4⟩

/-- From blank tape the run reaches S = D(1,0) = `1 0 C> 0` in two steps; the run inside a gap starts the same way. -/
theorem start_S : steps 2 init = some ⟨Dl 1 0 blank, blank, .C⟩ := by
  have h : TM.fsteps trans 2 (TM.FCfg.blank .A) = some ⟨[false, true], [], .C⟩ := by decide
  exact blank_reaches trans h

/-- The smallest halting gap: S followed by three 0s and then a 1 halts (k = 0, B = 0 of `drain_halts`). -/
theorem start_halts_gap3 (R : Tape) :
    Halts trans ⟨Dl 1 0 blank, cons false (cons false (cons false (cons false (cons true R)))), .C⟩ :=
  drain_halts 0 0 R

/-- One odd sweep in drain form: D(A+3,B) next to `0 (10)^(c+2) 1` becomes D(A+1,B+3) next to `0 (10)^c 1`. -/
theorem odd_D (a b c : Nat) (L R : Tape) :
    steps (6 * b + 24) ⟨Dl (a + 3) b L, cons false (cons false (rep (c + 2) [true, false] (cons true R))), .C⟩ =
      some ⟨Dl (a + 1) (b + 3) L, cons false (cons false (rep c [true, false] (cons true R))), .C⟩ := by
  have h := m_odd b c (rep a [true] L) R
  have e : cons true (cons false (cons true (rep b [false, true] (cons false (cons true (cons false (cons true (rep a [true] L))))))))
      = rep (b + 3) [true, false] (rep (a + 1) [true] L) := by
    rw [rot10]
    show rep 1 [true, false] (rep b [true, false] (rep 2 [true, false] (rep (a + 1) [true] L))) = _
    rw [← rep_add, ← rep_add, show 1 + b + 2 = b + 3 by omega]
  rw [e] at h
  exact h

/-- k odd sweeps (k rounds of the ternary step): D(A+1+2k,B) next to `0 (10)^(c+2k) 1` becomes D(A+1,B+3k) next
to `0 (10)^c 1`. -/
theorem odd_drain (k : Nat) : ∀ (a b c : Nat) (L R : Tape),
    ∃ t, steps t ⟨Dl (a + 1 + 2 * k) b L, cons false (cons false (rep (c + 2 * k) [true, false] (cons true R))), .C⟩ =
      some ⟨Dl (a + 1) (b + 3 * k) L, cons false (cons false (rep c [true, false] (cons true R))), .C⟩ := by
  induction k with
  | zero => intro a b c L R; exact ⟨0, rfl⟩
  | succ k ih =>
    intro a b c L R
    have h1 := odd_D (a + 2 * k) b (c + 2 * k) L R
    obtain ⟨t, h2⟩ := ih a (b + 3) c L R
    rw [show a + 2 * k + 1 = a + 1 + 2 * k by omega] at h1
    rw [show b + 3 + 3 * k = b + 3 * (k + 1) by omega] at h2
    rw [show a + 1 + 2 * (k + 1) = a + 2 * k + 3 by omega, show c + 2 * (k + 1) = c + 2 * k + 2 by omega]
    exact ⟨_, steps_seq trans h1 h2⟩

/-- **The second way to halt.**  A drain D(A+3+2k,B) next to a block `0 (10)^(2k) 1` that is followed by exactly
three 0s and a 1: k odd sweeps use up the block, and the parity tail has no room (`m_tail_halt`). -/
theorem tail_halts (k a b : Nat) (L R : Tape) :
    Halts trans ⟨Dl (a + 3 + 2 * k) b L, cons false (cons false (rep (2 * k) [true, false]
      (cons true (cons false (cons false (cons false (cons true R))))))), .C⟩ := by
  obtain ⟨t, h1⟩ := odd_drain k (a + 2) b 0 L (cons false (cons false (cons false (cons true R))))
  rw [show 0 + 2 * k = 2 * k by omega, show a + 2 + 1 + 2 * k = a + 3 + 2 * k by omega] at h1
  have h2 := m_tail_halt (b + 3 * k) (rep a [true] L) R
  have e : Dl (a + 2 + 1) (b + 3 * k) L = cons false (rep (b + 3 * k) [true, false] (cons true (cons true (cons true
      (rep a [true] L))))) := rfl
  rw [← e] at h2
  exact ⟨_, _, steps_seq trans h1 h2, rfl⟩

end H8002
