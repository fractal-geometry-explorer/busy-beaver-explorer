import Visit

/-! Many visits at once, for 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---.

`VisN n s s'`: n visits in a row rewrite the stream `s` to `s'`. The theorem `visN_rep1010` is the step the fast
simulator `c/visp.c` takes at the start of every round: the tape there is `(1010)^j s`, and n visits of it are
n·2^j visits of `s`, with the blocks `1010` written back unchanged. Kernel only (no `native_decide`). -/

namespace H173741

open TM

/-- `n` visits in a row turn `s` into `s'`. -/
def VisN : Nat → Tape → Tape → Prop
  | 0, s, s' => s' = s
  | n + 1, s, s' => ∃ t, Vis s t ∧ VisN n t s'

/-- `1010` repeated `j` times in front of `s`. -/
def rep1010 : Nat → Tape → Tape
  | 0, s => s
  | j + 1, s => cons true (cons false (cons true (cons false (rep1010 j s))))

theorem visN_one {s s' : Tape} (h : Vis s s') : VisN 1 s s' := ⟨s', h, rfl⟩

/-- Visits compose: `a` visits and then `b` visits are `a + b` visits. -/
theorem visN_add {a b : Nat} {s t s' : Tape} (h1 : VisN a s t) (h2 : VisN b t s') : VisN (b + a) s s' := by
  induction a generalizing s with
  | zero => cases h1; exact h2
  | succ a ih =>
    obtain ⟨u, hu, hr⟩ := h1
    exact ⟨u, hu, ih hr⟩

/-- `n` visits of `1010 s` are `2n` visits of `s` (from `vis_1010`). -/
theorem visN_1010 {n : Nat} {s s' : Tape} (h : VisN (2 * n) s s') :
    VisN n (cons true (cons false (cons true (cons false s)))) (cons true (cons false (cons true (cons false s')))) := by
  induction n generalizing s with
  | zero => cases h; rfl
  | succ n ih =>
    have e : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [e] at h
    obtain ⟨t1, h1, t2, h2, hr⟩ := h
    exact ⟨_, vis_1010 h1 h2, ih hr⟩

/-- `n` visits of `(1010)^j s` are `n·2^j` visits of `s`; the blocks `1010` come back unchanged. -/
theorem visN_rep1010 (j : Nat) {n : Nat} {s s' : Tape} (h : VisN (n * 2 ^ j) s s') :
    VisN n (rep1010 j s) (rep1010 j s') := by
  induction j generalizing n with
  | zero => simpa [rep1010] using h
  | succ j ih =>
    have e : n * 2 ^ (j + 1) = (2 * n) * 2 ^ j := by
      rw [Nat.pow_succ, Nat.mul_comm 2 n, Nat.mul_assoc, Nat.mul_comm (2 ^ j) 2]
    rw [e] at h
    exact visN_1010 (ih h)

end H173741
