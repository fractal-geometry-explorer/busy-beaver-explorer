import Chain

/-!
# A chain end at a `0` marker, for all parameters

When the pairs left of the inner cycles run out and the next cell is a `0` marker (`S L' 0 u (r+2)` with
`L' = L (10)^(x+1) 0`), the marker is absorbed (`absorb0`), and a second cycle (`eat`) starts.  Each turn of it takes
two pairs from the run left of the marker and turns one `1010` block on the right into pairs:
`L (10)^(x+2) C>(10)^(k+1) 110 (1010)^(n+1) R` reaches `L (10)^x C>(10)^(k+5) 110 (1010)^n R`.
`end0` chains them: after the marker is absorbed, `t` turns of `eat` follow.  This is a piece of the chain-end
map, not the whole of it: what happens when `x` or the `1010` blocks run out is not proved here.
-/

namespace H131324

open TM

/-- The frame of the eating cycle: `L (10)^x C> (10)^(k+1) 110 (1010)^n R`. -/
def E (L R : Tape) (x k n : Nat) : Config :=
  ⟨rep x [false, true] L,
   rep (k + 1) [true, false] (cons true (cons true (cons false (rep n [true, false, true, false] R)))), .C⟩

theorem five_pairs (k : Nat) (Y : Tape) :
    cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false
      (rep k [true, false] (cons true (cons false Y)))))))))) = rep (k + 4 + 1) [true, false] Y := by
  show app [true, false] (app [true, false] (app [true, false] (app [true, false]
    (rep k [true, false] (app [true, false] Y))))) = _
  rw [rep_app_comm]
  rfl

theorem eat' (L R : Tape) (x k n : Nat) : Reach (E L R (x + 2) k (n + 1)) (E L R x (k + 4) n) :=
  reach_of (eat k n x L R) (by unfold E; rw [five_pairs])

theorem eatN (L R : Tape) (t : Nat) : ∀ x k n, Reach (E L R (x + 2 * t) k (n + t)) (E L R x (k + 4 * t) n) := by
  induction t with
  | zero => intro x k n; exact ⟨0, rfl⟩
  | succ t ih =>
    intro x k n
    rw [show x + 2 * (t + 1) = (x + 2 * t) + 2 by omega, show n + (t + 1) = (n + t) + 1 by omega]
    have h := ih x (k + 4) n
    rw [show k + 4 + 4 * t = k + 4 * (t + 1) by omega] at h
    exact (eat' L R (x + 2 * t) k (n + t)).join h

/-- The right part left behind by `absorb0`: `1 0 1 1 0 (10)^r 1`. -/
def R0 (r : Nat) : Tape := cons true (cons false (cons true (cons true (cons false (rep r [true, false] (cons true blank))))))

theorem absorb0' (L : Tape) (x u r : Nat) :
    Reach (S (cons false (rep (x + 1) [false, true] L)) 0 u (r + 2)) (E L (R0 r) x 0 (2 * u + 1)) := by
  have h := absorb0 r u x L (cons true blank)
  refine reach_of h ?_
  unfold E R0
  show _ = (⟨_, app [true, false] (cons true (cons true (cons false (rep (2 * u + 1) [true, false, true, false] _)))), _⟩ : Config)
  have e := rep_rotate (2 * u + 1) [true] [false, true, false, true] [true, false, true, false] rfl
    (cons false (cons true (cons true (cons false (rep r [true, false] (cons true blank))))))
  simp only [app] at e
  rw [e]
  rfl

/-- A chain end at a `0` marker, then `t` turns of the eating cycle (`n + t = 2u+1` blocks `1010` in all). -/
theorem end0 (L : Tape) (x u r n t : Nat) (h : n + t = 2 * u + 1) :
    Reach (S (cons false (rep (x + 2 * t + 1) [false, true] L)) 0 u (r + 2)) (E L (R0 r) x (4 * t) n) := by
  have a := absorb0' L (x + 2 * t) u r
  rw [← h] at a
  have b := eatN L (R0 r) t x 0 n
  rw [Nat.zero_add] at b
  exact a.join b

end H131324
