import Clock
import Rules

/-!
# A clock inside the word

A trip into the word starts at `L 0 0 0 1 1 A> W` (`PStep`). When the word begins with `0 1^(4+3k) 0`, the trip
does not stay a short excursion: it becomes a copy of the clock.

**Theorem `nest`.** For every `k`, every `Z` and every `L`, if `2^k` P-steps of total cost `E` take `Z` to `Z'`,
then

    L 0 0 0 1 1 A> 0 1^(4+3k) 0 Z   reaches   L 0 0 0 E> 1^(4+3(k+1)) 0 Z'

in exactly `3k + 8 + E + CS 0 k + 3` steps. `CS 0 k` is the structural count of ticks `0, ..., k-1` from `Clock.lean`,
equal to `19·(2^k − 1) − 3k`, so the total is `E + 19·2^k − 8`.

The proof has three parts:
1. `enter`: the trip's first pass turns the block `1^(4+3k)` into `0^(3+3k)` and goes on to `Z`. The result is
   exactly the tape the sweep of tick `k` leaves, one level further left. Its three left zeros are the trip's own
   `0 0 0`.
2. `after_sweep`: the rest of tick `k`, which is one P-step, ticks `0, ..., k-1` and the merge (the proof of `tick`
   without its sweep).
3. Putting the two together.

The end is the start of tick `k+1`, with the trip's region as the left-end zeros. So the word's block `1^(4+3k)`
becomes a clock that runs in the trip's place: from here on it ticks with `L` as its left end. It eats zeros of `L`
three at a time, as the main clock eats the blank tape. Each of its trips is again a P-step into what remains of the
word. A trip can therefore hold a whole nested clock, and this is why no finite list of trip outcomes covers every word
(see the README).
-/

namespace H38215

open TM

/-- The trip's first pass over `0 1^(4+3k) 0`: the result is the sweep's output (`rule_sweep`) with the trip's
`0 0 0` as the three zeros left of the block. -/
theorem enter (k : Nat) (Z L : Tape) :
    steps (3 * k + 8) ⟨cons true (cons true (cons false (cons false (cons false L)))), cons false (J k Z), .A⟩ =
      some ⟨cons true (cons true (cons false (cons false (rep (3 * k) [false]
        (cons false (cons true (cons true (cons true (cons false (cons false (cons false L))))))))))), Z, .A⟩ := by
  have h0 : steps 2 ⟨cons true (cons true (cons false (cons false (cons false L)))), cons false (J k Z), .A⟩ =
      some ⟨cons false (cons true (cons true (cons true (cons false (cons false (cons false L)))))),
        rep (3 * k) [true] (cons true (cons true (cons true (cons false Z)))), .B⟩ := rfl
  have h1 := bclear (3 * k) (cons false (cons true (cons true (cons true (cons false (cons false (cons false L)))))))
    (cons true (cons true (cons true (cons false Z))))
  have h2 : steps 6 ⟨rep (3 * k) [false] (cons false (cons true (cons true (cons true (cons false (cons false
      (cons false L))))))), cons true (cons true (cons true (cons false Z))), .B⟩ =
      some ⟨cons true (cons true (cons false (cons false (rep (3 * k) [false]
        (cons false (cons true (cons true (cons true (cons false (cons false (cons false L))))))))))), Z, .A⟩ := rfl
  exact steps_congr trans (a := 2 + (3 * k + 6)) (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

/-- Tick `j` after its sweep: one P-step, ticks `0, ..., j-1` and the merge. -/
theorem after_sweep (j : Nat) (W W' : Tape) (E : Nat) (h : PChain (2 ^ j) W W' E) (L : Tape) :
    steps (E + CS 0 j + 3) ⟨cons true (cons true (cons false (cons false (rep (3 * j) [false]
      (cons false (cons true (cons true (cons true L)))))))), W, .A⟩ = some ⟨L, J (j + 1) W', .E⟩ := by
  have hn := NP_eq j 0
  simp only [Nat.pow_zero, Nat.zero_add] at hn
  rw [show 2 ^ j = 1 + NP 0 j by omega] at h
  obtain ⟨W1, E1, E2, h1, h2, he⟩ := PChain.split _ _ h
  cases h1 with
  | succ hs hz =>
    cases hz
    have s1 := hs (rep (3 * j) [false] (cons true (cons true (cons true L))))
    have s2 := chain j 0 (fun i _ _ => tick i) W1 W' E2 h2 (cons true (cons true (cons true L)))
    simp only [zeros_cons] at s1 s2 ⊢
    have s3 := rule_merge L (rep (3 * (0 + j)) [true] (cons true (cons true (cons true (cons false W')))))
    have e3 : cons true (cons true (cons true (cons true (rep (3 * (0 + j)) [true]
        (cons true (cons true (cons true (cons false W')))))))) = J (j + 1) W' := by
      unfold J; rw [show 3 * (j + 1) = 3 * (0 + j) + 1 + 1 + 1 by omega]; rfl
    rw [e3] at s3
    have := steps_seq trans s1 (steps_seq trans s2 s3)
    refine steps_congr trans ?_ this
    omega

/-- **A clock inside the word.** A trip into `0 1^(4+3k) 0 Z` whose first `2^k` nested P-steps on `Z` return
reaches the start of tick `k+1`, with the trip's own `0 0 0` as the left-end zeros. -/
theorem nest (k : Nat) (Z Z' : Tape) (E : Nat) (h : PChain (2 ^ k) Z Z' E) (L : Tape) :
    steps (3 * k + 8 + (E + CS 0 k + 3))
      ⟨cons true (cons true (cons false (cons false (cons false L)))), cons false (J k Z), .A⟩ =
      some ⟨cons false (cons false (cons false L)), J (k + 1) Z', .E⟩ :=
  steps_seq trans (enter k Z L) (after_sweep k Z Z' E h (cons false (cons false (cons false L))))

/-- The nested clock then goes on ticking in the trip's place, by the same theorem as the main clock: tick `k+1`
eats the trip's `0 0 0`, and its result has `L` to its left. -/
theorem nest_then_tick (k : Nat) (Z Z' Z'' : Tape) (E E' : Nat) (h : PChain (2 ^ k) Z Z' E)
    (h' : PChain (2 ^ (k + 1)) Z' Z'' E') (L : Tape) :
    steps (3 * k + 8 + (E + CS 0 k + 3) + (E' + 19 * 2 ^ (k + 1) - 3))
      ⟨cons true (cons true (cons false (cons false (cons false L)))), cons false (J k Z), .A⟩ =
      some ⟨L, J (k + 2) Z'', .E⟩ :=
  steps_seq trans (nest k Z Z' E h L) (tick (k + 1) Z' Z'' E' h' L)

end H38215
