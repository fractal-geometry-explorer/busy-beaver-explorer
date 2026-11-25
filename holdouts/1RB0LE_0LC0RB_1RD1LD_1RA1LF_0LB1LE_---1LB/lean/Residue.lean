import Nest

/-!
# Trips into a block of each residue

A trip that meets a block at the start of the word, `L 0 0 0 1 1 A> 0 1^j 0 Z`, is decided by `j mod 3` once the trips
it makes into `Z` return. For `j ≥ 4` the first pass is the same for every `j` (`enter_gen`): the block becomes 0s
and the trip goes on into `Z`. The trip into `Z` and the ticks of a nested clock then eat those 0s three at a time,
and what is left over decides the end:

* `j = 4 + 3k`: nothing is left over; the trip is tick `k+1` of a nested clock (`nest`, `Nest.lean`).
* `j = 5 + 3m`: one 0 is left over. The trip becomes tick 0 of a nested clock with the trip's own `0 0 0` as its
  zeros (`trip_res2`), and that tick makes one trip into `1 1 ...`, which returns.
* `j = 6 + 3m`: two 0s are left over. The head turns back and rebuilds the trip's left end as `0 1 1 0 1 1 0 0`
  (`trip_res0`).

In all three cases the head leaves the trip's region to the left (`res2_leaves`, `res0_leaves`, `nest_then_tick`):
a trip into a word that starts with `0 1^j 0` for `j ≥ 4` never returns.
-/

namespace H38215

open TM

theorem ones_cons (n : Nat) (Y : Tape) : rep n [true] (cons true Y) = cons true (rep n [true] Y) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; rfl

theorem J_rep (m : Nat) (Z : Tape) : J m Z = rep (3 * m + 4) [true] (cons false Z) := by
  unfold J
  rw [rep_add]
  simp only [rep_succ, rep_zero, app, ones_cons]

/-- The trip's first pass over `0 1^(j+1) 0`, for every `j`: `1 1 A> 0 1^(j+1) 0 Z` becomes
`1 1 1 0^j 1 1 A> Z`. -/
theorem enter_gen (j : Nat) (Z L : Tape) :
    steps (j + 5) ⟨cons true (cons true (cons false (cons false (cons false L)))),
      cons false (cons true (rep j [true] (cons false Z))), .A⟩ =
      some ⟨cons true (cons true (rep j [false] (cons true (cons true (cons true (cons false (cons false
        (cons false L)))))))), Z, .A⟩ := by
  have h0 : steps 2 ⟨cons true (cons true (cons false (cons false (cons false L)))),
      cons false (cons true (rep j [true] (cons false Z))), .A⟩ =
      some ⟨cons false (cons true (cons true (cons true (cons false (cons false (cons false L)))))),
        rep j [true] (cons false Z), .B⟩ := rfl
  have h1 := bclear j (cons false (cons true (cons true (cons true (cons false (cons false (cons false L)))))))
    (cons false Z)
  rw [zeros_cons] at h1
  have h2 : steps 3 ⟨cons false (rep j [false] (cons true (cons true (cons true (cons false (cons false
      (cons false L))))))), cons false Z, .B⟩ =
      some ⟨cons true (cons true (rep j [false] (cons true (cons true (cons true (cons false (cons false
        (cons false L)))))))), Z, .A⟩ := rfl
  exact steps_congr trans (a := 2 + (j + 3)) (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

/-- One 0 left over: `1 1 1 0 E> 1^(4+3m) 0 W` becomes `E> 1^4 0 1^(3+3m) 0 W`. -/
theorem rule_r1 (m : Nat) (L W : Tape) :
    steps 10 ⟨cons false (cons true (cons true (cons true L))), J m W, .E⟩ =
      some ⟨L, J 0 (cons true (cons true (cons true (rep (3 * m) [true] (cons false W))))), .E⟩ := by
  have e : J m W = cons true (cons true (cons true (cons true (rep (3 * m) [true] (cons false W))))) := by
    unfold J; simp only [ones_cons]
  rw [e]; rfl

/-- Two 0s left over: `0 0 0 1 1 1 0 0 E> 1` turns back and becomes `E> 0 1 1 0 1 1 0 0 1`. -/
theorem rule_r2 (L R : Tape) :
    steps 12 ⟨cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons false L))))))),
      cons true R, .E⟩ =
      some ⟨L, cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons false
        (cons true R)))))))), .E⟩ := rfl

/-- `P(1 1 X) = 1 0 X` in 25 steps, for every `X`. -/
theorem pstep_11 (X : Tape) : PStep (cons true (cons true X)) (cons true (cons false X)) 25 := fun _ => rfl

theorem zeros_split (a b : Nat) (X : Tape) : rep (a + b) [false] X = rep a [false] (rep b [false] X) := rep_add _ _ _ _

/-- **`j = 5 + 3m`.** If `2^m` P-steps of cost `E` take `Z` to `Z'`, the trip into `0 1^(5+3m) 0 Z` reaches
`L 0 0 0 E> 1^4 0 1^(3+3m) 0 Z'`: tick 0 of a nested clock that uses the trip's own `0 0 0`. -/
theorem trip_res2 (m : Nat) (Z Z' : Tape) (E : Nat) (h : PChain (2 ^ m) Z Z' E) (L : Tape) :
    steps (3 * m + 9 + (E + CS 0 m) + 10)
      ⟨cons true (cons true (cons false (cons false (cons false L)))), cons false (cons true (J m Z)), .A⟩ =
      some ⟨cons false (cons false (cons false L)),
        J 0 (cons true (cons true (cons true (rep (3 * m) [true] (cons false Z'))))), .E⟩ := by
  have hn := NP_eq m 0
  simp only [Nat.pow_zero, Nat.zero_add] at hn
  rw [show 2 ^ m = 1 + NP 0 m by omega] at h
  obtain ⟨W1, E1, E2, h1, h2, he⟩ := PChain.split _ _ h
  cases h1 with
  | succ hs hz =>
    cases hz
    have s0 := enter_gen (3 * m + 4) Z L
    rw [← J_rep] at s0
    have z : rep (3 * m + 4) [false] (cons true (cons true (cons true (cons false (cons false (cons false L)))))) =
        cons false (cons false (cons false (rep (3 * m) [false] (cons false (cons true (cons true (cons true
          (cons false (cons false (cons false L)))))))))) := by
      rw [show 3 * m + 4 = 4 + 3 * m by omega, zeros_split]
      simp only [rep_succ, rep_zero, app, zeros_cons]
    rw [z] at s0
    have s1 := hs (rep (3 * m) [false] (cons false (cons true (cons true (cons true (cons false (cons false
      (cons false L))))))))
    have s2 := chain m 0 (fun i _ _ => tick i) W1 Z' E2 h2
      (cons false (cons true (cons true (cons true (cons false (cons false (cons false L)))))))
    simp only [Nat.zero_add] at s2
    have s3 := rule_r1 m (cons false (cons false (cons false L))) Z'
    have := steps_seq trans s0 (steps_seq trans s1 (steps_seq trans s2 s3))
    refine steps_congr trans ?_ this
    omega

/-- Then tick 0 makes its one trip, into `1 1 1 ...`, which returns, and the head leaves the region with
`1^7 0 1 0 1^(1+3m) 0 Z'` behind it. -/
theorem res2_leaves (m : Nat) (Z Z' : Tape) (E : Nat) (h : PChain (2 ^ m) Z Z' E) (L : Tape) :
    steps (3 * m + 9 + (E + CS 0 m) + 10 + (25 + 19 * 2 ^ 0 - 3))
      ⟨cons true (cons true (cons false (cons false (cons false L)))), cons false (cons true (J m Z)), .A⟩ =
      some ⟨L, J 1 (cons true (cons false (cons true (rep (3 * m) [true] (cons false Z'))))), .E⟩ := by
  have p : PChain (2 ^ 0) (cons true (cons true (cons true (rep (3 * m) [true] (cons false Z')))))
      (cons true (cons false (cons true (rep (3 * m) [true] (cons false Z'))))) 25 :=
    by simpa using PChain.succ (pstep_11 _) (.zero _)
  exact steps_seq trans (trip_res2 m Z Z' E h L) (tick 0 _ _ 25 p L)

/-- **`j = 6 + 3m`.** If `2^m` P-steps of cost `E` take `Z` to `Z'`, the trip into `0 1^(6+3m) 0 Z` turns back and
reaches `L E> 0 1 1 0 1 1 0 0 1^(4+3m) 0 Z'`; its next step leaves the region in state B. -/
theorem trip_res0 (m : Nat) (Z Z' : Tape) (E : Nat) (h : PChain (2 ^ m) Z Z' E) (L : Tape) :
    steps (3 * m + 10 + (E + CS 0 m) + 12)
      ⟨cons true (cons true (cons false (cons false (cons false L)))), cons false (cons true (cons true (J m Z))), .A⟩ =
      some ⟨L, cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons false
        (J m Z')))))))), .E⟩ := by
  have hn := NP_eq m 0
  simp only [Nat.pow_zero, Nat.zero_add] at hn
  rw [show 2 ^ m = 1 + NP 0 m by omega] at h
  obtain ⟨W1, E1, E2, h1, h2, he⟩ := PChain.split _ _ h
  cases h1 with
  | succ hs hz =>
    cases hz
    have s0 := enter_gen (3 * m + 5) Z L
    have ej : cons true (J m Z) = rep (3 * m + 5) [true] (cons false Z) := by
      rw [show 3 * m + 5 = (3 * m + 4) + 1 by omega, rep_succ, ← J_rep]; rfl
    rw [← ej] at s0
    have z : rep (3 * m + 5) [false] (cons true (cons true (cons true (cons false (cons false (cons false L)))))) =
        cons false (cons false (cons false (rep (3 * m) [false] (cons false (cons false (cons true (cons true
          (cons true (cons false (cons false (cons false L))))))))))) := by
      rw [show 3 * m + 5 = 5 + 3 * m by omega, zeros_split]
      simp only [rep_succ, rep_zero, app, zeros_cons]
    rw [z] at s0
    have s1 := hs (rep (3 * m) [false] (cons false (cons false (cons true (cons true (cons true (cons false
      (cons false (cons false L)))))))))
    have s2 := chain m 0 (fun i _ _ => tick i) W1 Z' E2 h2
      (cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons false L))))))))
    simp only [Nat.zero_add] at s2
    have s3 := rule_r2 L (rep (3 * m) [true] (cons true (cons true (cons true (cons false Z')))))
    have := steps_seq trans s0 (steps_seq trans s1 (steps_seq trans s2 s3))
    refine steps_congr trans ?_ this
    omega

/-- The step after `trip_res0`: the head leaves the region in state B. -/
theorem res0_leaves (m : Nat) (Z Z' : Tape) (E : Nat) (h : PChain (2 ^ m) Z Z' E) (b : Bool) (L : Tape) :
    steps (3 * m + 10 + (E + CS 0 m) + 12 + 1)
      ⟨cons true (cons true (cons false (cons false (cons false (cons b L))))),
        cons false (cons true (cons true (J m Z))), .A⟩ =
      some ⟨L, cons b (cons false (cons true (cons true (cons false (cons true (cons true (cons false (cons false
        (J m Z'))))))))), .B⟩ :=
  steps_seq trans (trip_res0 m Z Z' E h (cons b L)) rfl

end H38215
