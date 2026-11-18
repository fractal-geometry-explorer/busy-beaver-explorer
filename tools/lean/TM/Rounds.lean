import TM.Insert

/-!
# Following an inserted word round by round

`TM.halts_iff_of_good` (`TM/Insert.lean`) needs `Good t c`: the followed run of `c` never reaches a bad moment.
That is a statement about the whole run.  Many runs come back again and again to configurations of one kind (a
*round* ends where the next one starts), and the followed insertion comes back to one of a few allowed places each
time.  Then `Good` splits into one statement per round:

* `trk_add`: following `n + k` steps is following `n` steps and then `k` more;
* `trk_steps`: what the tracker reaches after `n` steps, the run reaches after at most `n` steps;
* **`good_of_rounds`**: if from every pair (insertion, configuration) of a set `P` the followed run either is good
  for ever, or comes after `n ≥ 1` steps without a bad moment to a pair of `P` again, then every pair of `P` is good.

For any machine `δ`; kernel only.
-/

namespace TM

variable {Q : Type} [DecidableEq Q] (δ : Q → Bool → Option (Bool × Dir × Q))

theorem trk_halt {fuel : Nat} {c : Cfg Q} (h : step δ c = none) : ∀ (k : Nat) (t : Ins), trk δ fuel k t c = some (t, c)
  | 0, _ => rfl
  | _ + 1, _ => by simp [trk, h]

/-- Following `n + k` steps is following `n` steps and then `k` more. -/
theorem trk_add {fuel : Nat} : ∀ (n k : Nat) (t : Ins) (c : Cfg Q),
    trk δ fuel (n + k) t c = (trk δ fuel n t c).bind (fun p => trk δ fuel k p.1 p.2)
  | 0, k, t, c => by simp [trk]
  | n + 1, k, t, c => by
    rw [Nat.add_right_comm]
    rcases hs : step δ c with _ | d
    · simp only [trk, hs, Option.bind_some]
      exact (trk_halt δ hs _ _).symm
    · rcases ht : tnext δ fuel t c with _ | t'
      · simp [trk, hs, ht]
      · simp only [trk, hs, ht]
        exact trk_add n k t' d

/-- Once the tracker has stopped at a bad moment, it stays stopped. -/
theorem trk_none_le {fuel : Nat} {m n : Nat} {t : Ins} {c : Cfg Q} (hmn : m ≤ n) (h : trk δ fuel m t c = none) :
    trk δ fuel n t c = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [trk_add, h]; rfl

/-- What the tracker reaches after `n` steps, the run reaches after at most `n` steps. -/
theorem trk_steps {fuel : Nat} : ∀ (n : Nat) {t t' : Ins} {c d : Cfg Q}, trk δ fuel n t c = some (t', d) →
    ∃ k, k ≤ n ∧ steps δ k c = some d
  | 0, t, t', c, d, h => by
    simp only [trk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨0, Nat.le_refl 0, rfl⟩
  | n + 1, t, t', c, d, h => by
    rcases hs : step δ c with _ | e
    · simp only [trk, hs, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨0, Nat.zero_le _, rfl⟩
    · rcases ht : tnext δ fuel t c with _ | t''
      · simp [trk, hs, ht] at h
      · simp only [trk, hs, ht] at h
        obtain ⟨k, hk, hk'⟩ := trk_steps n h
        exact ⟨k + 1, by omega, by rw [steps_succ_of_step δ k hs]; exact hk'⟩

/-- **Good, round by round.**  `P` is a set of pairs of an insertion and a configuration (the starts of rounds, with
the word somewhere allowed).  If from each of them the followed run is good for ever, or is followed for `n ≥ 1`
steps without a bad moment to a pair of `P` again, then each of them is good. -/
theorem good_of_rounds {fuel : Nat} (P : Ins → Cfg Q → Prop)
    (h : ∀ t c, P t c → Good δ fuel t c ∨ ∃ n t' d, 1 ≤ n ∧ trk δ fuel n t c = some (t', d) ∧ P t' d) :
    ∀ t c, P t c → Good δ fuel t c := by
  intro t c hc m
  induction m using Nat.strongRecOn generalizing t c with
  | _ m ih =>
    rcases h t c hc with hg | ⟨n, t', d, hn, htr, hd⟩
    · exact hg m
    · by_cases hmn : m ≤ n
      · intro hm
        rw [trk_none_le δ hmn hm] at htr; cases htr
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_le hmn))
        rw [trk_add, htr]
        exact ih k (by omega) t' d hd

end TM
