import Map

/-!
# 1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA: the first two cycles of the map, and a lower bound on the run

The orbit of `(14, 5)` under `next` (Map.lean) comes back to `n = 5` (a *reset*) at phases 8 and 6,819.  At phase
6,819 the stack has `M` copies of `1011` with `M > 10^2900` (`orbit_6819`, evaluated by compiled code:
`native_decide`).  Each later phase uses up at most two of them and the map can only stop at `m = 1`, so the next
`10^2899` phases all exist (`orbit_stays`), and the machine does not halt in its first `10^2899` steps
(`runs_long`).
-/

namespace H166535

open TM

/-- `10^2899`. -/
def bound : Nat := 10 ^ 2899

/-- `10^2900 = 10 * bound`. -/
def big : Nat := 10 ^ 2900

theorem big_eq : big = 10 * bound := by
  unfold big bound; rw [Nat.pow_succ, Nat.mul_comm]

theorem bound_pos : 0 < bound := Nat.pow_pos (by decide)

/-- The check run by compiled code on the orbit at phase 6,819. -/
def check (o : Option (Nat × Nat)) : Bool :=
  match o with
  | some (M, 5) => decide (big < M)
  | _ => false

theorem of_check (o : Option (Nat × Nat)) (h : check o = true) : ∃ M, o = some (M, 5) ∧ big < M := by
  unfold check at h
  split at h
  · rename_i M
    exact ⟨M, rfl, by simpa using h⟩
  · cases h

theorem check_6819 : check (orbit 6819) = true := by native_decide

/-- The orbit at phase 6,819 is `(M, 5)` with `M > big = 10^2900`. -/
theorem orbit_6819 : ∃ M, orbit 6819 = some (M, 5) ∧ big < M := of_check _ check_6819

theorem next_some (m n : Nat) (hm : 2 ≤ m) (hn : 3 ≤ n) :
    ∃ m' n', next m n = some (m', n') ∧ m - 2 ≤ m' ∧ 5 ≤ n' := by
  obtain ⟨m, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  unfold next
  rw [if_neg (show ¬ n < 3 by omega)]
  have hr : (n - 3) % 3 < 3 := Nat.mod_lt _ (by omega)
  generalize (n - 3) % 3 = r at hr
  match r, hr with
  | 0, _ => exact ⟨_, _, rfl, by omega, by omega⟩
  | 1, _ => exact ⟨_, _, rfl, by omega, by omega⟩
  | 2, _ => exact ⟨_, _, rfl, by omega, by omega⟩

theorem orbit_stays (i m n : Nat) (h : orbit i = some (m, n)) (hn : 3 ≤ n) :
    ∀ j, 2 * j + 2 ≤ m → ∃ m' n', orbit (i + j) = some (m', n') ∧ 3 ≤ n' ∧ m - 2 * j ≤ m' := by
  intro j
  induction j with
  | zero => intro _; exact ⟨m, n, h, hn, by omega⟩
  | succ j ih =>
    intro hj
    obtain ⟨m', n', h', hn', hm'⟩ := ih (by omega)
    obtain ⟨m'', n'', h'', hm'', hn''⟩ := next_some m' n' (by omega) hn'
    refine ⟨m'', n'', ?_, by omega, by omega⟩
    show (orbit (i + j)).bind (fun x => next x.1 x.2) = _
    rw [h']; exact h''

/-- No halt in the first `bound = 10^2899` steps from blank tape. -/
theorem runs_long : ∀ t, t ≤ bound → ∃ c, steps t init = some c := by
  intro t ht
  obtain ⟨M, hM, hbig⟩ := orbit_6819
  rw [big_eq] at hbig
  have := bound_pos
  obtain ⟨m', n', h', _, _⟩ := orbit_stays 6819 M 5 hM (by omega) bound (by omega)
  obtain ⟨u, hu, hu'⟩ := orbit_reach _ m' n' h'
  rw [show u = t + (u - t) by omega] at hu'
  exact steps_le trans hu'

end H166535
