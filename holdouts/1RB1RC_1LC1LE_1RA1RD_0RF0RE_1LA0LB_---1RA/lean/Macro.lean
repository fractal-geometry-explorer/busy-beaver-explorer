import Blank
import Rules

/-!
# One round in closed form, and halting reduced to an Antihydra-like map

A *round start* is the head in state A on the blank cell left of the tape, the tape being

* `R n m = 0^∞ A> 0 11 (01)^n 0 11 (01)^m 0^∞` (a number `n` and a counter `m`), or
* `Z k = 0^∞ A> 0 11 (01)^k 0^∞` (the counter used up).

In a round the head sweeps between the left end and the first `11`: each sweep turns two copies of `01` right of the
`11` into three left of it (`pass`, any number of times by `passes`), so `n` becomes about `3n/2`.  What is left at
the end (none or one copy) decides the counter: it gains two copies for even `n` and loses one for odd `n`.  `next`
is the map, `round` proves each round and `round_halt` the halting one (`Z k` with `k` even).  Reduction.lean puts
them together: the machine halts from blank tape iff the orbit of `next` from `Z 1` reaches `Z k` with `k` even.
Everything is checked by Lean's kernel.
-/

namespace H174634

open TM

/-! ## Runs between configurations -/

/-- `c` reaches `c'` in some number of steps (maybe none). -/
def Run (c c' : Config) : Prop := ∃ n, steps n c = some c'

/-- `c` reaches `c'` in at least one step. -/
def Reaches (c c' : Config) : Prop := ∃ n, steps (n + 1) c = some c'

theorem Run.trans {a b c : Config} (h₁ : Run a b) (h₂ : Run b c) : Run a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, steps_seq H174634.trans hn hm⟩

theorem Reaches.run {a b c : Config} (h₁ : Reaches a b) (h₂ : Run b c) : Reaches a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, by
    have := steps_seq H174634.trans hn hm
    rw [show n + 1 + m = n + m + 1 by omega] at this
    exact this⟩

theorem run_of_eq {n : Nat} {c c' d : Config} (h : steps n c = some c') (e : c' = d) : Run c d := ⟨n, e ▸ h⟩

theorem reaches_of_eq {n : Nat} {c c' d : Config} (h : steps n c = some c') (hn : 0 < n) (e : c' = d) :
    Reaches c d := ⟨n - 1, by rw [show n - 1 + 1 = n by omega]; exact e ▸ h⟩

theorem halts_of_reaches {c c' : Config} (h : Reaches c c') (h' : TM.Halts trans c') : TM.Halts trans c := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, d, hm, hd⟩ := h'
  exact ⟨n + 1 + m, d, steps_seq trans hn hm, hd⟩

theorem halts_of_run {c c' : Config} (h : Run c c') (h' : TM.Halts trans c') : TM.Halts trans c := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, d, hm, hd⟩ := h'
  exact ⟨n + m, d, steps_seq trans hn hm, hd⟩

/-! ## Tapes -/

abbrev w01 : List Bool := [false, true]

theorem rotA (k : Nat) (s : Tape) : cons false (rep k [true, false] s) = rep k w01 (cons false s) :=
  rep_rotate k [false] [true, false] w01 rfl s

theorem rot01 (k : Nat) (s : Tape) : cons false (cons true (rep k w01 s)) = rep k w01 (cons false (cons true s)) :=
  rep_rotate k w01 w01 w01 rfl s

/-- `0 11 (01)^m`, then blank: the counter. -/
def Ct (m : Nat) : Tape := cons false (cons true (cons true (rep m w01 blank)))

/-- The round start `0^∞ A> 0 11 (01)^n T`. -/
def Rs (n : Nat) (T : Tape) : Config := ⟨blank, cons false (cons true (cons true (rep n w01 T))), .A⟩

/-- Inside a round: `0^∞ C> (01)^k 0 11 (01)^j T`. -/
def X (k j : Nat) (T : Tape) : Config := ⟨blank, rep k w01 (cons false (cons true (cons true (rep j w01 T)))), .C⟩

/-! ## The sweeps -/

theorem pass_run (i : Nat) : ∀ k j T, Run (X k (j + 2 * i) T) (X (k + 3 * i) j T) := by
  induction i with
  | zero => intro k j T; exact ⟨0, rfl⟩
  | succ i ih =>
    intro k j T
    have h1 : Run (X k (j + 2 * i + 2) T) (X (k + 3) (j + 2 * i) T) :=
      run_of_eq (pass (j + 2 * i) k T) (by simp only [X, rep_succ, app_cons, app_nil, rot01])
    have h2 := ih (k + 3) j T
    rw [show j + 2 * (i + 1) = j + 2 * i + 2 by omega, show k + 3 * (i + 1) = k + 3 + 3 * i by omega]
    exact h1.trans h2

theorem start (n : Nat) (T : Tape) : Reaches (Rs n T) (X 1 n T) :=
  reaches_of_eq (entry n T) (by omega) (by simp only [X, rep_succ, rep_zero, app_cons, app_nil])

/-! ## The map -/

/-- Round starts, as counts. -/
inductive S2 where
  | r (n m : Nat)
  | z (k : Nat)
  deriving DecidableEq, Repr

def enc : S2 → Config
  | .r n m => Rs n (Ct m)
  | .z k => Rs k blank

/-- One round: `none` when it halts. -/
def next : S2 → Option S2
  | .r n m =>
    if n % 2 = 0 then some (.r (3 * (n / 2) + 2) (m + 2))
    else if m = 0 then some (.z (3 * (n / 2) + 6))
    else some (.r (3 * (n / 2) + 5) (m - 1))
  | .z k => if k % 2 = 0 then none else some (.r (3 * (k / 2) + 2) 1)

/-! ## A round -/

theorem round_even (p m : Nat) : Reaches (enc (.r (2 * p) m)) (enc (.r (3 * p + 2) (m + 2))) := by
  have h1 := start (2 * p) (Ct m)
  have h2 := pass_run p 1 0 (Ct m)
  rw [show 0 + 2 * p = 2 * p by omega] at h2
  refine h1.run (h2.trans (run_of_eq (endEven (1 + 3 * p) m) ?_))
  simp only [enc, Rs, Ct, rep_succ, rep_zero, app_cons, app_nil, rotA, rot01]
  rw [show 1 + 3 * p = 3 * p + 1 by omega]
  simp only [rep_succ, app_cons, app_nil, rot01]

theorem round_odd (p m : Nat) : Reaches (enc (.r (2 * p + 1) (m + 1))) (enc (.r (3 * p + 5) m)) := by
  have h1 := start (2 * p + 1) (Ct (m + 1))
  have h2 := pass_run p 1 1 (Ct (m + 1))
  rw [show 1 + 2 * p = 2 * p + 1 by omega] at h2
  refine h1.run (h2.trans (run_of_eq (endOdd (1 + 3 * p) m) ?_))
  simp only [enc, Rs, Ct, rep_succ, rep_zero, app_cons, app_nil, rotA, rot01]
  rw [show 1 + 3 * p = 3 * p + 1 by omega]
  simp only [rep_succ, app_cons, app_nil, rot01]

theorem round_odd0 (p : Nat) : Reaches (enc (.r (2 * p + 1) 0)) (enc (.z (3 * p + 6))) := by
  have h1 := start (2 * p + 1) (Ct 0)
  have h2 := pass_run p 1 1 (Ct 0)
  rw [show 1 + 2 * p = 2 * p + 1 by omega] at h2
  refine h1.run (h2.trans (run_of_eq (endOdd0 (1 + 3 * p)) ?_))
  simp only [enc, Rs, Ct, rep_succ, rep_zero, app_cons, app_nil, rotA, rot01]
  rw [show 1 + 3 * p = 3 * p + 1 by omega]
  simp only [rep_succ, app_cons, app_nil, rot01]

theorem round_zodd (p : Nat) : Reaches (enc (.z (2 * p + 1))) (enc (.r (3 * p + 2) 1)) := by
  have h1 := start (2 * p + 1) blank
  have h2 := pass_run p 1 1 blank
  rw [show 1 + 2 * p = 2 * p + 1 by omega] at h2
  refine h1.run (h2.trans (run_of_eq (zOdd (1 + 3 * p)) ?_))
  simp only [enc, Rs, Ct, rep_succ, rep_zero, app_cons, app_nil, rotA, rot01]
  rw [show 1 + 3 * p = 3 * p + 1 by omega]
  simp only [rep_succ, app_cons, app_nil, rot01]

theorem round_zeven (p : Nat) : TM.Halts trans (enc (.z (2 * p))) := by
  have h1 := start (2 * p) blank
  have h2 := pass_run p 1 0 blank
  rw [show 0 + 2 * p = 2 * p by omega] at h2
  refine halts_of_reaches (h1.run h2) ⟨_, _, zEven (1 + 3 * p), rfl⟩

theorem round {s s' : S2} (h : next s = some s') : Reaches (enc s) (enc s') := by
  cases s with
  | r n m =>
    simp only [next] at h
    obtain ⟨p, hp⟩ : ∃ p, n = 2 * p + n % 2 := ⟨n / 2, by omega⟩
    by_cases he : n % 2 = 0
    · rw [if_pos he] at h
      cases h
      rw [he] at hp
      subst hp
      have := round_even p m
      rw [show 2 * p + 0 = 2 * p by omega, show 2 * p / 2 = p by omega]
      exact this
    · rw [if_neg he] at h
      have h1 : n % 2 = 1 := by omega
      rw [h1] at hp
      subst hp
      rw [show (2 * p + 1) / 2 = p by omega] at h
      by_cases hm : m = 0
      · rw [if_pos hm] at h
        cases h
        subst hm
        exact round_odd0 p
      · rw [if_neg hm] at h
        cases h
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simpa using round_odd p m'
  | z k =>
    simp only [next] at h
    by_cases he : k % 2 = 0
    · rw [if_pos he] at h; cases h
    · rw [if_neg he] at h
      cases h
      obtain ⟨p, rfl⟩ : ∃ p, k = 2 * p + 1 := ⟨k / 2, by omega⟩
      rw [show (2 * p + 1) / 2 = p by omega]
      exact round_zodd p

theorem round_halt {s : S2} (h : next s = none) : TM.Halts trans (enc s) := by
  cases s with
  | r n m =>
    simp only [next] at h
    split at h
    · cases h
    · split at h <;> cases h
  | z k =>
    simp only [next] at h
    by_cases he : k % 2 = 0
    · obtain ⟨p, rfl⟩ : ∃ p, k = 2 * p := ⟨k / 2, by omega⟩
      exact round_zeven p
    · rw [if_neg he] at h; cases h

end H174634
