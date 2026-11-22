import Machine
import ResetMapRuns
import Twin29537
import TM.MapOrbit

/-!
# 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---: the reset map X' = floor(3X/2) + 1 (X even) or + 3 (X odd)

At a reset the tape is `Reset X T = 0^inf 1 B> 1 0 (10)^X T`.  The next phase counts the block `(10)^X` down
two at a time while a new block after it grows by three, and ends at the reset `Reset (f X) T'`, with

    f X = floor(3X/2) + 1   (X even)        f X = floor(3X/2) + 3   (X odd).

The *head part* of the tape, left of the tail `T`, does this for every `X`, whatever the tail holds.  The tail is
used only by *excursions*: the head reads the first cell of the tail in a state `q` with four known cells `u` on its
left, and later leaves to the left of those four cells in a state `q'`, having written four known cells `v` where
`u` was.  `Exc u q q' v T T'` says that this happens, for every tape on the left; `T'` is what the excursion leaves
of the tail.  Every phase step makes one excursion of the kind `Exc [0,0,1,1] A D [0,0,1,0]` (a carry into the tail)
and the reset makes a few others; which ones, in which order, is the predicate `Good X T K`.

**What is proved here** (kernel only, from the runs in `ResetMapRuns.lean`, written by `py/gen_resetmap.py`):

* `reset_map`: if `X ≥ 36` and the excursions of the phase are as in `Good X T K`, then the run goes from
  `Reset X T` to `Reset (f X) T'`, where `K T'`.  Nothing else about the tail is assumed: `X'` is `f X` exactly.
* `orbit`: by induction, `k` phases in a row (`GoodN k X T`) take the run to `Reset (f^k X) T'` in at least `k`
  steps (`fit`).
* `reach_own`, `reach_twin`: this machine's run from blank tape is at `Reset 40 T₀` after 8,577 steps; the twin
  1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD--- (this table started in state D, `Twin29537.lean`) is at `Reset 52 T₀'`
  after 6,412 steps.
* `never_halts_own`, `never_halts_twin`: if every phase's excursions are as in `Good` (`∀ k, GoodN k ...`), the
  machine never halts.  So both machines can halt only inside a tail excursion, and the halting question is
  exactly whether some excursion fails to come back the way the 3/2 map needs.

**What is not proved**: that the excursions come back.  An excursion is the carry of the counter through the
irregular tail; the README calls these the tail operators.  The hypotheses `Exc ...` are where the open part of the
problem now sits.  `py/gen_resetmap.py` checks on the direct runs that every excursion it meets (in 1,888 phase
steps and 22 resets and phase ends of the two machines) has the signature the hypotheses ask for.
-/

namespace H129771

open TM

set_option linter.unusedSimpArgs false

/-! ## Tapes in block form -/

/-- `(10)^n` in front of `X`. -/
abbrev P (n : Nat) (X : Tape) : Tape := rep n [true, false] X

theorem F1 (X : Tape) : cons true (cons false X) = P 1 X := rfl
theorem F2 (a b : Nat) (X : Tape) : P a (P b X) = P (a + b) X := (rep_add a b _ X).symm
theorem r4 (n : Nat) (X : Tape) : rep n [true, false, true, false] X = P (2 * n) X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2 * (n + 1) = 1 + (1 + 2 * n) by omega, ← F2, ← F2, ← ih]; rfl
theorem r4' (n : Nat) (X : Tape) : rep n [false, true, false, true] (cons false X) = cons false (P (2 * n) X) := by
  rw [← r4]; exact (rep_rotate n [false] [true, false, true, false] [false, true, false, true] rfl X).symm

theorem one_add' (n : Nat) : 1 + n = n + 1 := Nat.add_comm 1 n

/-- A left record of a phase: `0^inf B> 0 (10)^D 0 0 (10)^Y x T`. -/
def Rec (D Y : Nat) (x : Bool) (T : Tape) : Config :=
  ⟨blank, cons false (P D (cons false (cons false (P Y (cons x T))))), .B⟩

/-- The phase records the pieces meet: `D = 2d + 5` (the countdown), `Y = 2b + 11` (the growing block), `x = 1`. -/
def S (d b : Nat) (T : Tape) : Config := Rec (2 * d + 5) (2 * b + 11) true T

/-- A reset: `0^inf 1 B> 1 0 (10)^X T`. -/
def Reset (X : Nat) (T : Tape) : Config := ⟨cons true blank, cons true (cons false (P X T)), .B⟩

/-- An excursion into the tail `T`: entered in state `q` with the cells `u` (nearest first) on the left of the head,
left in state `q'` one cell left of those, which now hold `v` (in reading order), followed by `T'`; the same for every
tape `L` further left (the head never goes there). -/
def Exc (u : List Bool) (q q' : St) (v : List Bool) (T T' : Tape) : Prop :=
  ∃ n, ∀ L : Tape, steps n ⟨app u L, T, q⟩ = some ⟨tail L, cons (L 0) (app v T'), q'⟩

/-- Equal tapes in block form: unfold the definitions, merge the `10` pairs into blocks, add up the counts. -/
macro "tape_norm" : tactic => `(tactic| simp only [Reset, S, Rec, app_cons, app_nil, F1, F2, r4, r4', Nat.mul_add,
  Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, one_add'])

/-! ## The pieces

`re`, `ro`: a reset with `X` even / odd, up to the phase record with `Y = 13`.  `g`: two increments of a phase
(one excursion).  `e0`, `e1`: the end of a phase, from the countdown 5 / 7 to the next reset.  `Hname T K` lists the
excursions of the piece in order; `name_run` is the piece's run. -/

-- BEGIN GENERATED (py/gen_resetmap.py)
/-- The tail excursions of the piece `re_run`, in order, each from the tail the one before left; `K` receives the tail at the end. -/
def Hre (T : Tape) (K : Tape → Prop) : Prop :=
  ∃ T1, Exc [false, false, true, false] .A .B [true, false, false, true] T T1 ∧ ∃ T2, Exc [false, true, false, false] .E .C [false, true, false, true] T1 T2 ∧ ∃ T3, Exc [false, true, false, false] .E .C [false, true, false, true] T2 T3 ∧ ∃ T4, Exc [false, false, true, true] .A .D [false, true, false, true] T3 T4 ∧ ∃ T5, Exc [false, false, true, true] .A .D [false, true, false, true] T4 T5 ∧ K (app [true, false, true, false, true, false, true, false, true, false, true, false, true] T5)

theorem re_run (x : Nat) (T : Tape) (K : Tape → Prop) (h : Hre T K) :
    ∃ T', K T' ∧ Plus trans (Reset (2 * x + 36) T) (S (x + 11) 1 T') := by
  obtain ⟨T1, ⟨n1, e1⟩, T2, ⟨n2, e2⟩, T3, ⟨n3, e3⟩, T4, ⟨n4, e4⟩, T5, ⟨n5, e5⟩, hK⟩ := h
  exact ⟨_, hK, plus_of (steps_seq trans (re_s0 x T) (steps_seq trans (e1 (cons false (cons true (rep (x + 17) [true, false, false, true] (cons true (blank)))))) (steps_seq trans (re_s1 x T1) (steps_seq trans (e2 (cons true (cons false (cons false (cons true (rep (x + 17) [true, false, false, true] (cons true (cons false (blank))))))))) (steps_seq trans (re_s2 x T2) (steps_seq trans (e3 (cons true (cons false (cons false (cons true (cons true (cons true (rep (x + 17) [true, false, false, true] (cons true (cons false (blank))))))))))) (steps_seq trans (re_s3 x T3) (steps_seq trans (e4 (cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (rep (x + 15) [true, false, false, true] (cons true (cons false (cons false (cons true (cons true (cons false (blank))))))))))))))))))))))) (steps_seq trans (re_s4 x T4) (steps_seq trans (e5 (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (rep (x + 11) [true, false, false, true] (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (blank))))))))))))))))))))))))))))))))))))))))))))))) (re_s5 x T5)))))))))))
    (by tape_norm) (by tape_norm)⟩

/-- The tail excursions of the piece `ro_run`, in order, each from the tail the one before left; `K` receives the tail at the end. -/
def Hro (T : Tape) (K : Tape → Prop) : Prop :=
  ∃ T1, Exc [true, false, false, true] .B .D [true, false, true, true] T T1 ∧ ∃ T2, Exc [true, false, true, false] .C .A [true, false, true, false] T1 T2 ∧ ∃ T3, Exc [true, false, false, true] .B .D [true, false, true, true] T2 T3 ∧ ∃ T4, Exc [false, false, true, true] .A .D [false, true, false, true] T3 T4 ∧ ∃ T5, Exc [false, false, true, true] .A .D [false, true, false, true] T4 T5 ∧ K (app [true, false, true, false, true, false, true, false, true] T5)

theorem ro_run (x : Nat) (T : Tape) (K : Tape → Prop) (h : Hro T K) :
    ∃ T', K T' ∧ Plus trans (Reset (2 * x + 37) T) (S (x + 12) 1 T') := by
  obtain ⟨T1, ⟨n1, e1⟩, T2, ⟨n2, e2⟩, T3, ⟨n3, e3⟩, T4, ⟨n4, e4⟩, T5, ⟨n5, e5⟩, hK⟩ := h
  exact ⟨_, hK, plus_of (steps_seq trans (ro_s0 x T) (steps_seq trans (e1 (rep (x + 18) [true, false, false, true] (cons true (blank)))) (steps_seq trans (ro_s1 x T1) (steps_seq trans (e2 (cons false (cons true (cons true (rep (x + 17) [false, false, true, true] (cons false (cons false (cons true (cons true (cons false (blank))))))))))) (steps_seq trans (ro_s2 x T2) (steps_seq trans (e3 (cons true (cons true (cons true (rep (x + 17) [false, false, true, true] (cons false (cons false (cons true (cons true (cons false (blank))))))))))) (steps_seq trans (ro_s3 x T3) (steps_seq trans (e4 (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (rep (x + 16) [true, false, false, true] (cons true (cons false (cons false (cons true (cons true (cons false (blank))))))))))))))))))) (steps_seq trans (ro_s4 x T4) (steps_seq trans (e5 (cons false (cons false (cons true (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (rep (x + 12) [true, false, false, true] (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (blank))))))))))))))))))))))))))))))))))))))))))) (ro_s5 x T5)))))))))))
    (by tape_norm) (by tape_norm)⟩

/-- The tail excursions of the piece `g_run`, in order, each from the tail the one before left; `K` receives the tail at the end. -/
def Hg (T : Tape) (K : Tape → Prop) : Prop :=
  ∃ T1, Exc [false, false, true, true] .A .D [false, false, true, false] T T1 ∧ K (app [true, false, true, false] T1)

theorem g_run (d : Nat) (b : Nat) (T : Tape) (K : Tape → Prop) (h : Hg T K) :
    ∃ T', K T' ∧ Plus trans (S (d + 2) b T) (S d (b + 3) T') := by
  obtain ⟨T1, ⟨n1, e1⟩, hK⟩ := h
  exact ⟨_, hK, plus_of (steps_seq trans (g_s0 b d T) (steps_seq trans (e1 (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (rep (b) [true, false, false, true] (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons true (cons false (cons false (cons true (cons true (rep (d + 1) [false, false, true, true] (cons false (cons false (cons true (cons true (cons false (blank))))))))))))))))))))))))))))))))))))))))))) (g_s1 b d T1)))
    (by tape_norm) (by tape_norm)⟩

/-- The tail excursions of the piece `e0_run`, in order, each from the tail the one before left; `K` receives the tail at the end. -/
def He0 (T : Tape) (K : Tape → Prop) : Prop :=
  ∃ T1, Exc [false, false, true, true] .A .D [false, false, true, false] T T1 ∧ K (app [true, true, false, true, false] T1)

theorem e0_run (b : Nat) (T : Tape) (K : Tape → Prop) (h : He0 T K) :
    ∃ T', K T' ∧ Plus trans (S 0 b T) (Reset (2 * b + 20) T') := by
  obtain ⟨T1, ⟨n1, e1⟩, hK⟩ := h
  exact ⟨_, hK, plus_of (steps_seq trans (e0_s0 b T) (steps_seq trans (e1 (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (rep (b) [true, false, false, true] (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons true (cons false (cons false (cons true (cons true (cons false (blank)))))))))))))))))))))))))))))))))))))) (e0_s1 b T1)))
    (by tape_norm) (by tape_norm)⟩

/-- The tail excursions of the piece `e1_run`, in order, each from the tail the one before left; `K` receives the tail at the end. -/
def He1 (T : Tape) (K : Tape → Prop) : Prop :=
  ∃ T1, Exc [false, false, true, true] .A .D [false, false, true, false] T T1 ∧ ∃ T2, Exc [false, false, true, false] .A .B [true, false, true, false] T1 T2 ∧ K (app [false, true, false, true, false, true, false] T2)

theorem e1_run (b : Nat) (T : Tape) (K : Tape → Prop) (h : He1 T K) :
    ∃ T', K T' ∧ Plus trans (S 1 b T) (Reset (2 * b + 23) T') := by
  obtain ⟨T1, ⟨n1, e1⟩, T2, ⟨n2, e2⟩, hK⟩ := h
  exact ⟨_, hK, plus_of (steps_seq trans (e1_s0 b T) (steps_seq trans (e1 (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (rep (b) [true, false, false, true] (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (blank)))))))))))))))))))))))))))))))))))))))))) (steps_seq trans (e1_s1 b T1) (steps_seq trans (e2 (cons false (cons true (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (rep (b) [true, false, false, true] (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons true (cons false (blank)))))))))))))))))))))))))))))))))))))))))))))))))) (e1_s2 b T2)))))
    (by tape_norm) (by tape_norm)⟩
-- END GENERATED

/-! ## A phase -/

/-- `j` double increments of a phase, each with its carry. -/
def Gen : Nat → Tape → (Tape → Prop) → Prop
  | 0, T, K => K T
  | j + 1, T, K => Hg T (fun T' => Gen j T' K)

theorem gen_run : ∀ (j d b : Nat) (T : Tape) (K : Tape → Prop), Gen j T K →
    ∃ T', K T' ∧ Star trans (S (2 * j + d) b T) (S d (b + 3 * j) T')
  | 0, d, b, T, K, h => ⟨T, h, by simpa using Star.refl _⟩
  | j + 1, d, b, T, K, h => by
    obtain ⟨T1, h1, hp⟩ := g_run (2 * j + d) b T _ h
    obtain ⟨T2, hK, hs⟩ := gen_run j d (b + 3) T1 K h1
    refine ⟨T2, hK, ?_⟩
    have e1 : 2 * (j + 1) + d = 2 * j + d + 2 := by omega
    have e2 : b + 3 * (j + 1) = b + 3 + 3 * j := by omega
    rw [e1, e2]
    exact hp.star.trans hs

/-- The end of a phase from the countdown `2e + 5`. -/
def Hend (e : Nat) (T : Tape) (K : Tape → Prop) : Prop := if e % 2 = 0 then He0 T K else He1 T K

/-! ## The reset map -/

/-- The reset map. -/
def f (X : Nat) : Nat := 3 * X / 2 + (if X % 2 = 0 then 1 else 3)

/-- The excursions of the phase from `Reset X T`, in order; `K` receives the tail at the next reset. -/
def Good (X : Nat) (T : Tape) (K : Tape → Prop) : Prop :=
  if X % 2 = 0 then
    Hre T (fun T1 => Gen ((X / 2 - 18 + 11) / 2) T1 (fun T2 => Hend (X / 2 - 18 + 11) T2 K))
  else
    Hro T (fun T1 => Gen ((X / 2 - 18 + 12) / 2) T1 (fun T2 => Hend (X / 2 - 18 + 12) T2 K))

/-- **The reset map.**  From a reset with `X ≥ 36`, if the phase's excursions are as in `Good`, the run reaches the
next reset, and its block is `f X` long. -/
theorem reset_map (X : Nat) (hX : 36 ≤ X) (T : Tape) (K : Tape → Prop) (h : Good X T K) :
    ∃ T', K T' ∧ Plus trans (Reset X T) (Reset (f X) T') := by
  unfold Good at h
  split at h
  · rename_i hp
    obtain ⟨T1, h1, p1⟩ := re_run (X / 2 - 18) T _ h
    have e0 : X / 2 - 18 + 11 = 2 * ((X / 2 - 18 + 11) / 2) + (X / 2 - 18 + 11) % 2 := by omega
    obtain ⟨T2, h2, p2⟩ := gen_run _ ((X / 2 - 18 + 11) % 2) 1 T1 _ h1
    rw [← e0] at p2
    have eX : 2 * (X / 2 - 18) + 36 = X := by omega
    rw [eX] at p1
    unfold Hend at h2
    split at h2
    · rename_i he
      obtain ⟨T3, hK, p3⟩ := e0_run (1 + 3 * ((X / 2 - 18 + 11) / 2)) T2 K h2
      refine ⟨T3, hK, ?_⟩
      have es : (X / 2 - 18 + 11) % 2 = 0 := he
      rw [es] at p2
      have ef : 2 * (1 + 3 * ((X / 2 - 18 + 11) / 2)) + 20 = f X := by unfold f; split <;> omega
      rw [ef] at p3
      exact (p1.trans_star p2).trans p3
    · rename_i he
      obtain ⟨T3, hK, p3⟩ := e1_run (1 + 3 * ((X / 2 - 18 + 11) / 2)) T2 K h2
      refine ⟨T3, hK, ?_⟩
      have es : (X / 2 - 18 + 11) % 2 = 1 := by omega
      rw [es] at p2
      have ef : 2 * (1 + 3 * ((X / 2 - 18 + 11) / 2)) + 23 = f X := by unfold f; split <;> omega
      rw [ef] at p3
      exact (p1.trans_star p2).trans p3
  · rename_i hp
    obtain ⟨T1, h1, p1⟩ := ro_run (X / 2 - 18) T _ h
    have e0 : X / 2 - 18 + 12 = 2 * ((X / 2 - 18 + 12) / 2) + (X / 2 - 18 + 12) % 2 := by omega
    obtain ⟨T2, h2, p2⟩ := gen_run _ ((X / 2 - 18 + 12) % 2) 1 T1 _ h1
    rw [← e0] at p2
    have eX : 2 * (X / 2 - 18) + 37 = X := by omega
    rw [eX] at p1
    unfold Hend at h2
    split at h2
    · rename_i he
      obtain ⟨T3, hK, p3⟩ := e0_run (1 + 3 * ((X / 2 - 18 + 12) / 2)) T2 K h2
      refine ⟨T3, hK, ?_⟩
      have es : (X / 2 - 18 + 12) % 2 = 0 := he
      rw [es] at p2
      have ef : 2 * (1 + 3 * ((X / 2 - 18 + 12) / 2)) + 20 = f X := by unfold f; split <;> omega
      rw [ef] at p3
      exact (p1.trans_star p2).trans p3
    · rename_i he
      obtain ⟨T3, hK, p3⟩ := e1_run (1 + 3 * ((X / 2 - 18 + 12) / 2)) T2 K h2
      refine ⟨T3, hK, ?_⟩
      have es : (X / 2 - 18 + 12) % 2 = 1 := by omega
      rw [es] at p2
      have ef : 2 * (1 + 3 * ((X / 2 - 18 + 12) / 2)) + 23 = f X := by unfold f; split <;> omega
      rw [ef] at p3
      exact (p1.trans_star p2).trans p3

/-! ## Many phases -/

/-- `f` applied `k` times. -/
def fit : Nat → Nat → Nat
  | 0, X => X
  | k + 1, X => fit k (f X)

/-- `k` phases in a row whose excursions are as in `Good`. -/
def GoodN : Nat → Nat → Tape → Prop
  | 0, _, _ => True
  | k + 1, X, T => Good X T (fun T' => GoodN k (f X) T')

theorem le_f (X : Nat) : X ≤ f X := by unfold f; split <;> omega

theorem orbit : ∀ (k X : Nat) (T : Tape), 36 ≤ X → GoodN k X T →
    ∃ n T', k ≤ n ∧ steps n (Reset X T) = some (Reset (fit k X) T')
  | 0, X, T, _, _ => ⟨0, T, Nat.le_refl _, rfl⟩
  | k + 1, X, T, hX, h => by
    obtain ⟨T1, h1, ⟨n, hn⟩⟩ := reset_map X hX T _ h
    obtain ⟨m, T2, hm, hs⟩ := orbit k (f X) T1 (Nat.le_trans hX (le_f X)) h1
    exact ⟨n + 1 + m, T2, by omega, steps_seq trans hn hs⟩

/-- If `GoodN k` holds for every `k` from a reached reset, the run never halts. -/
theorem never_halts_of {c : Config} {N X : Nat} {T : Tape} (hX : 36 ≤ X) (h0 : steps N c = some (Reset X T))
    (h : ∀ k, GoodN k X T) : ¬ Halts trans c := by
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun m => ∃ c', steps m c = some c')
  · intro n
    obtain ⟨m, T', hm, hs⟩ := orbit n X T hX (h n)
    exact ⟨N + m, by omega, _, steps_seq trans h0 hs⟩
  · intro m hm; exact hm

/-! ## The two machines -/

theorem app_falses (k : Nat) : app (List.replicate k false) blank = blank := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, app_cons, ih]; exact cons_false_blank

-- BEGIN REACH (py/gen_resetmap.py)
/-- The tail at the first reset with X >= 36 of this machine. -/
def T0own : Tape := app [true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, false, true, false, true, false, false, false, true, false, true, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, true, false] blank

theorem fsteps_own : fsteps 8577 (FCfg.blank .A) = some ⟨[true], [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, false, true, false, true, false, false, false, true, false, true, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, true, false], .B⟩ := by
  decide +kernel

/-- This machine is at `Reset 40 T0own` after 8577 steps from blank tape. -/
theorem reach_own : steps 8577 (blankCfg .A) = some (Reset 40 T0own) := by
  refine (blank_reaches trans fsteps_own).trans ?_
  show some (⟨app (true :: List.replicate 0 false) blank, _, _⟩ : Config) = _
  rw [app_cons, app_falses]
  rfl

/-- The tail at the first reset with X >= 36 of the twin (this table started in D). -/
def T0twin : Tape := app [true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, true, false, true, true, false, true, false, false, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false, true, false] blank

theorem fsteps_twin : fsteps 14638 (FCfg.blank .D) = some ⟨[true], [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, true, false, true, true, false, true, false, false, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false, true, false], .B⟩ := by
  decide +kernel

/-- The twin (this table started in D) is at `Reset 52 T0twin` after 14638 steps from blank tape. -/
theorem reach_twin : steps 14638 (blankCfg .D) = some (Reset 52 T0twin) := by
  refine (blank_reaches trans fsteps_twin).trans ?_
  show some (⟨app (true :: List.replicate 0 false) blank, _, _⟩ : Config) = _
  rw [app_cons, app_falses]
  rfl
-- END REACH

/-- **This machine** never halts if every phase's tail excursions come back as `Good` says. -/
theorem never_halts_own (h : ∀ k, GoodN k 40 T0own) : ¬ HaltsFromBlank :=
  never_halts_of (by omega) reach_own h

/-- **The twin** 1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD--- never halts if every phase's tail excursions come back
as `Good` says. -/
theorem never_halts_twin (h : ∀ k, GoodN k 52 T0twin) : ¬ Halts H29537.trans (blankCfg H29537.St.A) := by
  rw [twin_halts_iff]
  exact never_halts_of (by omega) reach_twin h

end H129771
