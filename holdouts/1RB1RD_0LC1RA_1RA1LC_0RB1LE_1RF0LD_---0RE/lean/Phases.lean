import Pieces
import Norm

/-!
# 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE: the whole phase map

Three kinds of configurations (tapes left to right, `S>` the head in state S, blank tape around):

* `PE x z` = `E>0 (10)^x 1^z`, the head at the left end;
* `PR x y` = `(10)^x 1^y 0 B>0`, the head on the blank cell right of the tape;
* `PQ m k t` = `(10)^m 1 D>0 0 (10)^k 1^t`, the bounce frame inside a doubling.

`next` is the map from one of them to the next one the machine reaches, and `next_sound` proves that the machine
really goes there, in every case and for all parameters (each case is one symbolic run of `Pieces.lean`, or the
bounce lemma `q_rounds` built from one of them by induction, glued by `tape_eq`).  `next` is `none` exactly at
`PE x 0` and `PE x 1`, and those halt (`e_halts`).  The run from blank tape reaches `PR 0 2` (`init_r`).

So the machine halts from blank tape if and only if iterating `next` from `PR 0 2` reaches `PE x 0` or `PE x 1`
(`halts_iff`, both directions), and `no_halt_phases` checks by `native_decide` that the first 100000000 phases do not.
Whether the iteration ever gets there is open.
-/

namespace H70028

open TM

/-- `E>0 (10)^x 1^z`. -/
def PE (x z : Nat) : Config := ⟨blank, cons false (rep x [true, false] (rep z [true] blank)), .E⟩

/-- `(10)^x 1^y 0 B>0`. -/
def PR (x y : Nat) : Config := ⟨cons false (rep y [true] (rep x [false, true] blank)), blank, .B⟩

/-- `(10)^m 1 D>0 0 (10)^k 1^t`. -/
def PQ (m k t : Nat) : Config :=
  ⟨cons true (rep m [false, true] blank), cons false (cons false (rep k [true, false] (rep t [true] blank))), .D⟩

/-- A phase. -/
inductive Ph where
  | e (x z : Nat)
  | r (x y : Nat)
  | q (m k t : Nat)
  deriving DecidableEq, Repr

def Ph.cfg : Ph → Config
  | .e x z => PE x z
  | .r x y => PR x y
  | .q m k t => PQ m k t

/-- The phase map.  Bounces are taken all at once: `b = min (m + 1) ((t + 2) / 2)` of them, until no `10` is left on
the left or the 1s on the right are down to one or two. -/
def next : Ph → Option Ph
  | .e _ 0 => none
  | .e _ 1 => none
  | .e x (z + 2) => some (.q x 0 z)
  | .q (m + 1) k (t + 3) =>
      some (.q (m + 1 - min (m + 1) ((t + 2) / 2)) (k + 2 * min (m + 1) ((t + 2) / 2)) (t + 3 - 2 * min (m + 1) ((t + 2) / 2)))
  | .q 0 k (t + 5) => some (.e (k + 4) (t + 1))
  | .q 0 k 4 => some (.r 0 (2 * k + 8))
  | .q 0 k 3 => some (.e 1 (2 * k + 7))
  | .q m k 2 => some (.r m (2 * k + 5))
  | .q 0 k 1 => some (.e 1 (2 * k + 4))
  | .q 1 k 1 => some (.e 3 (2 * k + 2))
  | .q (m + 2) k 1 => some (.q m 1 (2 * k + 4))
  | .q 0 k 0 => some (.e 1 (2 * k + 2))
  | .q 1 0 0 => some (.r 0 6)
  | .q 1 (k + 1) 0 => some (.e 3 (2 * k + 2))
  | .q (m + 2) k 0 => some (.q m 1 (2 * k + 2))
  | .r 0 0 => some (.e 1 1)
  | .r 0 (y + 1) => some (.e 1 (y + 2))
  | .r 1 0 => some (.e 1 5)
  | .r 1 1 => some (.r 0 6)
  | .r 1 2 => some (.e 3 1)
  | .r 1 (y + 3) => some (.e 3 (y + 2))
  | .r (x + 2) 0 => some (.q x 1 1)
  | .r (x + 2) (y + 1) => some (.q x 1 (y + 2))

/-- One bounce, `PQ (m+1) k (t+3)` to `PQ m (k+2) (t+1)`. -/
theorem q_round (m k t : Nat) : ∃ n, 0 < n ∧ steps n (PQ (m + 1) k (t + 3)) = some (PQ m (k + 2) (t + 1)) :=
  ⟨_, by omega, steps_eq_of (pc_round k m t) (cfg_eq (by tape_eq) (by tape_eq)) (cfg_eq (by tape_eq) (by tape_eq))⟩

/-- `b` bounces. -/
theorem q_rounds (b : Nat) : ∀ m k t, ∃ n, b ≤ n ∧ steps n (PQ (m + b) k (t + 2 * b + 1)) = some (PQ m (k + 2 * b) (t + 1)) := by
  induction b with
  | zero => intro m k t; exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ b ih =>
    intro m k t
    obtain ⟨n1, p1, h1⟩ := q_round (m + b) k (t + 2 * b)
    obtain ⟨n2, p2, h2⟩ := ih m (k + 2) t
    rw [show m + b + 1 = m + (b + 1) by omega, show t + 2 * b + 3 = t + 2 * (b + 1) + 1 by omega] at h1
    rw [show k + 2 + 2 * b = k + 2 * (b + 1) by omega] at h2
    exact ⟨n1 + n2, by omega, steps_seq trans h1 h2⟩

macro "piece" t:term:max : tactic =>
  `(tactic| focus
    simp only [next, Option.some.injEq] at *
    subst_vars
    simp only [Ph.cfg, PE, PR, PQ]
    refine ⟨_, ?_, steps_eq_of ($t) (cfg_eq (by tape_eq) (by tape_eq)) (cfg_eq (by tape_eq) (by tape_eq))⟩
    omega)

theorem next_sound : ∀ p p', next p = some p' → ∃ n, 0 < n ∧ steps n p.cfg = some p'.cfg
  | .e _ 0, _, h => by simp [next] at h
  | .e _ 1, _, h => by simp [next] at h
  | .e x (z + 2), _, h => by piece (pc_e x z)
  | .q (m + 1) k (t + 3), _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    have hk1 : min (m + 1) ((t + 2) / 2) ≤ m + 1 := Nat.min_le_left _ _
    have hk2 : 2 * min (m + 1) ((t + 2) / 2) ≤ t + 2 := by
      have := Nat.min_le_right (m + 1) ((t + 2) / 2); omega
    have hk0 : 1 ≤ min (m + 1) ((t + 2) / 2) := Nat.le_min.mpr ⟨by omega, by omega⟩
    obtain ⟨n, hn, h⟩ := q_rounds (min (m + 1) ((t + 2) / 2)) (m + 1 - min (m + 1) ((t + 2) / 2)) k
      (t + 2 - 2 * min (m + 1) ((t + 2) / 2))
    refine ⟨n, by omega, steps_eq_of h ?_ ?_⟩
    · simp only [Ph.cfg]; congr 1 <;> omega
    · simp only [Ph.cfg]; congr 1; omega
  | .q 0 k (t + 5), _, h => by piece (pc_end k t)
  | .q 0 k 4, _, h => by piece (pc_end4 k)
  | .q 0 k 3, _, h => by piece (pc_end3 k)
  | .q m k 2, _, h => by piece (pc_t2 k m)
  | .q 0 k 1, _, h => by piece (pc_t1z k)
  | .q 1 k 1, _, h => by piece (pc_t1o k)
  | .q (m + 2) k 1, _, h => by piece (pc_t1 k m)
  | .q 0 k 0, _, h => by piece (pc_t0z k)
  | .q 1 0 0, _, h => by piece pc_t0oz
  | .q 1 (k + 1) 0, _, h => by piece (pc_t0o k)
  | .q (m + 2) k 0, _, h => by piece (pc_t0 k m)
  | .r 0 0, _, h => by piece pc_r00
  | .r 0 (y + 1), _, h => by piece (pc_r0 y)
  | .r 1 0, _, h => by piece pc_r10
  | .r 1 1, _, h => by piece pc_r11
  | .r 1 2, _, h => by piece pc_r12
  | .r 1 (y + 3), _, h => by piece (pc_r1 y)
  | .r (x + 2) 0, _, h => by piece (pc_rx0 x)
  | .r (x + 2) (y + 1), _, h => by piece (pc_rx x y)

/-- `k` steps of the phase map. -/
def iter : Nat → Ph → Option Ph
  | 0, p => some p
  | k + 1, p => (next p).bind (iter k)

theorem reach_iter : ∀ k p p', iter k p = some p' → ∃ n, k ≤ n ∧ steps n p.cfg = some p'.cfg
  | 0, p, p', h => by simp only [iter, Option.some.injEq] at h; subst h; exact ⟨0, Nat.le_refl 0, rfl⟩
  | k + 1, p, p', h => by
    simp only [iter] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp, Option.bind_some] at h
      obtain ⟨n1, p1, h1⟩ := next_sound p q hp
      obtain ⟨n2, p2, h2⟩ := reach_iter k q p' h
      exact ⟨n1 + n2, by omega, steps_seq trans h1 h2⟩

/-- The run from blank tape reaches `PR 0 2`. -/
theorem init_r : steps 6 init = some (Ph.r 0 2).cfg :=
  steps_eq_of pc_init rfl (cfg_eq (by tape_eq) (by tape_eq))

/-- `PE x 0` and `PE x 1` halt. -/
theorem e_halts (x z : Nat) (hz : z ≤ 1) : TM.Halts trans (PE x z) := by
  rcases (show z = 0 ∨ z = 1 by omega) with rfl | rfl
  · exact ⟨_, _, pc_eh0 x, rfl⟩
  · exact ⟨_, _, pc_eh1 x, rfl⟩

/-- `next` fails only at `PE x 0` and `PE x 1`. -/
theorem next_none : ∀ p, next p = none → ∃ x z, z ≤ 1 ∧ p = .e x z
  | .e x 0, _ => ⟨x, 0, by omega, rfl⟩
  | .e x 1, _ => ⟨x, 1, by omega, rfl⟩
  | .e _ (_ + 2), h => by simp [next] at h
  | .q (_ + 1) _ (_ + 3), h => by simp [next] at h
  | .q 0 _ (_ + 5), h | .q 0 _ 4, h | .q 0 _ 3, h | .q _ _ 2, h | .q 0 _ 1, h | .q 1 _ 1, h | .q (_ + 2) _ 1, h
  | .q 0 _ 0, h | .q 1 0 0, h | .q 1 (_ + 1) 0, h | .q (_ + 2) _ 0, h => by simp [next] at h
  | .r 0 0, h | .r 0 (_ + 1), h | .r 1 0, h | .r 1 1, h | .r 1 2, h | .r 1 (_ + 3), h | .r (_ + 2) 0, h
  | .r (_ + 2) (_ + 1), h => by simp [next] at h

theorem iter_succ (k : Nat) (p p' : Ph) (h : iter k p = some p') : iter (k + 1) p = next p' := by
  induction k generalizing p with
  | zero => simp only [iter, Option.some.injEq] at h; subst h; simp [iter]
  | succ k ih =>
    simp only [iter] at h ⊢
    cases hp : next p with
    | none => simp [hp] at h
    | some q => simp only [hp, Option.bind_some] at h ⊢; exact ih q h

/-- **The machine halts from blank tape if and only if the phase map, iterated from `PR 0 2`, reaches `PE x z`
with `z ≤ 1`.** -/
theorem halts_iff :
    HaltsFromBlank ↔ ∃ k x z, z ≤ 1 ∧ iter k (.r 0 2) = some (.e x z) := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    have hall : ∀ k, ∃ p, iter k (.r 0 2) = some p := by
      intro k
      induction k with
      | zero => exact ⟨_, rfl⟩
      | succ k ih =>
        obtain ⟨p, hp⟩ := ih
        rw [iter_succ k _ p hp]
        cases hn : next p with
        | some q => exact ⟨q, rfl⟩
        | none =>
          obtain ⟨x, z, hz, rfl⟩ := next_none p hn
          exact absurd ⟨k, x, z, hz, hp⟩ hno
    apply TM.not_halts_of_forall trans _ hh
    apply TM.forall_of_unbounded trans (fun m => ∃ c', steps m init = some c')
    · intro n
      obtain ⟨p, hp⟩ := hall n
      obtain ⟨m, hm, h⟩ := reach_iter n _ p hp
      exact ⟨6 + m, by omega, _, steps_seq trans init_r h⟩
    · exact fun _ h => h
  · rintro ⟨k, x, z, hz, h⟩
    obtain ⟨n, -, h1⟩ := reach_iter k _ _ h
    obtain ⟨m, c', h2, h3⟩ := e_halts x z hz
    exact ⟨6 + (n + m), c', steps_seq trans init_r (steps_seq trans h1 h2), h3⟩

/-- `next` is defined `k` times in a row from `p`. -/
def okFor : Nat → Ph → Bool
  | 0, _ => true
  | k + 1, p => match next p with
    | none => false
    | some q => okFor k q

theorem okFor_sound : ∀ k p, okFor k p = true → ∀ j, j < k → ∀ x z, iter j p = some (.e x z) → 2 ≤ z
  | 0, _, _, j, hj, _, _, _ => absurd hj (Nat.not_lt_zero j)
  | k + 1, p, h, j, hj, x, z, hi => by
    simp only [okFor] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp] at h
      cases j with
      | zero =>
        simp only [iter, Option.some.injEq] at hi; subst hi
        rcases z with _ | _ | z
        · simp [next] at hp
        · simp [next] at hp
        · omega
      | succ j =>
        simp only [iter, hp, Option.bind_some] at hi
        exact okFor_sound k q h j (by omega) x z hi

/-- The first 100000000 phases of the run from blank tape contain no `PE x 0` or `PE x 1`, so by `halts_iff` a halt,
if any, comes later. -/
theorem no_halt_phases : ∀ j, j < 100000000 → ∀ x z, iter j (.r 0 2) = some (.e x z) → 2 ≤ z :=
  okFor_sound _ _ (by native_decide)

/-! ## The parity classes and the all-ones moments

`Even` phases (`PE x z` with `z` even and `z ≥ 2`, `PR x y` with `x ≥ 1` and `y` odd, `PQ m k t` with `t` even) lead only to `Even` phases or to all-ones tapes `PR 0 n` (`even_next`), so from an `Even` phase the machine cannot halt
before the tape is next all ones (`even_safe`).  From an all-ones tape `PR 0 n` the run reaches, within a few
phases, either a halting phase, an `Even` phase or another all-ones tape; `fate` follows it there, and
`fatal_list` checks by `native_decide`, for every `n < 100000`, that it halts first exactly when `n` is `0` and `20 * 2^k - 2k - 12` (`n = 8, 26, 64, 142, 300, ...`).  `ones_safe` and `ones_fatal` turn that into statements
about the machine. -/

def isEven : Ph → Bool
  | .e _ z => decide (z % 2 = 0 ∧ 2 ≤ z)
  | .r x y => decide (1 ≤ x ∧ y % 2 = 1)
  | .q _ _ t => decide (t % 2 = 0)

def isOnes : Ph → Bool
  | .r x _ => x == 0
  | _ => false

theorem even_next (p p' : Ph) (he : isEven p = true) (h : next p = some p') : isEven p' = true ∨ isOnes p' = true := by
  unfold next at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [isEven, isOnes] at he ⊢ <;> omega

theorem iter_add : ∀ a b p, iter (a + b) p = (iter a p).bind (iter b)
  | 0, b, p => by simp [iter]
  | a + 1, b, p => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [iter]
    cases next p with
    | none => rfl
    | some q => simp only [Option.bind_some]; exact iter_add a b q

/-- From an `Even` phase, a halting phase comes only after an all-ones tape. -/
theorem even_safe : ∀ k p x z, isEven p = true → z ≤ 1 → iter k p = some (.e x z) →
    ∃ i, 0 < i ∧ i < k ∧ ∃ n, iter i p = some (.r 0 n)
  | 0, p, x, z, he, hz, h => by
    simp only [iter, Option.some.injEq] at h; subst h; simp [isEven] at he; omega
  | k + 1, p, x, z, he, hz, h => by
    simp only [iter] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp, Option.bind_some] at h
      rcases even_next p q he hp with hq | hq
      · obtain ⟨i, hi0, hik, n, hn⟩ := even_safe k q x z hq hz h
        exact ⟨i + 1, by omega, by omega, n, by simp only [iter, hp, Option.bind_some]; exact hn⟩
      · cases q with
        | r x0 n =>
          simp only [isOnes, beq_iff_eq] at hq; subst hq
          cases k with
          | zero => simp [iter] at h
          | succ k => exact ⟨1, by omega, by omega, n, by simp [iter, hp]⟩
        | e _ _ | q _ _ _ => simp [isOnes] at hq

/-- Follow the run from `p` (at most `f` phases) to a halting phase (`some true`) or to an `Even` phase or an
all-ones tape (`some false`). -/
def fate : Nat → Ph → Option Bool
  | 0, _ => none
  | f + 1, p => match next p with
    | none => some true
    | some q => if isEven q || isOnes q then some false else fate f q

theorem fate_true : ∀ f p, fate f p = some true → ∃ k x z, z ≤ 1 ∧ iter k p = some (.e x z)
  | 0, _, h => by simp [fate] at h
  | f + 1, p, h => by
    simp only [fate] at h
    cases hp : next p with
    | none => obtain ⟨x, z, hz, rfl⟩ := next_none p hp; exact ⟨0, x, z, hz, rfl⟩
    | some q =>
      simp only [hp] at h
      split at h
      · simp at h
      · obtain ⟨k, x, z, hz, hk⟩ := fate_true f q h
        exact ⟨k + 1, x, z, hz, by simp only [iter, hp, Option.bind_some]; exact hk⟩

theorem fate_false : ∀ f p, fate f p = some false → ∃ i q, 0 < i ∧ iter i p = some q ∧ (isEven q = true ∨ isOnes q = true)
  | 0, _, h => by simp [fate] at h
  | f + 1, p, h => by
    simp only [fate] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp] at h
      split at h
      · rename_i hq
        exact ⟨1, q, by omega, by simp [iter, hp], by simpa using hq⟩
      · obtain ⟨i, r, hi, hr, hc⟩ := fate_false f q h
        exact ⟨i + 1, r, by omega, by simp only [iter, hp, Option.bind_some]; exact hr, hc⟩

/-- A halting phase is the last one: nothing comes after it. -/
theorem iter_after_halt (k j : Nat) (p : Ph) (x z : Nat) (hz : z ≤ 1) (h : iter k p = some (.e x z)) (hj : k < j) :
    iter j p = none := by
  obtain ⟨d, rfl⟩ : ∃ d, j = k + (d + 1) := ⟨j - k - 1, by omega⟩
  rw [iter_add, h]
  rcases (show z = 0 ∨ z = 1 by omega) with rfl | rfl <;> simp [iter, next]

/-- The all-ones lengths that halt before the tape is next all ones: `0` and `20 * 2^k - 2k - 12` (`n = 8, 26, 64, 142, 300, ...`). -/
def fatalLen (n : Nat) : Bool := n == 0 || (List.range 64).any (fun k => n + 2 * k + 12 == 20 * 2 ^ k)

/-- Checked for every `n < 100000`, at most 128 phases each. -/
theorem fatal_list : (List.range 100000).all (fun n => fate 128 (.r 0 n) == some (fatalLen n)) = true := by native_decide

/-- If `n < 100000` is a fatal length, the run from the all-ones tape `PR 0 n` halts. -/
theorem ones_fatal (n : Nat) (hn : n < 100000) (hf : fatalLen n = true) : TM.Halts trans (PR 0 n) := by
  have h := List.all_eq_true.mp fatal_list n (List.mem_range.mpr hn)
  rw [hf] at h
  obtain ⟨k, x, z, hz, hk⟩ := fate_true 128 _ (by simpa using h)
  obtain ⟨m, -, h1⟩ := reach_iter k _ _ hk
  obtain ⟨m', c', h2, h3⟩ := e_halts x z hz
  exact ⟨m + m', c', steps_seq trans h1 h2, h3⟩

/-- If `n < 100000` is not a fatal length, the run from the all-ones tape `PR 0 n` cannot halt before the tape is
all ones again. -/
theorem ones_safe (n : Nat) (hn : n < 100000) (hf : fatalLen n = false) :
    ∀ k x z, z ≤ 1 → iter k (.r 0 n) = some (.e x z) → ∃ i, 0 < i ∧ i < k ∧ ∃ m, iter i (.r 0 n) = some (.r 0 m) := by
  intro k x z hz hk
  have h := List.all_eq_true.mp fatal_list n (List.mem_range.mpr hn)
  rw [hf] at h
  obtain ⟨i, q, hi, hq, hc⟩ := fate_false 128 _ (by simpa using h)
  have hik : i ≤ k := by
    apply Classical.byContradiction; intro hlt
    rw [iter_after_halt k i _ x z hz hk (by omega)] at hq; simp at hq
  have hik' : i < k := by
    rcases Nat.lt_or_eq_of_le hik with h' | rfl
    · exact h'
    · rw [hk] at hq; simp only [Option.some.injEq] at hq; subst hq
      simp [isEven, isOnes] at hc; omega
  obtain ⟨d, rfl⟩ : ∃ d, k = i + d := ⟨k - i, by omega⟩
  rw [iter_add, hq, Option.bind_some] at hk
  rcases hc with he | ho
  · obtain ⟨i', hi'0, hi'd, m, hm⟩ := even_safe d q x z he hz hk
    exact ⟨i + i', by omega, by omega, m, by rw [iter_add, hq, Option.bind_some]; exact hm⟩
  · cases q with
    | r x0 m => simp only [isOnes, beq_iff_eq] at ho; subst ho; exact ⟨i, hi, hik', m, hq⟩
    | e _ _ | q _ _ _ => simp [isOnes] at ho

end H70028
