import Pieces
import Norm

/-!
# 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE: the whole phase map

Three kinds of configurations (tapes left to right, `S>` the head in state S, blank tape around):

* `PE x z` = `E>0 (10)^x 1^z`, the head at the left end;
* `PA x y` = `(10)^x 1^y A>0`, the head on the blank cell right of the tape (`PA 0 0` is the blank tape);
* `PQ m j t` = `(10)^m 1 D>0 0 (1010)^j 1^t`, the bounce frame inside a doubling.

`next` is the map from one of them to the next one the machine reaches, and `next_sound` proves that the machine
really goes there, in every case and for all parameters (each case is one symbolic run of `Pieces.lean`, or the
bounce lemma `q_rounds` built from one of them by induction, glued by `tape_eq`).  `next` is `none` exactly at
`PE x 0` and `PE x 1`, and those halt (`e_halts`).  The run from blank tape starts at `PA 0 0`.

So the machine halts from blank tape if and only if iterating `next` from `PA 0 0` reaches `PE x 0` or `PE x 1`
(`halts_iff`, both directions), and `no_halt_phases` checks by `native_decide` that the first 100000000 phases do not.
Whether the iteration ever gets there is open.
-/

namespace H35167

open TM

/-- `E>0 (10)^x 1^z`. -/
def PE (x z : Nat) : Config := ⟨blank, cons false (rep x [true, false] (rep z [true] blank)), .E⟩

/-- `(10)^x 1^y A>0`. -/
def PA (x y : Nat) : Config := ⟨rep y [true] (rep x [false, true] blank), blank, .A⟩

/-- `(10)^m 1 D>0 0 (1010)^j 1^t`. -/
def PQ (m j t : Nat) : Config :=
  ⟨cons true (rep m [false, true] blank), cons false (cons false (rep j [true, false, true, false] (rep t [true] blank))), .D⟩

/-- A phase. -/
inductive Ph where
  | e (x z : Nat)
  | a (x y : Nat)
  | q (m j t : Nat)
  deriving DecidableEq, Repr

def Ph.cfg : Ph → Config
  | .e x z => PE x z
  | .a x y => PA x y
  | .q m j t => PQ m j t

/-- The phase map.  Bounces are taken all at once: `k = min (m + 1) ((t + 2) / 2)` of them, until no `10` is left on
the left or the 1s on the right are down to one or two. -/
def next : Ph → Option Ph
  | .e _ 0 => none
  | .e _ 1 => none
  | .e x (z + 2) => some (.q x 0 z)
  | .q (m + 1) j (t + 3) =>
      some (.q (m + 1 - min (m + 1) ((t + 2) / 2)) (j + min (m + 1) ((t + 2) / 2)) (t + 3 - 2 * min (m + 1) ((t + 2) / 2)))
  | .q 0 j (t + 5) => some (.e (2 * j + 4) (t + 1))
  | .q 0 j 4 => some (.a 0 (4 * j + 9))
  | .q 0 j 3 => some (.a 0 (4 * j + 7))
  | .q m j 2 => some (.a m (4 * j + 6))
  | .q m j 1 => some (.a m (4 * j + 4))
  | .q (m + 2) j 0 => some (.q m 0 (4 * j + 4))
  | .q 1 j 0 => some (.e 2 (4 * j + 2))
  | .q 0 0 0 => some (.a 0 7)
  | .q 0 (j + 1) 0 => some (.e 3 (4 * j + 4))
  | .a (x + 2) y => some (.q x 0 (y + 2))
  | .a 1 0 => some (.a 0 5)
  | .a 1 (n + 1) => some (.e 2 (n + 1))
  | .a 0 0 => some (.a 0 4)
  | .a 0 1 => some (.e 3 3)
  | .a 0 2 => some (.a 0 7)
  | .a 0 (n + 3) => some (.e 3 (n + 1))

/-- One bounce, `PQ (m+1) j (t+3)` to `PQ m (j+1) (t+1)`. -/
theorem q_round (m j t : Nat) : ∃ n, 0 < n ∧ steps n (PQ (m + 1) j (t + 3)) = some (PQ m (j + 1) (t + 1)) :=
  ⟨_, by omega, steps_eq_of (pc_round j m t) (cfg_eq (by tape_eq) (by tape_eq)) (cfg_eq (by tape_eq) (by tape_eq))⟩

/-- `k` bounces. -/
theorem q_rounds (k : Nat) : ∀ m j t, ∃ n, k ≤ n ∧ steps n (PQ (m + k) j (t + 2 * k + 1)) = some (PQ m (j + k) (t + 1)) := by
  induction k with
  | zero => intro m j t; exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ k ih =>
    intro m j t
    obtain ⟨n1, p1, h1⟩ := q_round (m + k) j (t + 2 * k)
    obtain ⟨n2, p2, h2⟩ := ih m (j + 1) t
    rw [show m + k + 1 = m + (k + 1) by omega, show t + 2 * k + 3 = t + 2 * (k + 1) + 1 by omega] at h1
    rw [show j + 1 + k = j + (k + 1) by omega] at h2
    exact ⟨n1 + n2, by omega, steps_seq trans h1 h2⟩

macro "piece" t:term:max : tactic =>
  `(tactic| focus
    simp only [next, Option.some.injEq] at *
    subst_vars
    simp only [Ph.cfg, PE, PA, PQ]
    refine ⟨_, ?_, steps_eq_of ($t) (cfg_eq (by tape_eq) (by tape_eq)) (cfg_eq (by tape_eq) (by tape_eq))⟩
    omega)

theorem next_sound : ∀ p p', next p = some p' → ∃ n, 0 < n ∧ steps n p.cfg = some p'.cfg
  | .e _ 0, _, h => by simp [next] at h
  | .e _ 1, _, h => by simp [next] at h
  | .e x (z + 2), _, h => by piece (pc_e x z)
  | .q (m + 1) j (t + 3), _, h => by
    simp only [next, Option.some.injEq] at h; subst h
    have hk1 : min (m + 1) ((t + 2) / 2) ≤ m + 1 := Nat.min_le_left _ _
    have hk2 : 2 * min (m + 1) ((t + 2) / 2) ≤ t + 2 := by
      have := Nat.min_le_right (m + 1) ((t + 2) / 2); omega
    have hk0 : 1 ≤ min (m + 1) ((t + 2) / 2) := Nat.le_min.mpr ⟨by omega, by omega⟩
    obtain ⟨n, hn, h⟩ := q_rounds (min (m + 1) ((t + 2) / 2)) (m + 1 - min (m + 1) ((t + 2) / 2)) j
      (t + 2 - 2 * min (m + 1) ((t + 2) / 2))
    refine ⟨n, by omega, steps_eq_of h ?_ ?_⟩
    · simp only [Ph.cfg]; congr 1 <;> omega
    · simp only [Ph.cfg]; congr 1; omega
  | .q 0 j (t + 5), _, h => by piece (pc_end j t)
  | .q 0 j 4, _, h => by piece (pc_end4 j)
  | .q 0 j 3, _, h => by piece (pc_end3 j)
  | .q m j 2, _, h => by piece (pc_t2 j m)
  | .q m j 1, _, h => by piece (pc_t1 j m)
  | .q (m + 2) j 0, _, h => by piece (pc_t0 j m)
  | .q 1 j 0, _, h => by piece (pc_t01 j)
  | .q 0 0 0, _, h => by piece pc_t00
  | .q 0 (j + 1) 0, _, h => by piece (pc_t0j j)
  | .a (x + 2) 0, _, h => by piece (pc_a0 x)
  | .a (x + 2) (n + 1), _, h => by
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rcases hk with rfl | rfl
    · piece (pc_aodd k x)
    · piece (pc_aeven k x)
  | .a 1 0, _, h => by piece pc_a10
  | .a 1 (n + 1), _, h => by
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rcases hk with rfl | rfl
    · piece (pc_a1odd k)
    · piece (pc_a1even k)
  | .a 0 0, _, h => by piece pc_a00
  | .a 0 1, _, h => by piece pc_ones1
  | .a 0 2, _, h => by piece pc_ones2
  | .a 0 3, _, h => by piece pc_ones3
  | .a 0 4, _, h => by piece pc_ones4
  | .a 0 (n + 5), _, h => by piece (pc_ones n)

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

/-- The blank tape is `PA 0 0`. -/
theorem init_pa : init = (Ph.a 0 0).cfg := rfl

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
  | .q (_ + 1) _ (_ + 3), h | .q 0 _ (_ + 5), h | .q 0 _ 4, h | .q 0 _ 3, h => by simp [next] at h
  | .q _ _ 2, h | .q _ _ 1, h | .q (_ + 2) _ 0, h | .q 1 _ 0, h | .q 0 0 0, h | .q 0 (_ + 1) 0, h => by
    simp [next] at h
  | .a (_ + 2) _, h | .a 1 0, h | .a 1 (_ + 1), h | .a 0 0, h | .a 0 1, h | .a 0 2, h | .a 0 (_ + 3), h => by
    simp [next] at h

theorem iter_succ (k : Nat) (p p' : Ph) (h : iter k p = some p') : iter (k + 1) p = next p' := by
  induction k generalizing p with
  | zero => simp only [iter, Option.some.injEq] at h; subst h; simp [iter]
  | succ k ih =>
    simp only [iter] at h ⊢
    cases hp : next p with
    | none => simp [hp] at h
    | some q => simp only [hp, Option.bind_some] at h ⊢; exact ih q h

/-- **The machine halts from blank tape if and only if the phase map, iterated from `PA 0 0`, reaches `PE x z`
with `z ≤ 1`.** -/
theorem halts_iff :
    HaltsFromBlank ↔ ∃ k x z, z ≤ 1 ∧ iter k (.a 0 0) = some (.e x z) := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    have hall : ∀ k, ∃ p, iter k (.a 0 0) = some p := by
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
      exact ⟨m, hm, _, by rw [init_pa]; exact h⟩
    · exact fun _ h => h
  · rintro ⟨k, x, z, hz, h⟩
    obtain ⟨n, -, h1⟩ := reach_iter k _ _ h
    obtain ⟨m, c', h2, h3⟩ := e_halts x z hz
    exact ⟨n + m, c', steps_seq trans (by rw [init_pa]; exact h1) h2, h3⟩

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
theorem no_halt_phases : ∀ j, j < 100000000 → ∀ x z, iter j (.a 0 0) = some (.e x z) → 2 ≤ z :=
  okFor_sound _ _ (by native_decide)

/-! ## The parity classes and the all-ones moments

`Even` phases (`PE x z` with `z` even and `z ≥ 2`, `PA x y` with `x ≥ 1` and `y` even, `PQ m j t` with `t` even) lead
only to `Even` phases or to all-ones tapes `PA 0 n` (`even_next`), so from an `Even` phase the machine cannot halt
before the tape is next all ones (`even_safe`).  From an all-ones tape `PA 0 n` the run reaches, within a few
phases, either a halting phase, an `Even` phase or another all-ones tape; `fate` follows it there, and
`fatal_list` checks by `native_decide`, for every `n < 100000`, that it halts first exactly when `n = 1` or
`n = 28 * 2^k - 2k - 13` (`n = 3, 15, 41, 95, 205, ...`).  `ones_safe` and `ones_fatal` turn that into statements
about the machine. -/

def isEven : Ph → Bool
  | .e _ z => decide (z % 2 = 0 ∧ 2 ≤ z)
  | .a x y => decide (1 ≤ x ∧ y % 2 = 0)
  | .q _ _ t => decide (t % 2 = 0)

def isOnes : Ph → Bool
  | .a x _ => x == 0
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
    ∃ i, 0 < i ∧ i < k ∧ ∃ n, iter i p = some (.a 0 n)
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
        | a x0 n =>
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

/-- The all-ones lengths that halt before the tape is next all ones: `3` and `28 * 2^k - 2k - 13`. -/
def fatalLen (n : Nat) : Bool := n == 3 || (List.range 64).any (fun k => n + 2 * k + 13 == 28 * 2 ^ k)

/-- Checked for every `n < 100000`, at most 64 phases each. -/
theorem fatal_list : (List.range 100000).all (fun n => fate 64 (.a 0 n) == some (fatalLen n)) = true := by native_decide

/-- If `n < 100000` is a fatal length, the run from the all-ones tape `PA 0 n` halts. -/
theorem ones_fatal (n : Nat) (hn : n < 100000) (hf : fatalLen n = true) : TM.Halts trans (PA 0 n) := by
  have h := List.all_eq_true.mp fatal_list n (List.mem_range.mpr hn)
  rw [hf] at h
  obtain ⟨k, x, z, hz, hk⟩ := fate_true 64 _ (by simpa using h)
  obtain ⟨m, -, h1⟩ := reach_iter k _ _ hk
  obtain ⟨m', c', h2, h3⟩ := e_halts x z hz
  exact ⟨m + m', c', steps_seq trans h1 h2, h3⟩

/-- If `n < 100000` is not a fatal length, the run from the all-ones tape `PA 0 n` cannot halt before the tape is
all ones again. -/
theorem ones_safe (n : Nat) (hn : n < 100000) (hf : fatalLen n = false) :
    ∀ k x z, z ≤ 1 → iter k (.a 0 n) = some (.e x z) → ∃ i, 0 < i ∧ i < k ∧ ∃ m, iter i (.a 0 n) = some (.a 0 m) := by
  intro k x z hz hk
  have h := List.all_eq_true.mp fatal_list n (List.mem_range.mpr hn)
  rw [hf] at h
  obtain ⟨i, q, hi, hq, hc⟩ := fate_false 64 _ (by simpa using h)
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
    | a x0 m => simp only [isOnes, beq_iff_eq] at ho; subst ho; exact ⟨i, hi, hik', m, hq⟩
    | e _ _ | q _ _ _ => simp [isOnes] at ho

end H35167
