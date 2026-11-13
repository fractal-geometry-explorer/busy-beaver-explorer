import Round
import Zone

/-!
# The round map for every tail, and the reduction

`Round.lean` proves the rounds for three tails.  Here the end of a round is computed for *any* tail `T` by the
zone simulator of `Zone.lean`: after the sweeps the tape is `0 11 0 11 0 111 (0111)^t 0 1^c T`; one copy of `0111`
is kept on each side and the `t - 2` copies between are the block, which the head only ever crosses whole, by six
shift rules (`rulesR`, `rulesL`).  The simulator never looks at `t`, so

    roundMap (n, T) = (4 (t - 2) + N, T')     with (N, T') computed from (T, (n - 1) mod 3) alone,

and `round_next` / `round_halt` say that this is what the machine does, for all `n ≥ 7` and all `T` for which the
simulator answers (it answers `stuck` if the head meets the block in a way the six rules do not cover, or after
`fuel T` moves; neither has been seen).

`halts_iff`: as long as the orbit of `(11, [])` never gets the answer `stuck`, the machine halts from blank tape
iff the orbit reaches a halting round.
-/

namespace H176107

open TM TM.Zone

def rulesR : List (Rule St) :=
  [⟨.A, [], [false, true, true, true], [true, false, false, true], 4⟩,
   ⟨.D, [], [true, true, false, true], [false, true, true, false], 4⟩]

def rulesL : List (Rule St) :=
  [⟨.A, [true], [true, false, false, true], [true, true, false, true], 6⟩,
   ⟨.F, [false], [false, true, true, false], [true, true, true, true], 4⟩,
   ⟨.C, [true], [true, false, false, true], [true, true, true, true], 4⟩,
   ⟨.D, [false], [false, true, true, false], [false, true, true, true], 6⟩]

theorem rulesR_ok : ∀ r ∈ rulesR, RuleR trans r := by
  intro r hr
  simp only [rulesR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact fun _ _ => rfl

theorem rulesL_ok : ∀ r ∈ rulesL, RuleL trans r := by
  intro r hr
  simp only [rulesL, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact fun _ _ => rfl

/-- The leading ones of a word: their number, and the rest. -/
def ones : List Bool → Nat × List Bool
  | true :: l => ((ones l).1 + 1, (ones l).2)
  | l => (0, l)

theorem ones_spec : ∀ (l : List Bool) (s : Tape), app l s = rep (ones l).1 [true] (app (ones l).2 s)
  | [], _ => rfl
  | false :: _, _ => rfl
  | true :: l, s => by
    simp only [ones, app_cons, rep_succ, app_nil]
    rw [← ones_spec l s]

/-- Drop the zeros at the end of a word. -/
def trim : List Bool → List Bool
  | [] => []
  | x :: l =>
    match x, trim l with
    | false, [] => []
    | x, t => x :: t

theorem trim_spec : ∀ l : List Bool, app (trim l) blank = app l blank
  | [] => rfl
  | x :: l => by
    have ih := trim_spec l
    simp only [trim]
    split
    · next h => rw [h] at ih; simp only [app_cons, app_nil] at ih ⊢; rw [← ih, cons_false_blank]
    · simp only [app_cons, ih]

def headWord : List Bool := [false, false, true, true, true, false]

/-- Reads a round start `D> 0 0 111 0 1^x (1111)^k 1^y T` off a simulator configuration: `(x + y, T)`. -/
def decode (c : ACfg St) : Option (Nat × List Bool) :=
  if c.z = .L ∧ c.st = .D ∧ c.a = [] ∧ c.m = [true, true, true, true] ∧ c.b.take 6 = headWord ∧
      (ones (c.b.drop 6)).2 = [] then
    some ((ones (c.b.drop 6)).1 + (ones c.o).1, trim (ones c.o).2)
  else none

theorem decode_spec (k : Nat) {c : ACfg St} {N : Nat} {T : List Bool} (h : decode c = some (N, T)) :
    enc k c = R0 (4 * k + N) T := by
  obtain ⟨z, a, b, m, o, q⟩ := c
  unfold decode at h
  split at h
  · next hc =>
    obtain ⟨rfl, rfl, rfl, rfl, hb, ho⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only at hb ho
    have eb : b = headWord ++ b.drop 6 := by rw [← hb, List.take_append_drop]
    have e1 : ∀ s : Tape, app b s = app headWord (rep (ones (b.drop 6)).1 [true] s) := by
      intro s
      have h1 := ones_spec (b.drop 6) s
      rw [ho] at h1
      calc app b s = app (headWord ++ b.drop 6) s := by rw [← eb]
        _ = app headWord (app (b.drop 6) s) := (app_app _ _ _).symm
        _ = _ := by rw [h1]; rfl
    have e2 : app o blank = rep (ones o).1 [true] (app (trim (ones o).2) blank) := by
      rw [trim_spec, ← ones_spec]
    simp only [enc, R0, app_nil]
    rw [e1, rep4, e2, ← rep_add, ← rep_add]
    have : (ones (List.drop 6 b)).fst + 4 * k + (ones o).fst = 4 * k + ((ones (List.drop 6 b)).fst + (ones o).fst) := by
      omega
    rw [this]; rfl
  · cases h

/-- After the sweeps: `A> 0 11 0 11 0 111 0111 [(0111)^k] 0111 0 1^c T`. -/
def ini (c : Nat) (T : List Bool) : ACfg St :=
  ⟨.L, [], [false, true, true, false, true, true, false, true, true, true, false, true, true, true],
    [false, true, true, true], [false, true, true, true, false] ++ (List.replicate c true ++ T), .A⟩

theorem app_replicate (c : Nat) (T : List Bool) (s : Tape) :
    app (List.replicate c true ++ T) s = rep c [true] (app T s) := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [List.replicate_succ, List.cons_append, app_cons, rep_succ, app_nil, ih]

theorem ini_spec (k c : Nat) (T : List Bool) : enc k (ini c T) = X (k + 2) c T := by
  have e1 : app ([false, true, true, true, false] ++ (List.replicate c true ++ T)) blank =
      app [false, true, true, true] (cons false (rep c [true] (app T blank))) := by
    rw [← app_app, app_replicate]; rfl
  simp only [enc, ini, X]
  rw [e1, rep_app_comm]
  rfl

def fuel (T : List Bool) : Nat := 100 * (T.length + 10) ^ 2

/-- The round map: from the round start `R0 n T`, the next round start, `halt`, or `stuck` (no answer). -/
def roundMap (x : Nat × List Bool) : Res (Nat × List Bool) :=
  if x.1 < 7 then .stuck else
  match arun trans rulesR rulesL (fun c => (decode c).isSome) (fuel x.2) (ini ((x.1 - 1) % 3 + 1) x.2) with
  | .next c' =>
    match decode c' with
    | some (N, T') => .next (4 * ((x.1 - 1) / 3 - 2) + N, T')
    | none => .stuck
  | .halt => .halt
  | .stuck => .stuck

/-- From a round start to the end of its sweeps, in a positive number of steps. -/
theorem to_end' (T : List Bool) (t c : Nat) :
    ∃ s, 0 < s ∧ steps s (R0 (c + 1 + 3 * t) T) = some (X t (c + 1) T) := by
  have h1 := first (c + 3 * t) T
  rw [show c + 3 * t + 1 = c + 1 + 3 * t by omega] at h1
  obtain ⟨s, hs⟩ := sweeps T t 0 c
  rw [Nat.zero_add] at hs
  exact ⟨60 + 35 + s, by omega, steps_seq trans h1 hs⟩

theorem decomp {n : Nat} (h : ¬ n < 7) :
    n = (n - 1) % 3 + 1 + 3 * (((n - 1) / 3 - 2) + 2) := by omega

/-- **A round, for every tail**: if the map answers `(n', T')`, the machine goes from `R0 n T` to `R0 n' T'`. -/
theorem round_next {x y : Nat × List Bool} (h : roundMap x = .next y) :
    ∃ s, 0 < s ∧ steps s (R0 x.1 x.2) = some (R0 y.1 y.2) := by
  unfold roundMap at h
  split at h
  · cases h
  · next hn =>
    split at h
    · next c' hr =>
      split at h
      · next N T' hd =>
        simp only [Res.next.injEq] at h
        subst h
        obtain ⟨_, n2, h2⟩ := arun_sound rulesR_ok rulesL_ok ((x.1 - 1) / 3 - 2) _ _ _ _ hr
        rw [ini_spec, decode_spec _ hd] at h2
        obtain ⟨s1, hp, h1⟩ := to_end' x.2 (((x.1 - 1) / 3 - 2) + 2) ((x.1 - 1) % 3)
        rw [← decomp hn] at h1
        exact ⟨s1 + n2, by omega, steps_seq trans h1 h2⟩
      · cases h
    · cases h
    · cases h

/-- If the map answers `halt`, the machine halts from `R0 n T`. -/
theorem round_halt {x : Nat × List Bool} (h : roundMap x = .halt) : Halts trans (R0 x.1 x.2) := by
  unfold roundMap at h
  split at h
  · cases h
  · next hn =>
    split at h
    · split at h <;> cases h
    · next hr =>
      obtain ⟨n2, c2, h2, h3⟩ := arun_halt rulesR_ok rulesL_ok ((x.1 - 1) / 3 - 2) _ _ _ hr
      rw [ini_spec] at h2
      obtain ⟨s1, _, h1⟩ := to_end' x.2 (((x.1 - 1) / 3 - 2) + 2) ((x.1 - 1) % 3)
      rw [← decomp hn] at h1
      exact ⟨_, c2, steps_seq trans h1 h2, h3⟩
    · cases h

/-! ## The orbit from blank tape -/

/-- The orbit of the round map from `(11, empty tail)`, the second round start of the run from blank tape. -/
def orbit : Nat → Res (Nat × List Bool)
  | 0 => .next (11, [])
  | i + 1 =>
    match orbit i with
    | .next x => roundMap x
    | r => r

theorem blank_to_11 : ∃ n, steps n init = some (R0 11 []) := by
  obtain ⟨s, hs⟩ := round (n := 3) (T := .e) (n' := 11) (T' := .e) rfl
  exact ⟨_, steps_seq trans blank_to_round hs⟩

theorem orbit_reach : ∀ (i : Nat) (x : Nat × List Bool), orbit i = .next x →
    ∃ n, i ≤ n ∧ steps n init = some (R0 x.1 x.2) := by
  intro i
  induction i with
  | zero =>
    intro x h
    simp only [orbit, Res.next.injEq] at h
    subst h
    obtain ⟨n, hn⟩ := blank_to_11
    exact ⟨n, Nat.zero_le _, hn⟩
  | succ i ih =>
    intro x h
    simp only [orbit] at h
    cases e : orbit i with
    | next y =>
      rw [e] at h
      obtain ⟨n, hn, h1⟩ := ih y e
      obtain ⟨s, hs, h2⟩ := round_next h
      exact ⟨n + s, by omega, steps_seq trans h1 h2⟩
    | halt => rw [e] at h; cases h
    | stuck => rw [e] at h; cases h

theorem halts_of_orbit : ∀ i, orbit i = .halt → HaltsFromBlank := by
  intro i
  induction i with
  | zero => intro h; cases h
  | succ i ih =>
    intro h
    simp only [orbit] at h
    cases e : orbit i with
    | next y =>
      rw [e] at h
      obtain ⟨n, _, h1⟩ := orbit_reach i y e
      obtain ⟨n2, c2, h2, h3⟩ := round_halt h
      exact ⟨_, c2, steps_seq trans h1 h2, h3⟩
    | halt => exact ih e
    | stuck => rw [e] at h; cases h

theorem not_halts_of_orbit (h : ∀ i, ∃ x, orbit i = .next x) : ¬ HaltsFromBlank := by
  rintro ⟨n, c', h1, h2⟩
  obtain ⟨x, hx⟩ := h (n + 1)
  obtain ⟨m, hm, h3⟩ := orbit_reach _ x hx
  have e : m = n + ((m - n - 1) + 1) := by omega
  rw [e] at h3
  have h4 : (some _ : Option Config) = none := h3.symm.trans (steps_halt trans h1 h2 (m - n - 1))
  cases h4

/-- **The reduction.**  As long as the round map answers along the orbit, the machine halts from blank tape iff
the orbit reaches a halting round. -/
theorem halts_iff (h : ∀ i, orbit i ≠ .stuck) : HaltsFromBlank ↔ ∃ i, orbit i = .halt := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hn
    apply not_halts_of_orbit _ hh
    intro i
    cases e : orbit i with
    | next x => exact ⟨x, rfl⟩
    | halt => exact absurd ⟨i, e⟩ hn
    | stuck => exact absurd e (h i)
  · rintro ⟨i, hi⟩
    exact halts_of_orbit i hi

/-! ## The first rounds, evaluated -/

def isNext : Res (Nat × List Bool) → Bool
  | .next _ => true
  | _ => false

theorem isNext_mono : ∀ i j, i ≤ j → isNext (orbit j) = true → isNext (orbit i) = true := by
  intro i j hij
  induction j with
  | zero => intro h; rw [show i = 0 by omega]; exact h
  | succ j ih =>
    intro h
    by_cases e : i = j + 1
    · rw [e]; exact h
    · apply ih (by omega)
      simp only [orbit] at h
      cases e2 : orbit j with
      | next _ => rfl
      | halt => rw [e2] at h; exact h
      | stuck => rw [e2] at h; exact h

/-- The orbit answers for its first 500 rounds, by the kernel. -/
theorem orbit_500 : isNext (orbit 500) = true := by decide +kernel

theorem first_rounds : ∀ i, i ≤ 500 → ∃ x, orbit i = .next x := by
  intro i hi
  have h := isNext_mono i 500 hi orbit_500
  cases e : orbit i with
  | next x => exact ⟨x, rfl⟩
  | halt => rw [e] at h; cases h
  | stuck => rw [e] at h; cases h

/-- The orbit after ten rounds: 579 ones, empty tail (as `py/zonemap.py orbit` prints). -/
theorem orbit_10 : orbit 10 = .next (579, []) := by decide +kernel

/-- The map does answer `halt` on some tails: the round start of `halting_round`. -/
theorem roundMap_halt : roundMap (57, tH) = .halt := by decide +kernel

end H176107
