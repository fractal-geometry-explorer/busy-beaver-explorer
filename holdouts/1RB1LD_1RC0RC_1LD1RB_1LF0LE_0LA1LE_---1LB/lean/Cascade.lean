import Xor

/-!
# The XOR sweep is a cascade of one-bit transducers (machine-independent)

The same file is in the folders of the four F08 machines with the `111110` block
(`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`, `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA`,
`1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA`, `1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB`).

Keep the word `Z` of the zone orbit (`Zone.lean`) as a row of one-bit cells, cell 0 next to the block of words.
A sweep is an **event** that enters at cell 0 and travels away from the block:

* `P c`: the sweep arrives carrying the letter `c` (at cell 0, `c = pat n`, the letter of the block);
* `F`: the sweep stopped just before this cell and flips it.

Every cell does the same thing (`cell`), with its own bit `x`:

| event | `x = 0` | `x = 1` |
|---|---|---|
| `F`   | `x := 1`, nothing goes on | `x := 0`, nothing goes on |
| `P 0` | `F` goes on (the `00` is here) | `P 1` goes on |
| `P 1` | `P 0` goes on, `x := 1` | `P 1` goes on, `x := 0` |

`swr_feed`: one sweep of `c :: Z` is exactly the event `P c` fed to the cells `Z`.  The event either dies in a
cell (an ordinary sweep), or leaves the last cell: as `F` that is a **halt** (a `00` at the very end), as `P _` a
**reset** (no `00`).

`cell_bit`: what a cell's bit does depends on the event only, never on the bit: `F` and `P 1` toggle it, `P 0`
leaves it.  Hence (`run_rep_pow`) **any `m` cells fed `2^m` copies of any list of events are back where they
started**, and since the block's letter has period 3, the zone orbit restricted to its first `m` cells is periodic
with a period dividing `3 · 2^m` (`zone_period`).  `never_of_quiet`: if nothing leaves the word in the first
`3 · 2^|Z|` sweeps, nothing ever does, so the orbit neither halts nor resets.

Everything is checked by Lean's kernel.
-/

namespace XS

inductive Ev where
  | F
  | P (b : Bool)
  deriving DecidableEq, Repr

/-- One cell with bit `x`: the event that goes on (if any) and the new bit. -/
def cell (x : Bool) : Ev → Option Ev × Bool
  | .F => (none, !x)
  | .P false => if x then (some (.P true), true) else (some .F, false)
  | .P true => (some (.P x), !x)

/-- An event fed to a row of cells: the new cells and what leaves the last one. -/
def feed : List Bool → Ev → List Bool × Option Ev
  | [], e => ([], some e)
  | x :: t, e =>
    match cell x e with
    | (none, x') => (x' :: t, none)
    | (some e', x') => (x' :: (feed t e').1, (feed t e').2)

/-! ## One sweep is one event -/

/-- **The cascade.** A sweep that finds its `00` is an event that dies inside the cells, with the same new word. -/
theorem swr_feed_ok : ∀ (c : Bool) (Z : List Bool), (feed Z (.P c)).2 = none →
    ∃ d, swr (c :: Z) = .ok d (feed Z (.P c)).1
  | _, [], h => by simp [feed] at h
  | false, false :: [], h => by simp [feed, cell] at h
  | false, false :: c' :: t, _ => ⟨0, by cases c' <;> rfl⟩
  | false, true :: t, h => by
    have h' : (feed t (.P true)).2 = none := by simpa [feed, cell] using h
    obtain ⟨d, hd⟩ := swr_feed_ok true t h'
    refine ⟨d + 1, ?_⟩
    rw [swr_cons _ _ _ (by simp), hd]; simp [SW.pre, feed, cell]
  | true, b :: t, h => by
    have h' : (feed t (.P b)).2 = none := by cases b <;> simpa [feed, cell] using h
    obtain ⟨d, hd⟩ := swr_feed_ok b t h'
    refine ⟨d + 1, ?_⟩
    rw [swr_cons _ _ _ (by simp), hd]; cases b <;> simp [SW.pre, feed, cell]

/-- An `F` leaving the last cell is a halt. -/
theorem swr_feed_halt : ∀ (c : Bool) (Z : List Bool), (feed Z (.P c)).2 = some .F → swr (c :: Z) = .halt
  | _, [], h => by simp [feed] at h
  | false, false :: [], _ => rfl
  | false, false :: c' :: t, h => by simp [feed, cell] at h
  | false, true :: t, h => by
    have h' : (feed t (.P true)).2 = some .F := by simpa [feed, cell] using h
    rw [swr_cons _ _ _ (by simp), swr_feed_halt true t h']; rfl
  | true, b :: t, h => by
    have h' : (feed t (.P b)).2 = some .F := by cases b <;> simpa [feed, cell] using h
    rw [swr_cons _ _ _ (by simp), swr_feed_halt b t h']; rfl

/-- A `P` leaving the last cell is a reset. -/
theorem swr_feed_reset : ∀ (c : Bool) (Z : List Bool) (b : Bool), (feed Z (.P c)).2 = some (.P b) →
    swr (c :: Z) = .reset
  | c, [], _, _ => by cases c <;> rfl
  | false, false :: [], _, h => by simp [feed, cell] at h
  | false, false :: c' :: t, _, h => by simp [feed, cell] at h
  | false, true :: t, b, h => by
    have h' : (feed t (.P true)).2 = some (.P b) := by simpa [feed, cell] using h
    rw [swr_cons _ _ _ (by simp), swr_feed_reset true t b h']; rfl
  | true, x :: t, b, h => by
    have h' : (feed t (.P x)).2 = some (.P b) := by cases x <;> simpa [feed, cell] using h
    rw [swr_cons _ _ _ (by simp), swr_feed_reset x t b h']; rfl

/-! ## A cell's bit does not depend on its bit -/

/-- Whether an event toggles the bit of the cell it reaches. -/
def tog : Ev → Bool
  | .F => true
  | .P b => b

theorem cell_bit (x : Bool) (e : Ev) : (cell x e).2 = (x != tog e) := by
  cases e with
  | F => cases x <;> rfl
  | P b => cases b <;> cases x <;> rfl

/-! ## Streams of events -/

/-- A list of events fed to the cells one after the other: the new cells and everything that left the last one. -/
def run : List Bool → List Ev → List Bool × List Ev
  | Z, [] => (Z, [])
  | Z, e :: u =>
    let (Z1, o) := feed Z e
    ((run Z1 u).1, o.toList ++ (run Z1 u).2)

/-- One cell fed a list of events: its new bit and the events that went on. -/
def crun : Bool → List Ev → Bool × List Ev
  | x, [] => (x, [])
  | x, e :: u =>
    let (o, x') := cell x e
    ((crun x' u).1, o.toList ++ (crun x' u).2)

/-- The parity of a list of events: whether it toggles a cell. -/
def par : List Ev → Bool
  | [] => false
  | e :: u => tog e != par u

theorem crun_bit : ∀ (x : Bool) (u : List Ev), (crun x u).1 = (x != par u)
  | x, [] => by simp [crun, par]
  | x, e :: u => by
    have h := crun_bit (cell x e).2 u
    show (crun (cell x e).2 u).1 = (x != (tog e != par u))
    rw [h, cell_bit]; cases x <;> cases tog e <;> cases par u <;> rfl

theorem run_nil_out : ∀ (u : List Ev), run [] u = ([], u)
  | [] => rfl
  | e :: u => by simp [run, feed, run_nil_out u]

/-- **Causality.** The first cell processes the whole stream, the rest of the row gets what it lets through. -/
theorem run_cons : ∀ (x : Bool) (t : List Bool) (u : List Ev),
    run (x :: t) u = ((crun x u).1 :: (run t (crun x u).2).1, (run t (crun x u).2).2)
  | x, t, [] => by simp [run, crun]
  | x, t, e :: u => by
    simp only [run, crun, feed]
    cases hc : cell x e with
    | mk o x' =>
      cases o with
      | none =>
        simp only [Option.toList, List.nil_append]
        exact run_cons x' t u
      | some e' =>
        simp only [Option.toList, List.cons_append, List.nil_append]
        rw [run_cons x' (feed t e').1 u]
        simp only [run]
        rfl

theorem crun_append : ∀ (x : Bool) (u v : List Ev),
    crun x (u ++ v) = ((crun (crun x u).1 v).1, (crun x u).2 ++ (crun (crun x u).1 v).2)
  | x, [], v => by simp [crun]
  | x, e :: u, v => by
    simp only [List.cons_append, crun]
    rw [crun_append (cell x e).2 u v]; simp [List.append_assoc]

theorem run_append : ∀ (Z : List Bool) (u v : List Ev),
    run Z (u ++ v) = ((run (run Z u).1 v).1, (run Z u).2 ++ (run (run Z u).1 v).2)
  | Z, [], v => by simp [run]
  | Z, e :: u, v => by
    simp only [List.cons_append, run]
    rw [run_append (feed Z e).1 u v]; simp [List.append_assoc]

/-! ## Periodicity -/

/-- `k` copies of a list. -/
def rep : Nat → List Ev → List Ev
  | 0, _ => []
  | k + 1, u => u ++ rep k u

theorem rep_add (a b : Nat) (u : List Ev) : rep (a + b) u = rep a u ++ rep b u := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add]; simp [rep, ih, List.append_assoc]

theorem rep_mul (a b : Nat) (u : List Ev) : rep (a * b) u = rep a (rep b u) := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_mul, Nat.add_comm, rep_add, ih]; rfl

theorem par_append : ∀ (u v : List Ev), par (u ++ v) = (par u != par v)
  | [], v => by simp [par]
  | e :: u, v => by
    simp only [List.cons_append, par, par_append u v]
    cases tog e <;> cases par u <;> cases par v <;> rfl

/-- A cell that is back to its bit after `v` is back after any number of copies, and lets through as many
copies of the same events. -/
theorem crun_rep (x : Bool) (v : List Ev) (h : (crun x v).1 = x) :
    ∀ k, crun x (rep k v) = (x, rep k (crun x v).2)
  | 0 => rfl
  | k + 1 => by
    show crun x (v ++ rep k v) = _
    rw [crun_append, h, crun_rep x v h k]; rfl

/-- **Periodicity.** `m` cells fed `2^m` copies of any list of events are back to their bits. -/
theorem run_rep_pow : ∀ (Z : List Bool) (u : List Ev), (run Z (rep (2 ^ Z.length) u)).1 = Z
  | [], _ => by rw [run_nil_out]
  | x :: t, u => by
    have h2 : (crun x (u ++ u)).1 = x := by
      rw [crun_bit, par_append]; cases x <;> cases par u <;> rfl
    have e : rep (2 ^ (x :: t).length) u = rep (2 ^ t.length) (u ++ u) := by
      rw [show (x :: t).length = t.length + 1 from rfl, Nat.pow_succ, rep_mul]
      congr 1; simp [rep]
    rw [e, run_cons, crun_rep x (u ++ u) h2]
    simp only
    rw [run_rep_pow t]

/-! ## The zone orbit -/

/-- The events of `k` sweeps from block count `n`. -/
def evs (n : Nat) : Nat → List Ev
  | 0 => []
  | k + 1 => .P (pat n) :: evs (n + 1) k

theorem evs_add (n : Nat) : ∀ a b, evs n (a + b) = evs n a ++ evs (n + a) b
  | 0, b => by simp [evs]
  | a + 1, b => by
    rw [Nat.succ_add]
    simp only [evs, List.cons_append]
    rw [evs_add (n + 1) a b, show n + 1 + a = n + (a + 1) by omega]

theorem evs_shift3 (n k : Nat) : evs (n + 3) k = evs n k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [evs]
    rw [show n + 3 + 1 = (n + 1) + 3 by omega, ih (n + 1), pat_mod (n + 3), pat_mod n,
      show (n + 3) % 3 = n % 3 by omega]

theorem evs_rep (n : Nat) : ∀ j, evs n (3 * j) = rep j (evs n 3)
  | 0 => rfl
  | j + 1 => by
    rw [show 3 * (j + 1) = 3 + 3 * j by omega, evs_add, evs_shift3, evs_rep n j]; rfl

theorem evs_mod (n k : Nat) : evs n k = evs (n % 3) k := by
  have : ∀ r j, evs (r + 3 * j) k = evs r k := by
    intro r j; induction j with
    | zero => rfl
    | succ j ih => rw [show r + 3 * (j + 1) = (r + 3 * j) + 3 by omega, evs_shift3, ih]
  have e := this (n % 3) (n / 3)
  rw [Nat.mod_add_div] at e
  exact e

/-- **The period of a zone.** The first `m` cells of the zone orbit are back after `3 · 2^m` sweeps, from any
block count and any bits: the zone orbit, cut to any prefix of its word, is periodic. -/
theorem zone_period (n : Nat) (Z : List Bool) : (run Z (evs n (3 * 2 ^ Z.length))).1 = Z := by
  rw [evs_rep]; exact run_rep_pow Z (evs n 3)

/-- **Quiet for one period, quiet forever.** If nothing leaves the word during the first `3 · 2^|Z|` sweeps,
nothing leaves it during any number of sweeps: the zone orbit then never halts and never resets. -/
theorem never_of_quiet (n : Nat) (Z : List Bool) (h : (run Z (evs n (3 * 2 ^ Z.length))).2 = []) :
    ∀ k, (run Z (evs n k)).2 = [] := by
  have hz := zone_period n Z
  generalize hP : 3 * 2 ^ Z.length = P at h hz
  have hP0 : 0 < P := by rw [← hP]; exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have hper : ∀ n', n' % 3 = n % 3 → evs n' P = evs n P := by
    intro n' hn
    rw [evs_mod n', evs_mod n, hn]
  have h3 : P % 3 = 0 := by rw [← hP]; simp [Nat.mul_mod_right]
  have hall : ∀ j, (run Z (evs n (j * P))).1 = Z ∧ (run Z (evs n (j * P))).2 = [] := by
    intro j; induction j with
    | zero => simp [evs, run]
    | succ j ih =>
      rw [Nat.succ_mul, evs_add, run_append, ih.1, hper (n + j * P) (by
        rw [Nat.add_mod, Nat.mul_mod, h3]; simp), hz, ih.2, h]
      exact ⟨rfl, rfl⟩
  intro k
  have hk : k + (k * P - k) = k * P := by
    have : k ≤ k * P := Nat.le_mul_of_pos_right k hP0
    omega
  have := (hall k).2
  rw [← hk, evs_add, run_append] at this
  exact (List.append_eq_nil_iff.mp this).1

end XS
