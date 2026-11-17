import Cascade

/-!
# Windows of the cascade: one pass per cell for a whole period (machine-independent)

The same file is in the folders of the four F08 machines with the `111110` block
(`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`, `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA`,
`1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA`, `1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB`).

`Cascade.lean` turns a sweep of the zone orbit into an event fed to a row of one-bit cells.  A cell's bit
depends only on the parity of what it was fed (`crun_bit`), so a cell fed a list of events `W` is back to its
bit either after `W` or after `W ++ W`.  This gives an exact way to run a prefix of the word over a long
window without running the sweeps one by one:

* `wfold Z W` passes `W` through the first cell once if its bit is back afterwards, twice otherwise, and goes on
  with what came out; it returns what leaves the last cell and the number `d` of cells that needed two passes.
* `wfold_run`: the cells `Z` fed `r · 2^d` copies of `W` are back to their bits and let through `r` copies of
  that output.
* `window_quiet`: split the word as `Zp ++ Zr`.  If the output of `wfold Zp` (the block's three letters), run
  through `Zr`, lets nothing out of the word, then nothing leaves the word during the first `3 · 2^d` sweeps.

The window doubles with every cell of `Zp` whose bit is not back, while the work only grows with the length of
the streams.  Everything here is checked by Lean's kernel; the per-machine files evaluate it with compiled code.
-/

namespace XS

/-! ## Fast versions for compiled evaluation

`crun` recurses once per event, which overflows the stack on streams of millions of events.  `crunAcc` is
tail-recursive; `@[csimp]` makes compiled code use it (the equality is proved), so it comes before every
definition that compiled code runs.  `outC` below runs the word cell by cell instead of event by event. -/

/-- One cell, tail-recursive: the output is accumulated reversed. -/
def crunAcc : Bool → List Ev → List Ev → Bool × List Ev
  | x, [], acc => (x, acc.reverse)
  | x, e :: u, acc =>
    match cell x e with
    | (none, x') => crunAcc x' u acc
    | (some o, x') => crunAcc x' u (o :: acc)

theorem crunAcc_eq : ∀ (x : Bool) (u acc : List Ev), crunAcc x u acc = ((crun x u).1, acc.reverse ++ (crun x u).2)
  | x, [], acc => by simp [crunAcc, crun]
  | x, e :: u, acc => by
    simp only [crunAcc, crun]
    cases hc : cell x e with
    | mk o x' =>
      cases o with
      | none => simp only [Option.toList, List.nil_append]; exact crunAcc_eq x' u acc
      | some o =>
        show crunAcc x' u (o :: acc) = _
        rw [crunAcc_eq x' u (o :: acc)]; simp

def crunFast (x : Bool) (u : List Ev) : Bool × List Ev := crunAcc x u []

@[csimp] theorem crun_eq_fast : @crun = @crunFast := by
  funext x u; simp [crunFast, crunAcc_eq]

/-- The window: the stream that leaves the cells `Z` over one period, and the number of cells that needed two
passes (the period of `Z` fed `W` is `2^d` copies of `W`). -/
def wfold : List Bool → List Ev → List Ev × Nat
  | [], W => (W, 0)
  | x :: t, W =>
    let r := crun x W
    if r.1 = x then wfold t r.2
    else
      let p := wfold t (r.2 ++ (crun r.1 W).2)
      (p.1, p.2 + 1)

theorem rep_two (u : List Ev) : rep 2 u = u ++ u := by simp [rep]

theorem rep_one (u : List Ev) : rep 1 u = u := by simp [rep]

/-- **The window.** The cells `Z` fed `r · 2^d` copies of `W` are back where they started and let through `r`
copies of the output of `wfold`. -/
theorem wfold_run : ∀ (Z : List Bool) (W : List Ev) (r : Nat),
    run Z (rep (r * 2 ^ (wfold Z W).2) W) = (Z, rep r (wfold Z W).1)
  | [], W, r => by simp only [wfold, Nat.pow_zero, Nat.mul_one]; exact run_nil_out _
  | x :: t, W, r => by
    by_cases h : (crun x W).1 = x
    · have e : wfold (x :: t) W = wfold t (crun x W).2 := by simp only [wfold, h, ite_true]
      rw [e, run_cons, crun_rep x W h, wfold_run t (crun x W).2 r]
    · have e : wfold (x :: t) W =
          ((wfold t ((crun x W).2 ++ (crun (crun x W).1 W).2)).1,
           (wfold t ((crun x W).2 ++ (crun (crun x W).1 W).2)).2 + 1) := by
        simp only [wfold, h, ite_false]
      have h2 : (crun x (W ++ W)).1 = x := by
        rw [crun_bit, par_append]; cases x <;> cases par W <;> rfl
      have e2 : (crun x (W ++ W)).2 = (crun x W).2 ++ (crun (crun x W).1 W).2 := by
        rw [crun_append]
      rw [e, Nat.pow_succ, ← Nat.mul_assoc, rep_mul, rep_two, run_cons, crun_rep x (W ++ W) h2, e2,
        wfold_run t _ r]

/-- Running a word cut in two: the second part gets what leaves the first. -/
theorem run_split : ∀ (Zp Zr : List Bool) (u : List Ev),
    (run (Zp ++ Zr) u).2 = (run Zr (run Zp u).2).2
  | [], Zr, u => by rw [run_nil_out]; rfl
  | x :: t, Zr, u => by
    rw [List.cons_append, run_cons, run_cons]
    exact run_split t Zr _

/-- What leaves the word during a prefix of the sweeps is a prefix of what leaves it during all of them. -/
theorem evs_quiet_le (n : Nat) (Z : List Bool) {k K : Nat} (hk : k ≤ K) (h : (run Z (evs n K)).2 = []) :
    (run Z (evs n k)).2 = [] := by
  rw [show K = k + (K - k) by omega, evs_add, run_append] at h
  exact (List.append_eq_nil_iff.mp h).1

/-- **Quiet over a window.** If the output of `wfold Zp` over the block's three letters, run through `Zr`, lets
nothing out, then nothing leaves the word `Zp ++ Zr` during the first `3 · 2^d` sweeps. -/
theorem window_quiet (n : Nat) (Zp Zr : List Bool) (h : (run Zr (wfold Zp (evs n 3)).1).2 = []) :
    ∀ k, k ≤ 3 * 2 ^ (wfold Zp (evs n 3)).2 → (run (Zp ++ Zr) (evs n k)).2 = [] := by
  intro k hk
  apply evs_quiet_le n _ hk
  rw [evs_rep, run_split, show 2 ^ (wfold Zp (evs n 3)).2 = 1 * 2 ^ (wfold Zp (evs n 3)).2 by omega,
    wfold_run, rep_one]
  exact h

/-- What leaves the word, cell by cell. -/
def outC : List Bool → List Ev → List Ev
  | [], u => u
  | x :: t, u => outC t (crun x u).2

theorem outC_eq : ∀ (Z : List Bool) (u : List Ev), outC Z u = (run Z u).2
  | [], u => by rw [run_nil_out]; rfl
  | x :: t, u => by rw [run_cons]; exact outC_eq t _

/-- The check that the per-machine files evaluate: the word `Z` cut after `m` cells, the window has `d`
doublings and nothing leaves the word. -/
def windowCheck (n m d : Nat) (Z : List Bool) : Bool :=
  let p := wfold (Z.take m) (evs n 3)
  p.2 == d && (outC (Z.drop m) p.1).isEmpty

theorem window_of_check {n m d : Nat} {Z : List Bool} (h : windowCheck n m d Z = true) :
    ∀ k, k ≤ 3 * 2 ^ d → (run Z (evs n k)).2 = [] := by
  simp only [windowCheck, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨hd, ho⟩ := h
  rw [outC_eq] at ho
  intro k hk
  rw [← List.take_append_drop m Z]
  exact window_quiet n _ _ ho k (hd ▸ hk)

end XS
