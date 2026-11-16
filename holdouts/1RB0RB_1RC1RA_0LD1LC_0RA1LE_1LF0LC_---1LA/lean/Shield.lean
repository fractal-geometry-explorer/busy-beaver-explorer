import ZoneCascade

/-!
# 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA: the stranded block shields the old zone

At zone step 3 · 10^7 the word of the zone orbit is: the new zone (76 cells), the stranded block (403,835 cells
`0 1 0 0 1 0 …`, on the tape the pairs `10 1110`), and the old zone (63 cells).  In the cascade of
`Cascade.lean`:

* `sb_stop`: an event that reaches the untouched part of the block dies within five of its cells, and changes
  nothing beyond them;
* `shield`: so a row `X ++ (5k cells of the block) ++ R` fed at most `k` events lets nothing out: the old zone
  is frozen, and the word lets nothing out, until the new zone has sent 80,767 events into the block;
* `per_run`: the events the first `m` cells let through during one period, computed by doubling (`per`);
* `zone96`: by compiled evaluation, at zone step 3 · 10^7 the first 96 cells (the new zone and the first 20 cells of
  the block) are back after `3 · 2^44` sweeps and let 42,405 events through per period, fewer than the 80,763 that
  the remaining 403,815 cells of the block need;
* `blank_runs_shield`: hence no halt for `3 · 2^44` more sweeps, and **no halt in the first 5.5 · 10^27 steps from
  blank tape**.
-/

namespace H25821

open TM hiding rep
open XS

/-! ## The block -/

/-- The letters of the stranded block, `0 1 0 0 1 0 …` from the new zone outwards. -/
def bq (i : Nat) : Bool := i % 3 == 1

/-- `k` letters of the block from phase `s`. -/
def sb (s : Nat) : Nat → List Bool
  | 0 => []
  | k + 1 => bq s :: sb (s + 1) k

theorem sb_add (s : Nat) : ∀ a b, sb s (a + b) = sb s a ++ sb (s + a) b
  | 0, b => by simp [sb]
  | a + 1, b => by
    rw [Nat.succ_add]; simp only [sb, List.cons_append]
    rw [sb_add (s + 1) a b, show s + 1 + a = s + (a + 1) by omega]

theorem sb_mod : ∀ (k s : Nat), sb s k = sb (s % 3) k
  | 0, _ => rfl
  | k + 1, s => by
    simp only [sb]
    have h1 : bq s = bq (s % 3) := by simp [bq]
    have h2 : (s + 1) % 3 = (s % 3 + 1) % 3 := by omega
    rw [h1, sb_mod k (s + 1), sb_mod k (s % 3 + 1), h2]

theorem feed_append : ∀ (X Y : List Bool) (e : Ev),
    feed (X ++ Y) e = match feed X e with
      | (X', none) => (X' ++ Y, none)
      | (X', some e') => (X' ++ (feed Y e').1, (feed Y e').2)
  | [], Y, e => by simp [feed]
  | x :: t, Y, e => by
    simp only [List.cons_append, feed]
    cases cell x e with
    | mk o x' =>
      cases o with
      | none => rfl
      | some e' =>
        simp only
        rw [feed_append t Y e']
        cases feed t e' with
        | mk X' o' => cases o' <;> rfl

/-- **An event dies within five cells of the untouched block.** -/
theorem sb_stop (s : Nat) (e : Ev) (R : List Bool) :
    ∃ Y : List Bool, Y.length = 5 ∧ feed (sb s 5 ++ R) e = (Y ++ R, none) := by
  have h5 : (feed (sb s 5) e).2 = none ∧ (feed (sb s 5) e).1.length = 5 := by
    rw [sb_mod]
    have h : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
    rcases h with h | h | h <;> rw [h] <;> rcases e with _ | b <;> (try cases b) <;> decide
  rw [feed_append]
  obtain ⟨h1, h2⟩ := h5
  cases hf : feed (sb s 5) e with
  | mk Y o =>
    rw [hf] at h1 h2
    simp only at h1 h2
    subst h1
    exact ⟨Y, h2, rfl⟩

/-- **The shield.** At most `k` events into `5k` cells of the block: nothing gets out. -/
theorem shield : ∀ (w : List Ev) (X : List Bool) (s k : Nat) (R : List Bool), w.length ≤ k →
    (run (X ++ sb s (5 * k) ++ R) w).2 = []
  | [], _, _, _, _, _ => rfl
  | e :: w, X, s, k, R, hk => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hw : w.length ≤ k' + 1 := by simp at hk; omega
    have hw' : w.length ≤ k' := by simp at hk; omega
    simp only [run]
    rw [List.append_assoc, feed_append]
    cases hX : feed X e with
    | mk X' o =>
      cases o with
      | none =>
        simp only [Option.toList, List.nil_append]
        rw [← List.append_assoc]
        exact shield w X' s (k' + 1) R hw
      | some e' =>
        simp only
        rw [show 5 * (k' + 1) = 5 + 5 * k' by omega, sb_add, List.append_assoc]
        obtain ⟨Y, -, hY⟩ := sb_stop s e' (sb (s + 5) (5 * k') ++ R)
        rw [hY]
        simp only [Option.toList, List.nil_append]
        rw [← List.append_assoc, ← List.append_assoc]
        exact shield w (X' ++ Y) (s + 5) k' R hw'

/-! ## A prefix of cells, and its period computed by doubling -/

theorem run_cells_append : ∀ (A B : List Bool) (u : List Ev),
    run (A ++ B) u = ((run A u).1 ++ (run B (run A u).2).1, (run B (run A u).2).2)
  | [], B, u => by rw [run_nil_out]; rfl
  | x :: t, B, u => by
    rw [List.cons_append, run_cons, run_cons, run_cells_append t B]; rfl

/-- The number of copies of `u` in one period of the cells `Z`, and what the cells let through meanwhile. -/
def per : List Bool → List Ev → Nat × List Ev
  | [], u => (1, u)
  | x :: t, u =>
    if (XS.crun x u).1 = x then per t (XS.crun x u).2
    else ((per t (XS.crun x (u ++ u)).2).1 * 2, (per t (XS.crun x (u ++ u)).2).2)

theorem rep_one (u : List Ev) : rep 1 u = u := by simp [rep]

theorem per_run : ∀ (Z : List Bool) (u : List Ev), run Z (rep (per Z u).1 u) = (Z, (per Z u).2)
  | [], u => by simp only [per]; rw [rep_one, run_nil_out]
  | x :: t, u => by
    simp only [per]
    split
    · next h =>
      rw [run_cons, crun_rep x u h, per_run t]
    · next h =>
      have h2 : (XS.crun x (u ++ u)).1 = x := by
        rw [crun_bit, par_append]; cases x <;> cases par u <;> rfl
      rw [rep_mul, show rep 2 u = u ++ u by simp [rep], run_cons, crun_rep x _ h2, per_run t]

theorem run_rep (Z : List Bool) (v w : List Ev) (h : run Z v = (Z, w)) : ∀ q, run Z (rep q v) = (Z, rep q w)
  | 0 => rfl
  | q + 1 => by
    show run Z (v ++ rep q v) = (Z, w ++ rep q w)
    rw [run_append, h]; simp only; rw [run_rep Z v w h q]

theorem rep_length (w : List Ev) : ∀ q, (rep q w).length = q * w.length
  | 0 => by simp [rep]
  | q + 1 => by simp [rep, rep_length w q, Nat.succ_mul]; omega

/-! ## The state of zone step 3 · 10^7 -/

/-- What compiled evaluation checks at zone step 3 · 10^7: the first 96 cells (the new zone and 20 cells of the block)
have a period of `3 · 2^44` sweeps and let 42,405 events through per period; then come 403,815 more cells of the
block. -/
def good : Option (Nat × CS) → Bool
  | some (_, .rt n Z) =>
    (per (Z.take 96) (evs n 3)).1 == 2 ^ 44 && (per (Z.take 96) (evs n 3)).2.length == 42405 &&
      ((Z.drop 96).take 403815 == sb 20 403815) && decide (29000000 ≤ n)
  | _ => false

theorem zone96 : good (H25821.crun 30000000 (3, .rt 0 [])) = true := by native_decide

/-! ## Step counts -/

theorem corb_quiet_t {j t n : Nat} {Z : List Bool} (hj : corb j = some (t, .rt n Z)) :
    ∀ k, (run Z (evs n k)).2 = [] →
      ∃ t', corb (j + k) = some (t', .rt (n + k) (run Z (evs n k)).1) ∧ t + 4 * (n * k) + 2 * (k * k) ≤ t' + 2 * k
  | 0, _ => ⟨t, by simpa [evs, run] using hj, by omega⟩
  | k + 1, h => by
    rw [evs_add, run_append] at h
    have h1 := (List.append_eq_nil_iff.mp h).1
    have h2 := (List.append_eq_nil_iff.mp h).2
    obtain ⟨t', ht', hle⟩ := corb_quiet_t hj k h1
    have e1 : evs (n + k) 1 = [.P (pat (n + k))] := rfl
    rw [e1] at h2
    have hn := feed_none_of_run _ _ h2
    obtain ⟨d, hd⟩ := swr_feed_ok (pat (n + k)) _ hn
    refine ⟨t' + (4 * (n + k + d) + 14), ?_, ?_⟩
    · rw [show j + (k + 1) = (j + k) + 1 by omega]
      show (match corb (j + k) with
        | none => none
        | some (t, s) => _) = _
      rw [ht']
      simp only [cstep, hd, evs_add, run_append, e1, run_one, show n + (k + 1) = n + k + 1 by omega]
    · have a1 : n * (k + 1) = n * k + n := Nat.mul_succ n k
      have a2 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
        rw [Nat.succ_mul, Nat.mul_succ]; omega
      rw [a1, a2]; omega

/-! ## The bound -/

/-- Sweeps covered: one period of the first 96 cells, 42,405 events into the rest of the block, fewer than
80,763. -/
def S0 : Nat := 1 * (3 * 2 ^ 44)

theorem quiet_S0 {n : Nat} {Z : List Bool} (hg : good (some (0, .rt n Z)) = true) :
    ∀ k, k ≤ S0 → (run Z (evs n k)).2 = [] := by
  simp only [good, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨hp1, hp2⟩, hb⟩, -⟩ := hg
  have hZ : Z = Z.take 96 ++ (sb 20 (5 * 80763) ++ (Z.drop 96).drop 403815) := by
    rw [show 5 * 80763 = 403815 from rfl, ← hb, List.take_append_drop, List.take_append_drop]
  have hall : (run Z (evs n S0)).2 = [] := by
    have hper := per_run (Z.take 96) (evs n 3)
    rw [hp1] at hper
    have e : evs n S0 = rep 1 (rep (2 ^ 44) (evs n 3)) := by
      rw [S0, ← rep_mul, ← evs_rep]
    rw [e, hZ, run_cells_append, run_rep _ _ _ hper 1]
    have hs := shield (rep 1 (per (Z.take 96) (evs n 3)).2) [] 20 80763 ((Z.drop 96).drop 403815)
      (by rw [rep_length, hp2]; decide)
    simpa using hs
  intro k hk
  have h := hall
  rw [show S0 = k + (S0 - k) by omega, evs_add, run_append] at h
  exact (List.append_eq_nil_iff.mp h).1

/-- **No halt in the first 5.5 · 10^27 steps from blank tape.** -/
theorem blank_runs_shield : ∃ c, steps 5500000000000000000000000000 init = some c := by
  have hz := zone96
  rw [← corb_eq_crun] at hz
  cases hc : corb 30000000 with
  | none => rw [hc] at hz; simp [good] at hz
  | some p =>
    obtain ⟨t, s⟩ := p
    cases s with
    | raw c => rw [hc] at hz; simp [good] at hz
    | rt n Z =>
      rw [hc] at hz
      have hg : good (some (0, .rt n Z)) = true := hz
      have hn : 29000000 ≤ n := by
        simp only [good, Bool.and_eq_true, decide_eq_true_eq] at hz; exact hz.2
      obtain ⟨t', ht', hle⟩ := corb_quiet_t hc S0 (quiet_S0 hg S0 (Nat.le_refl _))
      have hs := (corb_sound _ _ _ ht').1
      have hbig : 5500000000000000000000000000 ≤ t' := by
        have e1 : S0 = 52776558133248 := rfl
        have e2 : S0 * S0 = 2785365088392105618523029504 := rfl
        rw [e2, e1] at hle
        omega
      rw [show t' = 5500000000000000000000000000 + (t' - 5500000000000000000000000000) by omega] at hs
      exact steps_le trans hs

end H25821
