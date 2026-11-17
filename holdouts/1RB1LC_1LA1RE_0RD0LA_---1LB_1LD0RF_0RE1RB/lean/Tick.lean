import TM

/-!
# Window runs, two-sided ticks and batches of counter ticks

Generic over the machine `δ`.  Three pieces, each a finite computation with a theorem that turns it into machine
steps on any surrounding tape:

* `wrun`: a run on a finite window of cells (`WCfg`: left cells nearest first, the head on the first right cell).
  It fails if the head would read past the right end of the window or step left of its left end, so a successful
  run never looks outside the window, and `wrun_sound` gives the same steps on `app l X`, `app r Y` for any `X`, `Y`.
* `side`: one side of the tape around a *base* cell, driven through a list of arrivals `P` at the base.  At each
  arrival the machine is on the base cell; the step from there goes into the left part or the right part, and the
  side that owns that direction runs until the head is back on the base cell about to go to the other side (or at
  the end of the tick).  `side_sound`: if the left part and the right part both follow the same arrivals, the whole
  machine does, and its cost is the sum of the two.
* `layD`: a counter laid out on one side as digit cells (single cells, or pairs of equal cells) separated by fixed
  gaps.  `tick` turns a check of the two sides for every carry length into one increment of both counters for any
  value, and `batch` into `d` increments, with the step count in closed form (`csum`, `cnt`).
-/

namespace TM

variable {Q : Type}

/-- A window: the cells left of the head (nearest first), the head cell and the cells right of it. -/
structure WCfg (Q : Type) where
  l : List Bool
  r : List Bool
  st : Q

/-- The window placed in a tape: `X` beyond its left end, `Y` beyond its right end. -/
def WCfg.at (c : WCfg Q) (X Y : Tape) : Cfg Q := ⟨app c.l X, app c.r Y, c.st⟩

section
variable (δ : Q → Bool → Option (Bool × Dir × Q))

/-- One step inside the window; `none` on a halt, on reading past the right end, or on stepping off the left end. -/
def wstep (c : WCfg Q) : Option (WCfg Q) :=
  match c.r with
  | [] => none
  | a :: r' =>
    match δ c.st a with
    | none => none
    | some (w, .R, s) => some ⟨w :: c.l, r', s⟩
    | some (w, .L, s) =>
      match c.l with
      | [] => none
      | b :: l' => some ⟨l', b :: w :: r', s⟩

theorem wstep_sound {c c' : WCfg Q} (h : wstep δ c = some c') (X Y : Tape) :
    step δ (c.at X Y) = some (c'.at X Y) := by
  obtain ⟨l, r, q⟩ := c
  cases r with
  | nil => simp [wstep] at h
  | cons a r' =>
    simp only [wstep] at h
    cases hd : δ q a with
    | none => rw [hd] at h; cases h
    | some t =>
      obtain ⟨w, d, s⟩ := t
      rw [hd] at h
      cases d with
      | R =>
        cases h
        simp only [step, WCfg.at, app_cons, cons_zero, hd, tail_cons]
      | L =>
        cases l with
        | nil => cases h
        | cons b l' =>
          cases h
          simp only [step, WCfg.at, app_cons, cons_zero, hd, tail_cons]

/-- Run in the window until `stop` holds (checked after each step), with `fuel` steps at most; `n` counts steps. -/
def wrun (stop : WCfg Q → Bool) : Nat → Nat → WCfg Q → Option (Nat × WCfg Q)
  | 0, _, _ => none
  | fuel + 1, n, c =>
    match wstep δ c with
    | none => none
    | some c' => if stop c' then some (n + 1, c') else wrun stop fuel (n + 1) c'

theorem wrun_sound (stop : WCfg Q → Bool) :
    ∀ (fuel n : Nat) (c : WCfg Q) (m : Nat) (c' : WCfg Q), wrun δ stop fuel n c = some (m, c') →
      ∃ k, m = n + k ∧ ∀ X Y, steps δ k (c.at X Y) = some (c'.at X Y) := by
  intro fuel
  induction fuel with
  | zero => intro n c m c' h; cases h
  | succ fuel ih =>
    intro n c m c' h
    simp only [wrun] at h
    cases hs : wstep δ c with
    | none => rw [hs] at h; cases h
    | some c1 =>
      rw [hs] at h
      simp only at h
      by_cases hst : stop c1 = true
      · rw [ite_eq_left hst] at h
        cases h
        exact ⟨1, rfl, fun X Y => by rw [steps_succ_of_step δ 0 (wstep_sound δ hs X Y)]; rfl⟩
      · rw [ite_eq_right hst] at h
        obtain ⟨k, hk, hr⟩ := ih (n + 1) c1 m c' h
        exact ⟨k + 1, by omega, fun X Y => by rw [steps_succ_of_step δ k (wstep_sound δ hs X Y)]; exact hr X Y⟩

/-- The step from `(q, v)` goes right / left. -/
def goesR (q : Q) (v : Bool) : Bool :=
  match δ q v with
  | some (_, .R, _) => true
  | _ => false

def goesL (q : Q) (v : Bool) : Bool :=
  match δ q v with
  | some (_, .L, _) => true
  | _ => false

theorem not_goesL_of_goesR {q : Q} {v : Bool} (h : goesR δ q v = true) : goesL δ q v = false := by
  unfold goesR at h; unfold goesL
  split at h
  · rename_i heq; rw [heq]
  · cases h

theorem not_goesR_of_goesL {q : Q} {v : Bool} (h : goesL δ q v = true) : goesR δ q v = false := by
  unfold goesL at h; unfold goesR
  split at h
  · rename_i heq; rw [heq]
  · cases h

variable [DecidableEq Q]

/-- The right part is done: the head is on the base cell (the window's left list is empty) and either goes left
next or is at the end of the tick (`q0` on a 0). -/
def stopR (q0 : Q) (c : WCfg Q) : Bool :=
  match c.l, c.r with
  | [], v :: _ => (decide (c.st = q0) && v == false) || goesL δ c.st v
  | _, _ => false

/-- The left part is done: the head is on the base cell (the window's right list is that one cell). -/
def stopL (q0 : Q) (c : WCfg Q) : Bool :=
  match c.r with
  | [v] => (decide (c.st = q0) && v == false) || goesR δ c.st v
  | _ => false

/-- A visit of the right part from the base cell `v` in state `q`: steps, new right part, base cell, state. -/
def excR (fuel : Nat) (q0 : Q) (W : List Bool) (q : Q) (v : Bool) : Option (Nat × List Bool × Bool × Q) :=
  match wrun δ (stopR δ q0) fuel 0 ⟨[], v :: W, q⟩ with
  | some (n, ⟨[], v' :: W', q'⟩) => some (n, W', v', q')
  | _ => none

/-- A visit of the left part from the base cell `v` in state `q`. -/
def excL (fuel : Nat) (q0 : Q) (W : List Bool) (q : Q) (v : Bool) : Option (Nat × List Bool × Bool × Q) :=
  match wrun δ (stopL δ q0) fuel 0 ⟨W, [v], q⟩ with
  | some (n, ⟨W', [v'], q'⟩) => some (n, W', v', q')
  | _ => none

theorem excR_sound {fuel : Nat} {q0 : Q} {W W' : List Bool} {q q' : Q} {v v' : Bool} {n : Nat}
    (h : excR δ fuel q0 W q v = some (n, W', v', q')) (X Y : Tape) :
    steps δ n ⟨X, cons v (app W Y), q⟩ = some ⟨X, cons v' (app W' Y), q'⟩ := by
  unfold excR at h
  split at h
  · rename_i n0 W0 v0 q1 hw
    cases h
    obtain ⟨k, hk, hr⟩ := wrun_sound δ _ _ _ _ _ _ hw
    simp only [Nat.zero_add] at hk
    subst hk
    exact hr X Y
  · cases h

theorem excL_sound {fuel : Nat} {q0 : Q} {W W' : List Bool} {q q' : Q} {v v' : Bool} {n : Nat}
    (h : excL δ fuel q0 W q v = some (n, W', v', q')) (X Y : Tape) :
    steps δ n ⟨app W X, cons v Y, q⟩ = some ⟨app W' X, cons v' Y, q'⟩ := by
  unfold excL at h
  split at h
  · rename_i n0 W0 v0 q1 hw
    cases h
    obtain ⟨k, hk, hr⟩ := wrun_sound δ _ _ _ _ _ _ hw
    simp only [Nat.zero_add] at hk
    subst hk
    exact hr X Y
  · cases h

/-- One side (`right` or left) through the arrivals `P` at the base cell, from `(q, v)`: its steps and its new
cells.  A visit by the other side leaves this side as it is. -/
def side (q0 : Q) (right : Bool) (fuel : Nat) : List (Q × Bool) → List Bool → Q → Bool → Option (Nat × List Bool)
  | [], W, _, _ => some (0, W)
  | (q2, v2) :: P, W, q, v =>
    if (if right then goesR δ q v else goesL δ q v) then
      match (if right then excR δ fuel q0 W q v else excL δ fuel q0 W q v) with
      | some (n, W', v', q') =>
        if decide (q' = q2) && v' == v2 then
          match side q0 right fuel P W' q2 v2 with
          | some (m, W'') => some (n + m, W'')
          | none => none
        else none
      | none => none
    else if (if right then goesL δ q v else goesR δ q v) then side q0 right fuel P W q2 v2
    else none

/-- The last arrival. -/
def lastA : Q × Bool → List (Q × Bool) → Q × Bool
  | x, [] => x
  | _, y :: P => lastA y P

theorem side_sound (q0 : Q) (fuel : Nat) :
    ∀ (P : List (Q × Bool)) (WL WR WL' WR' : List Bool) (q : Q) (v : Bool) (cL cR : Nat),
      side δ q0 false fuel P WL q v = some (cL, WL') → side δ q0 true fuel P WR q v = some (cR, WR') →
      ∀ X Y, steps δ (cL + cR) ⟨app WL X, cons v (app WR Y), q⟩ =
        some ⟨app WL' X, cons (lastA (q, v) P).2 (app WR' Y), (lastA (q, v) P).1⟩ := by
  intro P
  induction P with
  | nil =>
    intro WL WR WL' WR' q v cL cR hL hR X Y
    simp only [side, Option.some.injEq, Prod.mk.injEq] at hL hR
    obtain ⟨rfl, rfl⟩ := hL; obtain ⟨rfl, rfl⟩ := hR
    rfl
  | cons a P ih =>
    obtain ⟨q2, v2⟩ := a
    intro WL WR WL' WR' q v cL cR hL hR X Y
    simp only [side, ite_true, ite_false, Bool.false_eq_true] at hL hR
    simp only [lastA]
    by_cases hg : goesR δ q v = true
    · -- the right part moves
      have hg' := not_goesL_of_goesR δ hg
      rw [ite_eq_left hg] at hR
      rw [hg'] at hL
      simp only [Bool.false_eq_true, ite_false, ite_eq_left hg] at hL
      cases he : excR δ fuel q0 WR q v with
      | none => rw [he] at hR; cases hR
      | some t =>
        obtain ⟨n, W1, v1, q1⟩ := t
        rw [he] at hR
        simp only at hR
        by_cases hc : (decide (q1 = q2) && v1 == v2) = true
        · rw [ite_eq_left hc] at hR
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          cases hs : side δ q0 true fuel P W1 q1 v1 with
          | none => rw [hs] at hR; cases hR
          | some t' =>
            obtain ⟨m, W2⟩ := t'
            rw [hs] at hR
            simp only [Option.some.injEq, Prod.mk.injEq] at hR
            obtain ⟨rfl, rfl⟩ := hR
            have h1 := excR_sound δ he (app WL X) Y
            have h2 := ih WL W1 WL' W2 q1 v1 cL m hL hs X Y
            have e : cL + (n + m) = n + (cL + m) := by omega
            rw [e]
            exact steps_seq δ h1 h2
        · rw [ite_eq_right hc] at hR; cases hR
    · have hgR : goesR δ q v = false := by simpa using hg
      rw [ite_eq_right hg] at hR
      by_cases hl : goesL δ q v = true
      · rw [ite_eq_left hl] at hR
        rw [ite_eq_left hl] at hL
        cases he : excL δ fuel q0 WL q v with
        | none => rw [he] at hL; cases hL
        | some t =>
          obtain ⟨n, W1, v1, q1⟩ := t
          rw [he] at hL
          simp only at hL
          by_cases hc : (decide (q1 = q2) && v1 == v2) = true
          · rw [ite_eq_left hc] at hL
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
            obtain ⟨rfl, rfl⟩ := hc
            cases hs : side δ q0 false fuel P W1 q1 v1 with
            | none => rw [hs] at hL; cases hL
            | some t' =>
              obtain ⟨m, W2⟩ := t'
              rw [hs] at hL
              simp only [Option.some.injEq, Prod.mk.injEq] at hL
              obtain ⟨rfl, rfl⟩ := hL
              have h1 := excL_sound δ he X (app WR Y)
              have h2 := ih W1 WR W2 WR' q1 v1 m cR hs hR X Y
              have e : n + m + cR = n + (m + cR) := by omega
              rw [e]
              exact steps_seq δ h1 h2
          · rw [ite_eq_right hc] at hL; cases hL
      · rw [ite_eq_right hl] at hR; cases hR

end

/-! ## Counters laid out on a side -/

/-- One digit: a single cell, or a pair of equal cells. -/
def blk (p : Bool) (b : Bool) : List Bool := if p then [b, b] else [b]

/-- The digits of `n` (least significant first), each followed by its gap. -/
def layD (p : Bool) : List (List Bool) → Nat → List Bool
  | [], _ => []
  | g :: gs, n => blk p (n % 2 == 1) ++ g ++ layD p gs (n / 2)

theorem two_pow_succ (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem mod_two_mul (x M : Nat) : x % (2 * M) = 2 * (x / 2 % M) + x % 2 := by
  have h1 := Nat.div_add_mod (x % (2 * M)) 2
  rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd x (Nat.dvd_mul_right 2 M)] at h1
  omega

theorem layD_mod (p : Bool) : ∀ (gs : List (List Bool)) (n m : Nat),
    n % 2 ^ gs.length = m % 2 ^ gs.length → layD p gs n = layD p gs m := by
  intro gs
  induction gs with
  | nil => intro n m _; rfl
  | cons g gs ih =>
    intro n m h
    simp only [List.length_cons, two_pow_succ] at h
    have h2 : n % 2 = m % 2 := by
      have := mod_two_mul n (2 ^ gs.length); have := mod_two_mul m (2 ^ gs.length); omega
    have h3 : n / 2 % 2 ^ gs.length = m / 2 % 2 ^ gs.length := by
      have := mod_two_mul n (2 ^ gs.length); have := mod_two_mul m (2 ^ gs.length); omega
    simp only [layD, h2, ih _ _ h3]

theorem layD_append (p : Bool) : ∀ (gs1 gs2 : List (List Bool)) (n : Nat),
    layD p (gs1 ++ gs2) n = layD p gs1 n ++ layD p gs2 (n / 2 ^ gs1.length) := by
  intro gs1
  induction gs1 with
  | nil => intro gs2 n; simp [layD]
  | cons g gs1 ih =>
    intro gs2 n
    simp only [List.cons_append, layD, ih, List.length_cons, List.append_assoc, Nat.div_div_eq_div_mul,
      two_pow_succ]

/-! ## Trailing ones and how often each carry length occurs -/

/-- The number of trailing 1 bits: the carry length of `n + 1`. -/
def tz1 (n : Nat) : Nat := if n % 2 = 1 then tz1 (n / 2) + 1 else 0
termination_by n
decreasing_by omega

theorem tz1_eq (n : Nat) : tz1 n = if n % 2 = 1 then tz1 (n / 2) + 1 else 0 := by
  rw [tz1]

theorem tz1_mod : ∀ (n x : Nat), x < n → x % 2 ^ (tz1 x + 1) = 2 ^ tz1 x - 1 := by
  intro n
  induction n with
  | zero => intro x h; omega
  | succ n ih =>
    intro x hx
    rw [tz1_eq]
    by_cases h : x % 2 = 1
    · rw [ite_eq_left h]
      have := ih (x / 2) (by omega)
      rw [two_pow_succ (tz1 (x / 2) + 1), mod_two_mul, this, h, two_pow_succ]
      have := Nat.two_pow_pos (tz1 (x / 2)); omega
    · rw [ite_eq_right h]; simp; omega

theorem tz1_of_mod : ∀ (k x : Nat), x % 2 ^ (k + 1) = 2 ^ k - 1 → tz1 x = k := by
  intro k
  induction k with
  | zero => intro x h; rw [tz1_eq]; simp at h; simp [h]
  | succ k ih =>
    intro x h
    rw [two_pow_succ (k + 1), mod_two_mul, two_pow_succ] at h
    have hp := Nat.two_pow_pos k
    have h1 : x % 2 = 1 := by have := Nat.mod_two_eq_zero_or_one x; omega
    have h2 : x / 2 % 2 ^ (k + 1) = 2 ^ k - 1 := by rw [two_pow_succ]; omega
    rw [tz1_eq, ite_eq_left h1, ih _ h2]

theorem tz1_lt {a n : Nat} (h : a + 1 < 2 ^ n) : tz1 a < n := by
  have hm := tz1_mod (a + 1) a (by omega)
  have hle := Nat.mod_le a (2 ^ (tz1 a + 1))
  apply Nat.lt_of_not_le
  intro hn
  have := Nat.pow_le_pow_right (show 0 < 2 by omega) hn
  omega

/-- How many `t` in `[a, a + d)` have `tz1 t = k`. -/
def cnt (a d k : Nat) : Nat := (a + d + 2 ^ k) / 2 ^ (k + 1) - (a + 2 ^ k) / 2 ^ (k + 1)

theorem div_succ_ind (x k : Nat) :
    (x + 2 ^ k + 1) / 2 ^ (k + 1) = (x + 2 ^ k) / 2 ^ (k + 1) + if tz1 x = k then 1 else 0 := by
  rw [Nat.succ_div]
  congr 1
  have hp := Nat.two_pow_pos k
  have hM : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have hr := Nat.mod_lt x (Nat.two_pow_pos (k + 1))
  have hx := Nat.div_add_mod x (2 ^ (k + 1))
  -- (x + 2^k + 1) % 2^(k+1) = (x % 2^(k+1) + 2^k + 1) % 2^(k+1)
  have hmod : (x + 2 ^ k + 1) % 2 ^ (k + 1) = (x % 2 ^ (k + 1) + 2 ^ k + 1) % 2 ^ (k + 1) := by
    conv => lhs; rw [← hx]
    rw [show 2 ^ (k + 1) * (x / 2 ^ (k + 1)) + x % 2 ^ (k + 1) + 2 ^ k + 1 =
      2 ^ (k + 1) * (x / 2 ^ (k + 1)) + (x % 2 ^ (k + 1) + 2 ^ k + 1) by omega, Nat.mul_add_mod]
  by_cases ht : tz1 x = k
  · rw [ite_eq_left ht]
    have := tz1_mod (x + 1) x (by omega)
    rw [ht] at this
    rw [ite_eq_left]
    apply Nat.dvd_of_mod_eq_zero
    rw [hmod, this, show 2 ^ k - 1 + 2 ^ k + 1 = 2 ^ (k + 1) by omega, Nat.mod_self]
  · rw [ite_eq_right ht, ite_eq_right]
    intro hd
    have h0 := Nat.mod_eq_zero_of_dvd hd
    rw [hmod] at h0
    apply ht
    apply tz1_of_mod
    by_cases hlt : x % 2 ^ (k + 1) + 2 ^ k + 1 < 2 ^ (k + 1)
    · rw [Nat.mod_eq_of_lt hlt] at h0; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h0
      omega

theorem cnt_succ (a d k : Nat) : cnt a (d + 1) k = cnt a d k + if tz1 (a + d) = k then 1 else 0 := by
  unfold cnt
  have h := div_succ_ind (a + d) k
  rw [show a + (d + 1) + 2 ^ k = a + d + 2 ^ k + 1 by omega, h]
  have hm : (a + 2 ^ k) / 2 ^ (k + 1) ≤ (a + d + 2 ^ k) / 2 ^ (k + 1) :=
    Nat.div_le_div_right (by omega)
  split <;> omega

theorem cnt_zero (a k : Nat) : cnt a 0 k = 0 := by simp [cnt]

/-- `∑ i, Cs[i] * cnt a d (k0 + i)`: the steps of `d` ticks from `a` when a carry of length `k` costs `Cs[k]`. -/
def csumA (a d : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, k0 => c * cnt a d k0 + csumA a d cs (k0 + 1)

def csum (Cs : List Nat) (a d : Nat) : Nat := csumA a d Cs 0

theorem csumA_succ (a d : Nat) : ∀ (Cs : List Nat) (k0 : Nat),
    csumA a (d + 1) Cs k0 = csumA a d Cs k0 + if k0 ≤ tz1 (a + d) then Cs.getD (tz1 (a + d) - k0) 0 else 0 := by
  intro Cs
  induction Cs with
  | nil => intro k0; simp [csumA]
  | cons c cs ih =>
    intro k0
    simp only [csumA, cnt_succ, ih]
    generalize tz1 (a + d) = t
    by_cases h1 : t = k0
    · subst h1
      have e1 : ¬ (t + 1 ≤ t) := by omega
      simp [e1, Nat.mul_add]; omega
    · rw [ite_eq_right h1]
      by_cases h2 : k0 + 1 ≤ t
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
        have : t - k0 = (t - (k0 + 1)) + 1 := by omega
        rw [this]; simp; omega
      · rw [ite_eq_right h2, ite_eq_right (by omega)]; simp

theorem csum_succ (Cs : List Nat) (a d : Nat) : csum Cs a (d + 1) = csum Cs a d + Cs.getD (tz1 (a + d)) 0 := by
  unfold csum; rw [csumA_succ]; simp

theorem csumA_zero (a : Nat) : ∀ (Cs : List Nat) (k0 : Nat), csumA a 0 Cs k0 = 0 := by
  intro Cs; induction Cs with
  | nil => intro; rfl
  | cons c cs ih => intro k0; simp [csumA, cnt_zero, ih]

/-! ## A tick and a batch of ticks -/

/-- A layout: at the left of the base cell `g0L` and the pair digits with their gaps; at the right of the base cell
`g0R` and the single digits with their gaps. -/
structure Lay where
  g0L : List Bool
  gsL : List (List Bool)
  g0R : List Bool
  gsR : List (List Bool)

/-- The configuration with counters `a` (left) and `b` (right), the head on the base cell (a 0) in `q0`. -/
def Lay.cfg (y : Lay) (q0 : Q) (a b : Nat) : FCfg Q :=
  ⟨y.g0L ++ layD true y.gsL a, false :: (y.g0R ++ layD false y.gsR b), q0⟩

/-- The left part up to digit `k` and its gap, with the low digits set to `n`. -/
def Lay.winL (y : Lay) (k n : Nat) : List Bool := y.g0L ++ layD true (y.gsL.take (k + 1)) n
def Lay.winR (y : Lay) (j n : Nat) : List Bool := y.g0R ++ layD false (y.gsR.take (j + 1)) n

section
variable (δ : Q → Bool → Option (Bool × Dir × Q)) [DecidableEq Q]

theorem split_lay (p : Bool) (g0 : List Bool) (gs : List (List Bool)) (k a : Nat) (hk : k < gs.length)
    (hm : a % 2 ^ (k + 1) = 2 ^ k - 1) :
    g0 ++ layD p gs a = (g0 ++ layD p (gs.take (k + 1)) (2 ^ k - 1)) ++ layD p (gs.drop (k + 1)) (a / 2 ^ (k + 1)) ∧
    g0 ++ layD p gs (a + 1) = (g0 ++ layD p (gs.take (k + 1)) (2 ^ k)) ++ layD p (gs.drop (k + 1)) (a / 2 ^ (k + 1)) := by
  have hl : (gs.take (k + 1)).length = k + 1 := by simp; omega
  have hp := Nat.two_pow_pos k
  have hM := two_pow_succ k
  have hx := Nat.div_add_mod a (2 ^ (k + 1))
  constructor
  · conv => lhs; rw [← List.take_append_drop (k + 1) gs]
    rw [layD_append, hl, List.append_assoc]
    congr 2
    apply layD_mod; rw [hl, hm, Nat.mod_eq_of_lt (by omega)]
  · conv => lhs; rw [← List.take_append_drop (k + 1) gs]
    rw [layD_append, hl, List.append_assoc]
    have e : a + 1 = 2 ^ (k + 1) * (a / 2 ^ (k + 1)) + 2 ^ k := by omega
    congr 2
    · apply layD_mod; rw [hl, e, Nat.mul_add_mod]
    · rw [e, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (show 2 ^ k < 2 ^ (k + 1) by omega)]; simp

/-- One tick: if the left part, checked for every carry length `k` (from `2^k - 1` to `2^k` in its low digits), and
the right part, checked likewise for every `j`, follow the same arrivals and end back at `(q0, 0)`, then from any
counter values the machine adds one to both, in `Gs[k] + Fs[j]` steps. -/
theorem tick (y : Lay) (q0 : Q) (fuel : Nat) (P : List (Q × Bool)) (Gs Fs : List Nat)
    (hP : lastA (q0, false) P = (q0, false))
    (hL : ∀ k, k < y.gsL.length → side δ q0 false fuel P (y.winL k (2 ^ k - 1)) q0 false = some (Gs.getD k 0, y.winL k (2 ^ k)))
    (hR : ∀ j, j < y.gsR.length → side δ q0 true fuel P (y.winR j (2 ^ j - 1)) q0 false = some (Fs.getD j 0, y.winR j (2 ^ j)))
    (a b : Nat) (ha : a + 1 < 2 ^ y.gsL.length) (hb : b + 1 < 2 ^ y.gsR.length) :
    steps δ (Gs.getD (tz1 a) 0 + Fs.getD (tz1 b) 0) (y.cfg q0 a b).toCfg = some (y.cfg q0 (a + 1) (b + 1)).toCfg := by
  have hk := tz1_lt ha
  have hj := tz1_lt hb
  obtain ⟨sa, sa'⟩ := split_lay true y.g0L y.gsL (tz1 a) a hk (tz1_mod (a + 1) a (by omega))
  obtain ⟨sb, sb'⟩ := split_lay false y.g0R y.gsR (tz1 b) b hj (tz1_mod (b + 1) b (by omega))
  have h := side_sound δ q0 fuel P _ _ _ _ q0 false _ _ (hL _ hk) (hR _ hj)
    (app (layD true (y.gsL.drop (tz1 a + 1)) (a / 2 ^ (tz1 a + 1))) blank)
    (app (layD false (y.gsR.drop (tz1 b + 1)) (b / 2 ^ (tz1 b + 1))) blank)
  rw [hP] at h
  simp only [Lay.winL, Lay.winR, ← app_app] at h
  simp only [Lay.cfg, FCfg.toCfg, sa, sa', sb, sb', app_cons, ← app_app]
  exact h

theorem batch (y : Lay) (q0 : Q) (fuel : Nat) (P : List (Q × Bool)) (Gs Fs : List Nat)
    (hP : lastA (q0, false) P = (q0, false))
    (hL : ∀ k, k < y.gsL.length → side δ q0 false fuel P (y.winL k (2 ^ k - 1)) q0 false = some (Gs.getD k 0, y.winL k (2 ^ k)))
    (hR : ∀ j, j < y.gsR.length → side δ q0 true fuel P (y.winR j (2 ^ j - 1)) q0 false = some (Fs.getD j 0, y.winR j (2 ^ j)))
    (a b : Nat) : ∀ d, a + d < 2 ^ y.gsL.length → b + d < 2 ^ y.gsR.length →
      steps δ (csum Gs a d + csum Fs b d) (y.cfg q0 a b).toCfg = some (y.cfg q0 (a + d) (b + d)).toCfg := by
  intro d
  induction d with
  | zero => intro _ _; simp [csum, csumA_zero]
  | succ d ih =>
    intro ha hb
    have h1 := ih (by omega) (by omega)
    have h2 := tick δ y q0 fuel P Gs Fs hP hL hR (a + d) (b + d) (by omega) (by omega)
    rw [csum_succ, csum_succ, show csum Gs a d + Gs.getD (tz1 (a + d)) 0 + (csum Fs b d + Fs.getD (tz1 (b + d)) 0)
      = (csum Gs a d + csum Fs b d) + (Gs.getD (tz1 (a + d)) 0 + Fs.getD (tz1 (b + d)) 0) by omega]
    rw [show a + (d + 1) = a + d + 1 by omega, show b + (d + 1) = b + d + 1 by omega]
    exact steps_seq δ h1 h2

end

end TM
