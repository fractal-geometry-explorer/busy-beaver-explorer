import Walk

/-!
# 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA: every level is a prefix of one orbit of one digit map

On a long tail the walk of `Walk.lean` (the proved table) is, phase by phase, the map

    fd (10a + d) = 31a + dK (d / 2),   dK = 15, 27, 47, 35, 36,

on a single number x, which stands for the phase end `(10 + 31 (x / 10), (x % 10) / 2)` (`enc`): `digit_step`.  One
step of `fd` is one phase (two for r = 1, 2, whose resets go straight into an r = 0 reset) and uses `dCost r` = 4, 5,
8, 3, 2 words `1110` of the tail.  Every level starts at `(17, 0, tl T s)`, which after its first phase is the state
x = 22 with T - 4 words (`level_start`).  So **every level runs a prefix of the same orbit 22, 697, 2162, ... of
`fd`**, and stops at the first state whose phase needs more words than are left (`dstop`, `dstop_run`).

`level1_digit` (by `decide`): with the 6801 words of level 1 the orbit stops after 1566 steps at r = 3 with no word
left, as `level1_end'` found with the phase map.  `halts_iff_level2_end`: **the machine halts from blank tape if and
only if the walk halts from the state where the orbit of 22 stops with the budget B = 26 + 31 (X1 / 10) of level 2**
(X1 the state where level 1 stopped).  B has 772 digits, so that state is about 2·10^770 steps of `fd` along the
orbit: no closed form is known (see the README: the low digits of the orbit are the digits of a rational base 31/10
expansion), and what the walk does from there is decided by the row of that state.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace H66813

open TM

def dK : Nat → Nat
  | 0 => 15 | 1 => 27 | 2 => 47 | 3 => 35 | _ => 36

def dCost : Nat → Nat
  | 0 => 4 | 1 => 5 | 2 => 8 | 3 => 3 | _ => 2

def dLen : Nat → Nat
  | 0 => 2 | 1 => 3 | 2 => 3 | 3 => 2 | _ => 2

/-- The r of a state. -/
def dr (x : Nat) : Nat := x % 10 / 2

/-- The digit map. -/
def fd (x : Nat) : Nat := 31 * (x / 10) + dK (dr x)

/-- The phase end a state stands for. -/
def enc (s : Suf) (x t : Nat) : W := (10 + 31 * (x / 10), dr x, .long s t)

/-- Run the orbit from x with t words until the next phase needs more than are left (fuel bounds the steps). -/
def dstop : Nat → Nat → Nat → Nat × Nat
  | 0, x, t => (x, t)
  | f + 1, x, t => if dCost (dr x) ≤ t then dstop f (fd x) (t - dCost (dr x)) else (x, t)

/-- What comes after k walk steps. -/
def bindR : Res → (W → Res) → Res
  | .go v, g => g v
  | r, _ => r

theorem runW_add (a : Nat) (w : W) : ∀ b, runW (a + b) w = bindR (runW a w) (runW b) := by
  intro b
  induction b with
  | zero => cases h : runW a w <;> simp [runW, bindR]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega]
    simp only [runW]
    rw [ih]
    cases h : runW a w <;> simp [bindR]

theorem runW_go {a b : Nat} {w w' : W} (h : runW a w = .go w') : runW (a + b) w = runW b w' := by
  rw [runW_add, h]; rfl

theorem runW_halt {a b : Nat} {w : W} (h : runW a w = .halt) : runW (a + b) w = .halt := by
  rw [runW_add, h]; rfl

/-- Halting of the walk is the same from a record and from any record the walk reaches. -/
theorem walk_halts_iff {j : Nat} {w w' : W} (h : runW j w = .go w') :
    (∃ k, runW k w = .halt) ↔ (∃ k, runW k w' = .halt) := by
  constructor
  · rintro ⟨k, hk⟩
    by_cases hkj : j ≤ k
    · refine ⟨k - j, ?_⟩
      have := runW_go (b := k - j) h
      rw [show j + (k - j) = k by omega, hk] at this
      exact this.symm
    · have := runW_halt (b := j - k) hk
      rw [show k + (j - k) = j by omega, h] at this
      cases this
  · rintro ⟨k, hk⟩
    exact ⟨j + k, by rw [runW_go h]; exact hk⟩

theorem runW_one (w : W) : runW 1 w = wstep w := rfl

theorem runW_seq (a : Nat) (w : W) : runW (a + 1) w = bindR (runW a w) wstep := by
  cases h : runW a w <;> simp [runW, h, bindR]

theorem ws_period (n m : Nat) (s : Suf) (t : Nat) (hm : 5 ≤ m) :
    wstep (n, m, .long s t) = .go (n + 31 * (m / 5), m % 5, .long s t) := by
  simp [wstep, hm]

theorem ws_reset0 (n : Nat) (s : Suf) (t : Nat) (ht : 4 ≤ t) :
    wstep (n, 0, .long s t) = .go (10, (n + 5) / 2, .long s (t - 4)) := by
  simp [wstep, wlong, need, reset, ofReset, ht]

theorem ws_reset1 (n : Nat) (s : Suf) (t : Nat) (ht : 1 ≤ t) :
    wstep (n, 1, .long s t) = .go (n + 12, 0, .long s (t - 1)) := by
  simp [wstep, wlong, need, reset, ofReset, ht]

theorem ws_reset2 (n : Nat) (s : Suf) (t : Nat) (hn : 1 ≤ n) (ht : 4 ≤ t) :
    wstep (n, 2, .long s t) = .go (n + 32, 0, .long s (t - 4)) := by
  simp [wstep, wlong, need, reset, ofReset, ht, hn]

theorem ws_reset3 (n : Nat) (s : Suf) (t : Nat) (ht : 3 ≤ t) :
    wstep (n, 3, .long s t) = .go (10, (n + 25) / 2, .long s (t - 3)) := by
  simp [wstep, wlong, need, reset, ofReset, ht]

theorem ws_reset4 (n : Nat) (s : Suf) (t : Nat) (ht : 2 ≤ t) :
    wstep (n, 4, .long s t) = .go (10, (n + 26) / 2, .long s (t - 2)) := by
  simp [wstep, wlong, need, reset, ofReset, ht]

theorem divfix (u : Nat) : u / 2 / 5 = u / 10 ∧ u / 2 % 5 = u % 10 / 2 := by
  refine ⟨by rw [Nat.div_div_eq_div_mul], ?_⟩
  rw [show (10 : Nat) = 2 * 5 by rfl, Nat.mod_mul_right_div_self]

/-- The phase from (10 + 31a, r) with enough words, in numbers. -/
theorem digit_phase (s : Suf) (a r t : Nat) (hr : r < 5) (ht : dCost r ≤ t) :
    runW (dLen r) (10 + 31 * a, r, .long s t) =
      .go (10 + 31 * ((31 * a + dK r) / 10), (31 * a + dK r) % 10 / 2, .long s (t - dCost r)) := by
  match r, hr, ht with
  | 0, _, ht =>
    simp only [dCost] at ht
    simp only [dLen, dK, dCost]
    rw [runW_seq, runW_one, ws_reset0 _ _ _ ht, bindR, ws_period _ _ _ _ (by omega)]
    simp only [Res.go.injEq, Prod.mk.injEq]
    rw [show 10 + 31 * a + 5 = 31 * a + 15 by omega]
    obtain ⟨h1, h2⟩ := divfix (31 * a + 15)
    simp [h1, h2] <;> omega
  | 1, _, ht =>
    simp only [dCost] at ht
    simp only [dLen, dK, dCost]
    rw [runW_seq, runW_seq, runW_one, ws_reset1 _ _ _ (by omega), bindR, ws_reset0 _ _ _ (by omega), bindR,
      ws_period _ _ _ _ (by omega)]
    simp only [Res.go.injEq, Prod.mk.injEq]
    rw [show 10 + 31 * a + 12 + 5 = 31 * a + 27 by omega]
    obtain ⟨h1, h2⟩ := divfix (31 * a + 27)
    simp [h1, h2] <;> omega
  | 2, _, ht =>
    simp only [dCost] at ht
    simp only [dLen, dK, dCost]
    rw [runW_seq, runW_seq, runW_one, ws_reset2 _ _ _ (by omega) (by omega), bindR, ws_reset0 _ _ _ (by omega),
      bindR, ws_period _ _ _ _ (by omega)]
    simp only [Res.go.injEq, Prod.mk.injEq, Tl.long.injEq]
    rw [show 10 + 31 * a + 32 + 5 = 31 * a + 47 by omega]
    obtain ⟨h1, h2⟩ := divfix (31 * a + 47)
    simp [h1, h2] <;> omega
  | 3, _, ht =>
    simp only [dCost] at ht
    simp only [dLen, dK, dCost]
    rw [runW_seq, runW_one, ws_reset3 _ _ _ ht, bindR, ws_period _ _ _ _ (by omega)]
    simp only [Res.go.injEq, Prod.mk.injEq]
    rw [show 10 + 31 * a + 25 = 31 * a + 35 by omega]
    obtain ⟨h1, h2⟩ := divfix (31 * a + 35)
    simp [h1, h2] <;> omega
  | 4, _, ht =>
    simp only [dCost] at ht
    simp only [dLen, dK, dCost]
    rw [runW_seq, runW_one, ws_reset4 _ _ _ ht, bindR, ws_period _ _ _ _ (by omega)]
    simp only [Res.go.injEq, Prod.mk.injEq]
    rw [show 10 + 31 * a + 26 = 31 * a + 36 by omega]
    obtain ⟨h1, h2⟩ := divfix (31 * a + 36)
    simp [h1, h2] <;> omega

/-- One step of the digit map is one phase (r = 0, 3, 4) or two (r = 1, 2) of the walk, for every suffix. -/
theorem digit_step (s : Suf) (x t : Nat) (ht : dCost (dr x) ≤ t) :
    runW (dLen (dr x)) (enc s x t) = .go (enc s (fd x) (t - dCost (dr x))) := by
  have e := digit_phase s (x / 10) (dr x) t (by unfold dr; omega) ht
  unfold enc fd
  rw [e]
  unfold dr
  rfl

/-- The walk follows the orbit until it stops. -/
theorem dstop_run (s : Suf) : ∀ f x t, ∃ j, runW j (enc s x t) = .go (enc s (dstop f x t).1 (dstop f x t).2) := by
  intro f
  induction f with
  | zero => intro x t; exact ⟨0, rfl⟩
  | succ f ih =>
    intro x t
    unfold dstop
    split
    · rename_i h
      obtain ⟨j, hj⟩ := ih (fd x) (t - dCost (dr x))
      exact ⟨dLen (dr x) + j, by rw [runW_go (digit_step s x t h)]; exact hj⟩
    · exact ⟨0, rfl⟩

theorem dCost_ge (r : Nat) : 2 ≤ dCost r := by
  unfold dCost; split <;> omega

/-- With fuel at least the words, the orbit really stops: the next phase needs more words than are left. -/
theorem dstop_stops : ∀ f x t, t ≤ f → (dstop f x t).2 < dCost (dr (dstop f x t).1) := by
  intro f
  induction f with
  | zero => intro x t ht; simp only [dstop]; have := dCost_ge (dr x); omega
  | succ f ih =>
    intro x t ht
    unfold dstop
    split
    · rename_i h; have := dCost_ge (dr x); exact ih _ _ (by omega)
    · rename_i h; simp only; omega

/-- A level starts at (17, 0, tl T s); after its first phase it is the state 22 with T - 4 words. -/
theorem level_start (s : Suf) (T : Nat) (hT : 4 ≤ T) : runW 2 (17, 0, .long s T) = .go (enc s 22 (T - 4)) := by
  rw [runW_seq, runW_one, ws_reset0 _ _ _ hT, bindR, ws_period _ _ _ _ (by omega)]
  rfl

/-- Level 1 (6801 words after its first phase) is the first 1566 steps of the orbit of 22: it stops at r = 3 with no
word left, as `level1_end'` found with the phase map. -/
theorem level1_digit : (dstop 6801 22 6801).2 = 0 ∧ dr (dstop 6801 22 6801).1 = 3 ∧
    (10 + 31 * ((dstop 6801 22 6801).1 / 10)) % 100 = 63 := by decide

/-- The state where level 1 stops. -/
def X1 : Nat := (dstop 6801 22 6801).1

/-- The budget of level 2 after its first phase: the 772-digit n where level 1 ends, plus 16. -/
def B2 : Nat := 10 + 31 * (X1 / 10) + 16

/-- The state where level 2 stops, and the words left there. -/
def end2 : Nat × Nat := dstop B2 22 B2

theorem end2_stops : end2.2 < dCost (dr end2.1) := dstop_stops _ _ _ (Nat.le_refl _)

/-- **The machine halts from blank tape if and only if the walk halts from the end of level 2**, the state where
the orbit of 22 under `fd` stops with the budget `B2` (772 digits). -/
theorem halts_iff_level2_end : Halts trans init ↔ ∃ k, runW k (enc .s2 end2.1 end2.2) = .halt := by
  rw [halts_iff_walk]
  -- level 1: first phase, then the orbit
  have h1 : runW 2 (17, 0, .long .s1 6805) = .go (enc .s1 22 6801) := level_start .s1 6805 (by omega)
  obtain ⟨j1, hj1⟩ := dstop_run .s1 6801 22 6801
  have hl1 := level1_digit
  -- the end of level 1 goes to level 2 (row (s1, r = 3, t = 0))
  have h2 : runW 1 (enc .s1 X1 0) = .go (17, 0, .long .s2 (10 + 31 * (X1 / 10) + 20)) := by
    have e3 : dr X1 = 3 := hl1.2.1
    simp only [runW, enc, e3, wstep, wlong, need, nearL, row_s1_0_3]
    rw [ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega)]
  have h3 : runW 2 (17, 0, .long .s2 (10 + 31 * (X1 / 10) + 20)) = .go (enc .s2 22 B2) := by
    rw [level_start .s2 _ (by omega)]
    unfold B2; congr 3
  obtain ⟨j2, hj2⟩ := dstop_run .s2 B2 22 B2
  have e0 : (dstop 6801 22 6801).2 = 0 := hl1.1
  rw [walk_halts_iff h1]
  rw [show (dstop 6801 22 6801) = (X1, 0) by
        unfold X1; rw [← e0]] at hj1
  rw [walk_halts_iff hj1, walk_halts_iff h2, walk_halts_iff h3, walk_halts_iff hj2]
  rfl

end H66813
