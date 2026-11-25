import Front
import Advance

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: the rules of the symbolic engine, as lemmas

`py/sym_engine.py` runs the transient on states whose entries are affine in parameters, whose lists hold runs of
equal blocks and end in a *history*: digits known only by their number.  Here each of its rules is a lemma about the
machine, so that a case of `py/sym_law.py` becomes a chain of them (`py/gen_front.py`):

* `RC c c'`: the machine goes from `c` to `c'`; the moves of the pass machine (`RC.pnext`, `RC.pdone`), the left
  sweep from a moment (`RC.start`), and a stretch of regular sub-rounds as arithmetic on the list's time left
  (`RC.arith`, from `advance_to`).
* the history `hist q D` (digits `D`, then the first block `3q`): `hist_dbl` (3z more cells on its first block
  multiply its number by `2^z`); reading a digit is a case split on `D`.
* the counter: `giter_chunks` (j chunks of 2^q sub-rounds at once) and `giter_pow_sub1` (2^q - 1 sub-rounds).
-/

namespace H4320

open TM

/-! ## Reaching a configuration -/

/-- The machine goes from `c` to `c'`. -/
def RC (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem RC.refl (c : Config) : RC c c := ⟨0, rfl⟩

theorem RC.trans {a b c : Config} (h : RC a b) (h' : RC b c) : RC a c := by
  obtain ⟨n, hn⟩ := h; obtain ⟨m, hm⟩ := h'
  exact ⟨n + m, steps_seq H4320.trans hn hm⟩

theorem RC.pnext {s s' : PS} {n : Nat} (h : pstep s = .next s' n) : RC s.cfg s'.cfg := ⟨n, pstep_next s s' n h⟩

theorem RC.pdone {s : PS} {bs : List Nat} {l : Nat} {us : List Nat} {n : Nat} (h : pstep s = .done bs l us n) :
    RC s.cfg (gcfg bs l us) := ⟨n, pstep_done s bs l us n h⟩

/-- `k + 1` moves of the pass machine: the first `k` give next states, the last gives the result. -/
def prunsR : Nat → PS → Res
  | 0, s => pstep s
  | k + 1, s => match pstep s with
    | .next s' _ => prunsR k s'
    | r => r

theorem RC.prn : ∀ (k : Nat) {s s' : PS} {n : Nat}, prunsR k s = .next s' n → RC s.cfg s'.cfg
  | 0, _, _, _, h => RC.pnext h
  | k + 1, s, s', n, h => by
    unfold prunsR at h
    split at h
    · rename_i s1 n1 e; exact RC.trans (RC.pnext e) (RC.prn k h)
    · rename_i r hr; exact absurd h (hr _ _)

theorem RC.prd : ∀ (k : Nat) {s : PS} {bs : List Nat} {l : Nat} {us : List Nat} {n : Nat},
    prunsR k s = .done bs l us n → RC s.cfg (gcfg bs l us)
  | 0, _, _, _, _, _, h => RC.pdone h
  | k + 1, s, bs, l, us, n, h => by
    unfold prunsR at h
    split at h
    · rename_i s1 n1 e; exact RC.trans (RC.pnext e) (RC.prd k h)
    · exact RC.pdone h

theorem RC.start {bs : List Nat} {l : Nat} {us : List Nat} {s : PS} {n : Nat} (h : startPS bs l us = some (s, n)) :
    RC (gcfg bs l us) s.cfg := ⟨n, startPS_sound bs l us s n h⟩

theorem Reach.rc {s t : PS} (h : Reach s t) : RC s.cfg t.cfg := h

theorem ReachM.rc {s : PS} {bs : List Nat} {l : Nat} {us : List Nat} (h : ReachM s bs l us) :
    RC s.cfg (gcfg bs l us) := h

/-! ## The list as a number -/

/-- Every number is the time left of some list of digits. -/
theorem T_surj (h : Nat) : ∃ D, T D = h := by
  induction h using Nat.strongRecOn with
  | ind h ih =>
    obtain ⟨k, hk | hk⟩ : ∃ k, h = 2 * k ∨ h = 2 * k + 1 := ⟨h / 2, by omega⟩ <;> subst hk
    · cases k with
      | zero => exact ⟨[], rfl⟩
      | succ k =>
        obtain ⟨D, hD⟩ := ih (k + 1) (by omega)
        cases D with
        | nil => simp [T] at hD
        | cons x r => exact ⟨(x + 1) :: r, by simp only [T] at hD ⊢; rw [Nat.pow_succ, ← hD]; grind⟩
    · obtain ⟨D, hD⟩ := ih k (by omega)
      exact ⟨0 :: D, by simp [T, hD]; omega⟩

/-- The time left is below `2^sig` and at least `2^(sig - 1)`. -/
theorem T_bounds : ∀ D : List Nat, T D < 2 ^ sig D ∧ 2 ^ sig D ≤ 2 * T D + 1
  | [] => by simp [T, sig]
  | x :: r => by
    obtain ⟨h1, h2⟩ := T_bounds r
    have e : sig (x :: r) = x + 1 + sig r := by simp only [sig, List.map_cons, List.sum_cons]
    rw [e, Nat.pow_add, Nat.pow_add, Nat.pow_one]
    simp only [T]
    refine ⟨?_, ?_⟩
    have hx : 0 < 2 ^ x := Nat.pow_pos (by omega)
    · have : 1 + 2 * T r < 2 * 2 ^ sig r := by omega
      calc 2 ^ x * (1 + 2 * T r) < 2 ^ x * (2 * 2 ^ sig r) := Nat.mul_lt_mul_of_pos_left this hx
        _ = 2 ^ x * 2 * 2 ^ sig r := by rw [Nat.mul_assoc]
    · have : 2 ^ x * 2 * 2 ^ sig r ≤ 2 * (2 ^ x * (1 + 2 * T r)) := by
        rw [Nat.mul_comm (2 ^ x) 2, Nat.mul_assoc]
        exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by omega))
      omega

theorem sig_le_of_T_le {A B : List Nat} (h : T A ≤ T B) : sig A ≤ sig B := by
  obtain ⟨_, a2⟩ := T_bounds A
  obtain ⟨b1, _⟩ := T_bounds B
  have : 2 ^ sig A < 2 ^ (sig B + 1) := by rw [Nat.pow_succ]; omega
  have := (Nat.pow_lt_pow_iff_right (show 1 < 2 by omega)).mp this
  omega

/-- **A stretch of regular sub-rounds as arithmetic.**  `N` sub-rounds from the digits `F ++ D` to `F' ++ D'`, where
only the number `h'` of the new history `D'` is given: such a `D'` exists, with the first block fixed by the mass. -/
theorem RC.arith (N q : Nat) (F F' D : List Nat) (h' : Nat) (x y : Nat × List Nat)
    (hT : T F' + 2 ^ sig F' * h' + N = T F + 2 ^ sig F * T D) (hy : giter N x = some y) :
    ∃ q' D', T D' = h' ∧ mass q' (F' ++ D') = mass q (F ++ D) ∧
      RC (gcfg (encBlocks q (F ++ D)) x.1 x.2) (gcfg (encBlocks q' (F' ++ D')) y.1 y.2) := by
  obtain ⟨D', hD'⟩ := T_surj h'
  have hT' : T (F' ++ D') + N = T (F ++ D) := by rw [T_append, T_append, hD']; omega
  have hs : sig (F' ++ D') ≤ sig (F ++ D) := sig_le_of_T_le (by omega)
  have hm : mass q (F ++ D) = q + sig (F ++ D) := by simp only [mass, sig]
  refine ⟨q + sig (F ++ D) - sig (F' ++ D'), D', hD', ?_, ?_⟩
  · simp only [mass, sig] at hm hs ⊢; omega
  · have h := advance_to N q (q + sig (F ++ D) - sig (F' ++ D')) (F ++ D) (F' ++ D') x y hT'
      (by simp only [mass, sig] at hm hs ⊢; omega) hy
    rw [enc_gcfg, enc_gcfg] at h
    exact h

/-! ## The history -/

/-- The history: digits `D` (blocks `3d + 2`), then the first block `3q`. -/
abbrev hist (q : Nat) (D : List Nat) : List Nat := encBlocks q D

/-- `3z` more cells on the history's first block multiply its number by `2^z` (on the first block `3q` itself, when
there are no digits, the number stays 0). -/
theorem hist_dbl (z q : Nat) (D : List Nat) : ∃ q' D', ((hist q D).headD 0 + 3 * z) :: (hist q D).tail = hist q' D' ∧
    T D' = 2 ^ z * T D ∧ mass q' D' = mass q D + z := by
  cases D with
  | nil => exact ⟨q + z, [], by simp [encBlocks]; omega, by simp [T], by simp [mass]⟩
  | cons d r =>
    refine ⟨q, (d + z) :: r, by simp [encBlocks]; omega, ?_, by simp [mass]; omega⟩
    simp only [T, Nat.pow_add]; grind

theorem hist_cons (q d : Nat) (D : List Nat) : hist q (d :: D) = (3 * d + 2) :: hist q D := rfl

/-! ## The counter, many steps at once -/

/-- `2^q - 1` steps from the last block `4q + 1`: the low `q` bits all become 1. -/
theorem giter_pow_sub1 : ∀ (q : Nat) (us : List Nat), giter (2 ^ q - 1) (4 * q + 1, us) = some (1, List.replicate q 3 ++ us)
  | 0, us => rfl
  | q + 1, us => by
    have h1 := giter_scale q (5, us) (1, 3 :: us) rfl
    have h2 := giter_pow_sub1 q (3 :: us)
    rw [show 2 ^ (q + 1) - 1 = 2 ^ q + (2 ^ q - 1) by rw [Nat.pow_succ]; have : 0 < 2 ^ q := Nat.pow_pos (by omega); omega,
      giter_add]
    simp only at h1
    rw [show 4 * (q + 1) + 1 = 5 + 4 * q by omega, h1, Option.bind_some, show 1 + 4 * q = 4 * q + 1 by omega, h2]
    simp [List.replicate_succ']

/-- **j chunks at once.**  From the last block `4q + 1` and a first gap `4j + r`, `2^(q+j) - 2^q` steps take the
gap's `4j` cells into the last block. -/
theorem giter_chunks : ∀ (j q r : Nat) (us : List Nat),
    giter (2 ^ (q + j) - 2 ^ q) (4 * q + 1, (4 * j + r) :: us) = some (4 * (q + j) + 1, r :: us)
  | 0, q, r, us => by simp [giter]
  | j + 1, q, r, us => by
    have h1 := giter_scale q (1, (4 * (j + 1) + r) :: us) (5, (4 * j + r) :: us)
      (by simp only [gstep, show 4 * (j + 1) + r = (4 * j + r) + 4 by omega]; rfl)
    have h2 := giter_chunks j (q + 1) r us
    have p1 : 0 < 2 ^ q := Nat.pow_pos (by omega)
    have p2 : 2 ^ (q + 1) ≤ 2 ^ (q + 1 + j) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [show 2 ^ (q + (j + 1)) - 2 ^ q = 2 ^ q + (2 ^ (q + 1 + j) - 2 ^ (q + 1)) by
        rw [show q + (j + 1) = q + 1 + j by omega]; rw [Nat.pow_succ] at p2 ⊢; omega, giter_add]
    simp only at h1
    rw [show 1 + 4 * q = 4 * q + 1 by omega] at h1
    rw [h1, Option.bind_some, show 5 + 4 * q = 4 * (q + 1) + 1 by omega, h2,
      show q + 1 + j = q + (j + 1) by omega]

/-! ## Helpers for the generated proofs -/

/-- Phase A on `3c + r` ones (`c ≥ 1`): `c` blocks of 2 at once. -/
theorem RC.arun (lb us : List Nat) (K c r : Nat) (h : K = 3 * c + r) (hc : 1 ≤ c) (hr : r < 3) :
    RC (PS.cfg ⟨lb, .A, K, us⟩) (PS.cfg ⟨List.replicate c 2 ++ lb, .A, r, us⟩) := by
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  subst h
  refine RC.pnext (n := 3 * (c + 1)) ?_
  rw [show 3 * (c + 1) + r = (3 * c + r) + 3 by omega]
  simp only [pstep]
  rw [show (3 * c + r + 3) / 3 = c + 1 by omega, show (3 * c + r + 3) % 3 = r by omega]

theorem RC.cast {a b c : Config} (h : RC a b) (e : b = c) : RC a c := e ▸ h

theorem sig_nil : sig [] = 0 := rfl
theorem sig_cons (x : Nat) (r : List Nat) : sig (x :: r) = x + 1 + sig r := by simp [sig]
theorem sig_append (a b : List Nat) : sig (a ++ b) = sig a + sig b := by simp [sig]
theorem sig_rep0 (c : Nat) : sig (List.replicate c 0) = c := by
  induction c with
  | zero => rfl
  | succ c ih => rw [List.replicate_succ, sig_cons, ih]; omega
theorem T_rep0 (c : Nat) : T (List.replicate c 0) + 1 = 2 ^ c := by
  have := T_zeros c []; simpa [T] using this
theorem T_cons (x : Nat) (r : List Nat) : T (x :: r) = 2 ^ x * (1 + 2 * T r) := rfl
theorem T_nil : T [] = 0 := rfl
theorem map_rep0 (c : Nat) : List.map (fun d => 3 * d + 2) (List.replicate c 0) = List.replicate c 2 := by
  simp [List.map_replicate]

/-- The time left of a list of `L` digits is at least `2^L - 1`. -/
theorem T_len : ∀ D : List Nat, 2 ^ D.length ≤ T D + 1
  | [] => by simp [T]
  | x :: r => by
    have := T_len r
    have hx : 1 ≤ 2 ^ x := Nat.one_le_two_pow
    simp only [List.length_cons, Nat.pow_succ, T]
    have : 1 + 2 * T r ≤ 2 ^ x * (1 + 2 * T r) := Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem RC.castl {a a' b : Config} (e : a = a') (h : RC a' b) : RC a b := e ▸ h

/-- Reaching a configuration with a property: the form of every case of the analysis. -/
def Lands (a : Config) (P : Config → Prop) : Prop := ∃ c, RC a c ∧ P c

theorem Lands.trans {a b : Config} {P : Config → Prop} (h : RC a b) (h' : Lands b P) : Lands a P := by
  obtain ⟨c, hc, hP⟩ := h'; exact ⟨c, RC.trans h hc, hP⟩

theorem Lands.here {a : Config} {P : Config → Prop} (h : P a) : Lands a P := ⟨a, RC.refl a, h⟩

theorem Lands.castr {a a' : Config} {P : Config → Prop} (e : a = a') (h : P a') : Lands a P := ⟨a, RC.refl a, e ▸ h⟩

theorem Lands.fin {a : PS} {P : Config → Prop} (b : PS) (e : a = b) (h : P b.cfg) : Lands a.cfg P := e ▸ Lands.here h

/-! ## Borrows into the history -/

/-- Half the time left, as a list. -/
def half : List Nat → List Nat
  | [] => []
  | 0 :: r => r
  | (x + 1) :: r => x :: r

theorem T_half : ∀ D : List Nat, T (half D) = T D / 2
  | [] => rfl
  | 0 :: r => by simp only [half, T, Nat.pow_zero, Nat.one_mul]; omega
  | (x + 1) :: r => by simp only [half, T, Nat.pow_succ]; rw [Nat.mul_comm (2 ^ x) 2, Nat.mul_assoc]; omega

theorem len_half : ∀ D : List Nat, D.length ≤ (half D).length + 1 ∧ (half D).length ≤ D.length
  | [] => by simp [half]
  | 0 :: r => by simp [half]
  | (x + 1) :: r => by simp [half]

def halfk : Nat → List Nat → List Nat
  | 0, D => D
  | k + 1, D => halfk k (half D)

theorem T_halfk : ∀ (k : Nat) (D : List Nat), T (halfk k D) = T D / 2 ^ k
  | 0, D => by simp [halfk]
  | k + 1, D => by rw [halfk, T_halfk k, T_half, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem len_halfk : ∀ (k : Nat) (D : List Nat), D.length ≤ (halfk k D).length + k ∧ (halfk k D).length ≤ D.length
  | 0, D => by simp [halfk]
  | k + 1, D => by
    have := len_halfk k (half D); have := len_half D; simp only [halfk]; omega

/-- Twice the time left. -/
def dbl1 : List Nat → List Nat
  | [] => []
  | y :: r => (y + 1) :: r

theorem T_dbl1 : ∀ D : List Nat, T (dbl1 D) = 2 * T D
  | [] => rfl
  | y :: r => by simp only [dbl1, T, Nat.pow_succ]; rw [Nat.mul_comm (2 ^ y) 2, Nat.mul_assoc]

/-- The time left less one. -/
def dec : List Nat → List Nat
  | [] => []
  | 0 :: r => dbl1 r
  | (x + 1) :: r => List.replicate (x + 1) 0 ++ dbl1 r

theorem T_dec : ∀ D : List Nat, T (dec D) + 1 = T D ∨ D = []
  | [] => Or.inr rfl
  | 0 :: r => by left; simp only [dec, T_dbl1, T, Nat.pow_zero, Nat.one_mul]; omega
  | (x + 1) :: r => by
    left
    have h1 := T_rep0 (x + 1)
    simp only [dec, T_append, sig_rep0, T_dbl1, T]
    rw [← h1]; grind

theorem len_dec : ∀ D : List Nat, D.length ≤ (dec D).length + 1
  | [] => by simp [dec]
  | 0 :: r => by cases r <;> simp [dec, dbl1]
  | (x + 1) :: r => by cases r <;> simp [dec, dbl1]

theorem len_pred {A B : List Nat} (h : T A + 1 = T B) : B.length ≤ A.length + 1 := by
  rcases T_dec B with h' | h'
  · have := T_inj A (dec B) (by omega); subst this; exact len_dec B
  · subst h'; simp [T] at h

theorem T_ge_pow (D : List Nat) (e : Nat) (h : e < D.length) : 2 ^ e ≤ T D := by
  have h1 := T_len D
  have h2 : 2 ^ (e + 1) ≤ 2 ^ D.length := Nat.pow_le_pow_right (by omega) h
  have h3 : 0 < 2 ^ e := Nat.two_pow_pos e
  rw [Nat.pow_succ] at h2; omega

/-- A borrow: taking `2^e - c` (`c ≤ 2^e`) from a history keeps its digits above `e`, but one. -/
theorem borrow_core (D : List Nat) (c e K : Nat) (hc : c ≤ 2 ^ e) (hb : 2 ^ e ≤ T D)
    (hQ : D.length ≤ (halfk (e + 1) D).length + K) :
    ∃ D', T D' + 2 ^ e = T D + c ∧ D.length ≤ D'.length + K + 1 := by
  obtain ⟨D', hD'⟩ := T_surj (T D + c - 2 ^ e)
  refine ⟨D', by omega, ?_⟩
  have hk := hQ
  have hk' := len_halfk (e + 1) D'
  have tq := T_halfk (e + 1) D
  have tq' := T_halfk (e + 1) D'
  generalize halfk (e + 1) D = Q at hk tq
  generalize halfk (e + 1) D' = Q' at hk' tq'
  have hP : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [Nat.pow_succ]; omega
  have hp := Nat.two_pow_pos e
  generalize 2 ^ e = p at hc hb hD' hP hp
  rw [hP] at tq tq'
  -- T D = 2p a + b
  have hdm := Nat.div_add_mod (T D) (2 * p)
  have hml := Nat.mod_lt (T D) (show 0 < 2 * p by omega)
  generalize T D / (2 * p) = a at hdm tq
  generalize T D % (2 * p) = b at hdm hml
  have e' : T D' = 2 * p * a + b + c - p := by omega
  rcases Nat.lt_or_ge (b + c) p with hlt | hge
  · -- a ≥ 1, the quotient drops by one
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0; simp at hdm; omega
      · exact h0
    have : T D' / (2 * p) = a - 1 := by
      apply Nat.div_eq_of_lt_le
      · have : (a - 1) * (2 * p) = 2 * p * a - 2 * p := by
          rw [Nat.mul_comm, Nat.mul_sub, Nat.mul_one]
        rw [this]
        have : 2 * p ≤ 2 * p * a := Nat.le_mul_of_pos_right _ ha
        omega
      · have : (a - 1 + 1) * (2 * p) = 2 * p * a := by
          rw [Nat.sub_add_cancel ha, Nat.mul_comm]
        rw [this]; omega
    rw [this] at tq'
    have := len_pred (A := Q') (B := Q) (by omega)
    omega
  · have : T D' / (2 * p) = a := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_comm]; omega
      · have : (a + 1) * (2 * p) = 2 * p * a + 2 * p := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
        rw [this]; omega
    rw [this] at tq'
    have := T_inj Q' Q (by omega)
    subst this; omega

/-- **A borrow.**  Taking `2^e - c` (`c ≤ 2^e`) from a history of more than `e` digits leaves a history at most
`e + 2` digits shorter. -/
theorem borrow (D : List Nat) (c e : Nat) (hc : c ≤ 2 ^ e) (hl : e < D.length) :
    ∃ D', T D' + 2 ^ e = T D + c ∧ D.length ≤ D'.length + e + 2 :=
  borrow_core D c e (e + 1) hc (T_ge_pow D e hl) (len_halfk (e + 1) D).1

theorem halfk_le : ∀ (k d : Nat) (r : List Nat), k ≤ d → halfk k (d :: r) = (d - k) :: r
  | 0, d, r, _ => rfl
  | k + 1, d + 1, r, h => by
    show halfk k (d :: r) = _
    rw [halfk_le k d r (by omega)]; congr 1; omega
  | k + 1, 0, r, h => by omega

theorem halfk_gt (j : Nat) (r : List Nat) : ∀ d : Nat, halfk (j + (d + 1)) (d :: r) = halfk j r
  | 0 => rfl
  | d + 1 => by
    show halfk (j + (d + 1)) (d :: r) = _
    exact halfk_gt j r d

/-- **A borrow from a known first digit `d`.**  Only the digits above `e` count: the history loses at most
`e + 2 - d` digits. -/
theorem borrowD (d : Nat) (r : List Nat) (c e : Nat) (hc : c ≤ 2 ^ e) (hl : e ≤ d + r.length) :
    ∃ D', T D' + 2 ^ e = T (d :: r) + c ∧ (d :: r).length ≤ D'.length + (e + 1 - d) + 1 := by
  apply borrow_core (d :: r) c e (e + 1 - d) hc
  · have h1 := T_len r
    have h2 : 2 ^ e ≤ 2 ^ (d + r.length) := Nat.pow_le_pow_right (by omega) hl
    rw [Nat.pow_add] at h2
    have h3 : 2 ^ d * 2 ^ r.length ≤ 2 ^ d * (1 + 2 * T r) := Nat.mul_le_mul_left _ (by omega)
    simp only [T]; omega
  · rcases Nat.lt_or_ge e d with h | h
    · rw [halfk_le (e + 1) d r (by omega)]; simp
    · obtain ⟨j, rfl⟩ : ∃ j, e = d + j := ⟨e - d, by omega⟩
      rw [show d + j + 1 = j + (d + 1) by omega, halfk_gt j r d]
      have := (len_halfk j r).1
      simp only [List.length_cons]; omega


/-! ## Arithmetic steps, in the form the generator uses -/

theorem RC.castbs {a : Config} {bs bs' : List Nat} {l : Nat} {us : List Nat} (h : RC a (gcfg bs l us))
    (e : bs = bs') : RC a (gcfg bs' l us) := e ▸ h

/-- `N` regular sub-rounds from the blocks `bs` (the digits `F ++ D`) to the digits `F' ++ D'`. -/
theorem RC.arithG (N q : Nat) (F F' D D' : List Nat) {bs : List Nat} {l l' : Nat} {us us' : List Nat}
    (e : bs = encBlocks q (F ++ D)) (hT : T F' + 2 ^ sig F' * T D' + N = T F + 2 ^ sig F * T D)
    (hy : giter N (l, us) = some (l', us')) : ∃ q', RC (gcfg bs l us) (gcfg (encBlocks q' (F' ++ D')) l' us') := by
  obtain ⟨q', D'', h1, _, h2⟩ := RC.arith N q F F' D (T D') (l, us) (l', us') hT hy
  have := T_inj D'' D' h1; subst this; subst e; exact ⟨q', h2⟩

theorem giter_pow (e l l' y1 : Nat) (us us' : List Nat) (hg : gstep (1, us) = some (y1, us')) (hl : l = 1 + 4 * e)
    (hl' : l' = y1 + 4 * e) : giter (2 ^ e) (l, us) = some (l', us') := by
  subst hl hl'; exact giter_scale e (1, us) (y1, us') hg

theorem giter_pm1 (e l : Nat) (us us' : List Nat) (hl : l = 4 * e + 1) (hu : us' = List.replicate e 3 ++ us) :
    giter (2 ^ e - 1) (l, us) = some (1, us') := by
  subst hl hu; exact giter_pow_sub1 e us

theorem giter_j (j q r l l' u : Nat) (us0 us' : List Nat) (hl : l = 4 * q + 1) (hu : u = 4 * j + r)
    (hl' : l' = 4 * (q + j) + 1) (hu' : us' = r :: us0) : giter (2 ^ (q + j) - 2 ^ q) (l, u :: us0) = some (l', us') := by
  subst hl hu hl' hu'; exact giter_chunks j q r us0

/-- The end of the transient: a moment of the counter form, the last block `4l + 1` and every gap `4x + 3`. -/
def EndM (bs : List Bool) (c : Config) : Prop :=
  ∃ (q : Nat) (D : List Nat) (l : Nat) (xs : List Nat) (u : Nat), c = gcfg (hist q D) (4 * l + 1) (xs.map (fun x => 4 * x + 3) ++ openZ (4 * u + 3) bs)

theorem EndM.of {bs : List Bool} (q : Nat) (D : List Nat) (l : Nat) (xs : List Nat) (u : Nat) {bl : List Nat} {L : Nat}
    {us : List Nat} (e1 : bl = hist q D) (e2 : L = 4 * l + 1)
    (e3 : us = xs.map (fun x => 4 * x + 3) ++ openZ (4 * u + 3) bs) : Lands (gcfg bl L us) (EndM bs) :=
  Lands.here ⟨q, D, l, xs, u, by subst e1 e2 e3; rfl⟩

theorem Lands.castl {a a' : Config} {P : Config → Prop} (e : a = a') (h : Lands a' P) : Lands a P := e ▸ h

theorem Lands.or_l {a : Config} {P Q : Config → Prop} (h : Lands a P) : Lands a (fun c => P c ∨ Q c) := by
  obtain ⟨c, h1, h2⟩ := h; exact ⟨c, h1, Or.inl h2⟩

theorem Lands.or_r {a : Config} {P Q : Config → Prop} (h : Lands a Q) : Lands a (fun c => P c ∨ Q c) := by
  obtain ⟨c, h1, h2⟩ := h; exact ⟨c, h1, Or.inr h2⟩

theorem RC.castr {a b b' : Config} (h : RC a b) (e : b = b') : RC a b' := e ▸ h

theorem RC.of_lands {a b : Config} (h : Lands a (fun c => c = b)) : RC a b := by
  obtain ⟨c, h1, h2⟩ := h; exact h2 ▸ h1

/-- Two sweep states with the same lists up to arithmetic. -/
macro "lsteq" : tactic => `(tactic| (simp +arith only [PS.mk.injEq, hist, encBlocks, List.map_cons, List.map_append,
  List.map_replicate, List.cons_append, List.append_assoc, List.cons.injEq, List.replicate_succ, List.nil_append,
  List.replicate_zero,
  and_true, true_and] <;> (try constructor) <;> omega))

/-- Two block lists that are the same up to arithmetic. -/
macro "bseq" : tactic => `(tactic| (simp +arith only [hist, encBlocks, List.map_append, List.map_cons, List.map_replicate,
  List.map_nil, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append, List.replicate_zero]
  <;> (try simp only [List.cons.injEq, List.append_cancel_left_eq, and_true, true_and]) <;> (try omega)))

/-- Two configurations that are the same up to arithmetic. -/
macro "cfgeq" : tactic => `(tactic| (congr 1 <;> first | with_reducible rfl | lsteq | bseq | omega))

end H4320
