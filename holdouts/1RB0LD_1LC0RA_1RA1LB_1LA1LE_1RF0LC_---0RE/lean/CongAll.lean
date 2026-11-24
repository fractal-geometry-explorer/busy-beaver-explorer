import Congruence

/-!
# 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE: no congruence of any modulus traps the doubling map

`Congruence.lean` rules out congruence invariants for the moduli dividing `2^16·3^9`, one certificate each.  This file
rules them out for **every** modulus `M`, with one construction:

* `run v k p`: the value `v = n - h k` after the level increments `p` (a list of `d ∈ {0, 1}`), in `Int`;
* `run_swap`: putting an increment one step later (`1, 0` → `0, 1`) changes the final value by
  `-3^r·δ(k)`, `δ(k) = 3 - 10·2^k`, and `δ(k+1) = 2δ(k) - 3` (`dl_succ`);
* `run_zeros`: steps that keep the level multiply `2v + k + 2` by 3, so `a` of them at a level with
  `2·3^a ∣ k + 2` make `v ≡ 0 (mod 3^a)` whatever `v` was;
* `reach`: write `M = 3^a·m` with `3 ∤ m`.  A block of `m` segments, each with two swappable pairs (at levels `κ`,
  `κ + 1`) and with lengths and level gains chosen so that `3^ℓ ≡ 1` and `2^κ` repeats mod `m` (`ord3`, `per2`,
  both by `pigeon`), lets one add `X·A + Y·B` mod `m` for any `X, Y < m`; with `δ(k+1) = 2δ(k) - 3` that covers
  every residue (`inv3`: an explicit inverse of 3).  A tail of `c` increments and `a` steps then fixes the residue
  mod `3^a`.  So from **every** value at every level `k ≥ M` some path leads to `v ≡ 0 (mod M)`;
* `no_cong_any`, `no_cong_ever`: hence every `CongInv M K P` (a property of the residues of `v`, `k`, `2^k` mod `M`
  that misses the halting values and is kept by the macro step from level `K` on) holds at no value of any level
  `k ≥ K`.  No congruence, of any modulus, from any start, can keep the run of the map away from the `h k`.

This settles the 2-adic question too: a closed set of 2-adic classes that holds the run and misses the targets
misses a ball around them, so it gives an invariant mod some `2^j`, which `no_cong_ever` rules out.
Everything is kernel-checked, standard axioms only, core Lean (no Mathlib).
-/

/-! ## Congruences in `Int` with explicit witnesses, a pigeonhole lemma, and orders mod `m` -/

namespace CgLib

def Cg (m a b : Int) : Prop := ∃ c, a - b = m * c

theorem Cg.refl (m a : Int) : Cg m a a := ⟨0, by grind⟩
theorem Cg.symm {m a b : Int} : Cg m a b → Cg m b a := fun ⟨c, h⟩ => ⟨-c, by grind⟩
theorem Cg.trans {m a b c : Int} : Cg m a b → Cg m b c → Cg m a c :=
  fun ⟨x, h1⟩ ⟨y, h2⟩ => ⟨x + y, by grind⟩
theorem Cg.add {m a b c d : Int} : Cg m a b → Cg m c d → Cg m (a + c) (b + d) :=
  fun ⟨x, h1⟩ ⟨y, h2⟩ => ⟨x + y, by grind⟩
theorem Cg.sub {m a b c d : Int} : Cg m a b → Cg m c d → Cg m (a - c) (b - d) :=
  fun ⟨x, h1⟩ ⟨y, h2⟩ => ⟨x - y, by grind⟩
theorem Cg.mul_left {m a b : Int} (k : Int) : Cg m a b → Cg m (k * a) (k * b) :=
  fun ⟨x, h1⟩ => ⟨k * x, by rw [← Int.mul_sub, h1]; grind⟩
theorem Cg.mul {m a b c d : Int} (h1 : Cg m a b) (h2 : Cg m c d) : Cg m (a * c) (b * d) := by
  obtain ⟨x, hx⟩ := h1; obtain ⟨y, hy⟩ := h2
  refine ⟨x * c + b * y, ?_⟩
  have e1 : a = b + m * x := by grind
  have e2 : c = d + m * y := by grind
  subst e1; subst e2; grind
theorem Cg.pow {m a b : Int} (h : Cg m a b) : ∀ n : Nat, Cg m (a ^ n) (b ^ n)
  | 0 => by rw [Int.pow_zero, Int.pow_zero]; exact Cg.refl _ _
  | n + 1 => by rw [Int.pow_succ, Int.pow_succ]; exact (Cg.pow h n).mul h
theorem Cg.zero_of {m a : Int} (h : Cg m a 0) : ∃ c, a = m * c := by
  obtain ⟨c, hc⟩ := h; exact ⟨c, by grind⟩
theorem Cg.of_eq {m a b : Int} (h : a = b) : Cg m a b := h ▸ Cg.refl m a

/-- `x` and `x % m` are congruent. -/
theorem Cg.emod (m x : Int) : Cg m (x % m) x := ⟨-(x / m), by have := Int.emod_add_mul_ediv x m; grind⟩

/-- Pigeonhole: `m + 1` values below `m` repeat. -/
theorem pigeon : ∀ (m : Nat) (f : Nat → Nat), (∀ i, i ≤ m → f i < m) → ∃ i j, i < j ∧ j ≤ m ∧ f i = f j := by
  intro m
  induction m with
  | zero => intro f hf; have := hf 0 (Nat.le_refl 0); omega
  | succ n ih =>
    intro f hf
    by_cases hc : ∃ i, i ≤ n ∧ f i = f (n + 1)
    · obtain ⟨i, hi, he⟩ := hc; exact ⟨i, n + 1, by omega, Nat.le_refl _, he⟩
    · let g : Nat → Nat := fun i => if f i = n then f (n + 1) else f i
      have hg : ∀ i, i ≤ n → g i < n := by
        intro i hi
        have := hf i (by omega)
        have h2 := hf (n + 1) (Nat.le_refl _)
        simp only [g]
        split
        · rename_i h3
          have : f (n + 1) ≠ n := fun h4 => hc ⟨i, hi, by omega⟩
          omega
        · omega
      obtain ⟨i, j, hij, hj, he⟩ := ih g hg
      simp only [g] at he
      split at he <;> split at he
      · exact ⟨i, j, hij, by omega, by omega⟩
      · exact absurd ⟨j, hj, he.symm⟩ hc
      · exact absurd ⟨i, by omega, he⟩ hc
      · exact ⟨i, j, hij, by omega, he⟩

/-- Residues of `x` mod `m > 0`, as a `Nat`. -/
def res (m : Nat) (x : Int) : Nat := (x % (m : Int)).toNat

theorem res_lt (m : Nat) (hm : 0 < m) (x : Int) : res m x < m := by
  unfold res
  have h1 := Int.emod_nonneg x (b := (m : Int)) (by omega)
  have h2 := Int.emod_lt_of_pos x (b := (m : Int)) (by omega)
  omega

theorem res_cg (m : Nat) (hm : 0 < m) (x y : Int) (h : res m x = res m y) : Cg m x y := by
  unfold res at h
  have h1 := Int.emod_nonneg x (b := (m : Int)) (by omega)
  have h2 := Int.emod_nonneg y (b := (m : Int)) (by omega)
  have e : x % (m : Int) = y % (m : Int) := by omega
  exact ((Cg.emod m x).symm.trans (Cg.of_eq e)).trans (Cg.emod m y)

/-- An inverse of `3` mod `m` when `3 ∤ m`. -/
theorem inv3 (m : Nat) (h : m % 3 ≠ 0) : ∃ i : Int, Cg m (3 * i) 1 := by
  rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h1 | h1
  · exact ⟨(2 * m + 1) / 3, 2, by omega⟩
  · exact ⟨(m + 1) / 3, 1, by omega⟩

/-- A period of `3^L ≡ 1` mod `m` when `3 ∤ m`. -/
theorem ord3 (m : Nat) (hm : 0 < m) (h : m % 3 ≠ 0) : ∃ L, 0 < L ∧ Cg m ((3 : Int) ^ L) 1 := by
  obtain ⟨i, j, hij, _, he⟩ := pigeon m (fun i => res m ((3 : Int) ^ i)) (fun i _ => res_lt m hm _)
  obtain ⟨u, hu⟩ := inv3 m h
  refine ⟨j - i, by omega, ?_⟩
  have c1 : Cg m ((3 : Int) ^ j) (3 ^ i) := (res_cg m hm _ _ he).symm
  have c2 : Cg m (u ^ i * 3 ^ j) (u ^ i * 3 ^ i) := c1.mul_left _
  have e1 : u ^ i * (3 : Int) ^ j = (3 * u) ^ i * 3 ^ (j - i) := by
    rw [show j = i + (j - i) by omega, Int.pow_add, Int.mul_pow]; grind
  have e2 : u ^ i * (3 : Int) ^ i = (3 * u) ^ i := by rw [Int.mul_pow]; grind
  have c3 : Cg m ((3 * u) ^ i) 1 := by have := hu.pow i; rwa [Int.one_pow] at this
  rw [e1, e2] at c2
  -- (3u)^i 3^L ≡ (3u)^i ≡ 1, and (3u)^i ≡ 1, so 3^L ≡ 1
  have c4 : Cg m ((3 * u) ^ i * 3 ^ (j - i)) (1 * 3 ^ (j - i)) := c3.mul (Cg.refl _ _)
  rw [Int.one_mul] at c4
  exact (c4.symm.trans c2).trans c3

/-- A period of `2^κ` mod `m` from some `j ≤ m` on. -/
theorem per2 (m : Nat) (hm : 0 < m) : ∃ j P, j ≤ m ∧ 0 < P ∧
    ∀ t κ, j ≤ κ → Cg m ((2 : Int) ^ (κ + t * P)) (2 ^ κ) := by
  obtain ⟨i, j, hij, hj, he⟩ := pigeon m (fun i => res m ((2 : Int) ^ i)) (fun i _ => res_lt m hm _)
  refine ⟨i, j - i, by omega, by omega, ?_⟩
  have c1 : Cg m ((2 : Int) ^ j) (2 ^ i) := (res_cg m hm _ _ he).symm
  intro t
  induction t with
  | zero => intro κ _; simp; exact Cg.refl _ _
  | succ t ih =>
    intro κ hκ
    have e : ∀ x : Nat, (2 : Int) ^ (x + j) = 2 ^ x * 2 ^ j := fun x => Int.pow_add _ _ _
    have e1 : κ + (t + 1) * (j - i) = (κ + t * (j - i) - i) + j := by rw [Nat.add_mul, Nat.one_mul]; omega
    have e2 : κ + t * (j - i) = (κ + t * (j - i) - i) + i := by have := Nat.zero_le (t * (j - i)); omega
    rw [e1]
    have c2 := c1.mul_left ((2 : Int) ^ (κ + t * (j - i) - i))
    rw [← Int.pow_add, ← Int.pow_add, ← e2] at c2
    exact c2.trans (ih κ hκ)

end CgLib

namespace RunLib
open CgLib

/-- `2^k` as an integer. -/
def tw (k : Nat) : Int := ((2 ^ k : Nat) : Int)

theorem tw_succ (k : Nat) : tw (k + 1) = 2 * tw k := by
  unfold tw; rw [Nat.pow_succ]; omega

/-- One macro step on `v = n - h k` at level `k`, when the level goes up by `d`. -/
def vs (v : Int) (k d : Nat) : Int := 3 * v + 2 + k + d + 5 * tw k - 5 * tw (k + d)

/-- The swap defect `δ(k) = 3 - 10·2^k`. -/
def dl (k : Nat) : Int := 3 - 10 * tw k

def run : Int → Nat → List Nat → Int
  | v, _, [] => v
  | v, k, d :: ds => run (vs v k d) (k + d) ds

def sm : List Nat → Nat
  | [] => 0
  | d :: ds => d + sm ds

theorem run_append : ∀ (p q : List Nat) (v : Int) (k : Nat), run v k (p ++ q) = run (run v k p) (k + sm p) q := by
  intro p
  induction p with
  | nil => intro q v k; simp [run, sm]
  | cons d ds ih =>
    intro q v k
    simp only [List.cons_append, run, sm]
    rw [ih, Nat.add_assoc]

theorem sm_append (p q : List Nat) : sm (p ++ q) = sm p + sm q := by
  induction p with
  | nil => simp [sm]
  | cons d ds ih => simp only [List.cons_append, sm, ih]; omega

theorem run_lin : ∀ (p : List Nat) (v w : Int) (k : Nat), run v k p - run w k p = 3 ^ p.length * (v - w) := by
  intro p
  induction p with
  | nil => intro v w k; simp [run]
  | cons d ds ih =>
    intro v w k
    simp only [run, List.length_cons]
    rw [ih, Int.pow_succ]; unfold vs; grind

/-- Swapping a level increment one step later costs `3^|q|·δ(k)`. -/
theorem run_swap (q : List Nat) (v : Int) (k : Nat) :
    run v k (0 :: 1 :: q) = run v k (1 :: 0 :: q) - 3 ^ q.length * dl k := by
  simp only [run]
  rw [show k + 0 + 1 = k + 1 + 0 by omega]
  have := run_lin q (vs (vs v k 0) k 1) (vs (vs v k 1) (k + 1) 0) (k + 1 + 0)
  have e : vs (vs v k 0) k 1 - vs (vs v k 1) (k + 1) 0 = - dl k := by
    unfold vs dl; simp only [Nat.add_zero]; rw [tw_succ]; grind
  rw [e] at this; grind

/-- `w = 2v + k + 2` is multiplied by 3 at each step that keeps the level. -/
theorem run_zeros (a : Nat) : ∀ (v : Int) (k : Nat),
    2 * run v k (List.replicate a 0) = 3 ^ a * (2 * v + k + 2) - (k + 2) := by
  induction a with
  | zero => intro v k; simp [run]; grind
  | succ a ih =>
    intro v k
    simp only [List.replicate_succ, run]
    rw [Nat.add_zero, ih, Int.pow_succ]; unfold vs; simp only [Nat.add_zero]; grind

theorem dl_succ (k : Nat) : dl (k + 1) = 2 * dl k - 3 := by unfold dl; rw [tw_succ]; grind

end RunLib

namespace RunLib
open CgLib

def pair (x : Bool) : List Nat := if x then [0, 1] else [1, 0]

/-- A segment: two swappable pairs, then `E - 2` more level increments and `Z` steps that keep the level. -/
def seg (x y : Bool) (E Z : Nat) : List Nat :=
  pair x ++ pair y ++ (List.replicate (E - 2) 1 ++ List.replicate Z 0)

theorem sm_rep1 (c : Nat) : sm (List.replicate c 1) = c := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [List.replicate_succ, sm, ih]; omega

theorem sm_rep0 (c : Nat) : sm (List.replicate c 0) = 0 := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [List.replicate_succ, sm, ih]

theorem sm_seg (x y : Bool) (E Z : Nat) (hE : 2 ≤ E) : sm (seg x y E Z) = E := by
  unfold seg
  rw [sm_append, sm_append, sm_append, sm_rep1, sm_rep0]
  cases x <;> cases y <;> simp [pair, sm] <;> omega

theorem len_seg (x y : Bool) (E Z : Nat) : (seg x y E Z).length = (E - 2 + Z) + 4 := by
  unfold seg; cases x <;> cases y <;> simp [pair] <;> omega

theorem run_swap2 (a b : Nat) (q : List Nat) (v : Int) (k : Nat) :
    run v k (a :: b :: 0 :: 1 :: q) = run v k (a :: b :: 1 :: 0 :: q) - 3 ^ q.length * dl (k + a + b) := by
  simp only [run]; exact run_swap q _ _

theorem seg_formula (x y : Bool) (E Z : Nat) (w : Int) (κ : Nat) :
    run w κ (seg x y E Z) = run w κ (seg false false E Z)
      - (if x then 3 ^ (E - 2 + Z + 2) * dl κ else 0) - (if y then 3 ^ (E - 2 + Z) * dl (κ + 1) else 0) := by
  unfold seg
  have hl : (List.replicate (E - 2) 1 ++ List.replicate Z 0).length = E - 2 + Z := by simp
  generalize List.replicate (E - 2) 1 ++ List.replicate Z 0 = R at hl ⊢
  cases x <;> cases y <;> simp only [pair, List.cons_append, List.nil_append, ite_true, ite_false,
    Bool.false_eq_true]
  · simp
  · rw [run_swap2, hl]; simp
  · rw [run_swap (1 :: 0 :: R)]; simp [hl]
  · rw [run_swap (0 :: 1 :: R), run_swap2 1 0]; simp [hl]; grind

def adj (X Y E Z : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => adj X Y E Z n ++ seg (decide (n < X)) (decide (n < Y)) E Z

theorem sm_adj (X Y E Z : Nat) (hE : 2 ≤ E) : ∀ n, sm (adj X Y E Z n) = n * E := by
  intro n
  induction n with
  | zero => simp [adj, sm]
  | succ n ih => simp only [adj]; rw [sm_append, ih, sm_seg _ _ _ _ hE, Nat.add_mul, Nat.one_mul]

theorem adj_le (X Y E Z : Nat) : ∀ n, ∀ d ∈ adj X Y E Z n, d ≤ 1 := by
  intro n
  induction n with
  | zero => simp [adj]
  | succ n ih =>
    intro d hd
    simp only [adj, List.mem_append] at hd
    rcases hd with hd | hd
    · exact ih d hd
    · unfold seg pair at hd
      simp only [List.mem_append, List.mem_replicate] at hd
      split at hd <;> split at hd <;> simp at hd <;> omega

/-- The swaps add `min X n` times `A` and `min Y n` times `B`, modulo `m`. -/
theorem adj_diff (m : Nat) (X Y E Z : Nat) (hE : 2 ≤ E) (k : Nat) (v : Int)
    (h3 : Cg m ((3 : Int) ^ (E - 2 + Z + 4)) 1)
    (h2 : ∀ t, Cg m (tw (k + t * E)) (tw k)) :
    ∀ n, Cg m (run v k (adj X Y E Z n) - run v k (adj 0 0 E Z n))
      ((min X n : Nat) * (-(3 ^ (E - 2 + Z + 2) * dl k)) + (min Y n : Nat) * (-(3 ^ (E - 2 + Z) * dl (k + 1)))) := by
  intro n
  induction n with
  | zero => simp [adj]; exact Cg.refl _ _
  | succ n ih =>
    simp only [adj]
    have h0 : decide (n < 0) = false := by simp
    rw [h0, run_append, run_append, sm_adj _ _ _ _ hE, sm_adj _ _ _ _ hE, seg_formula _ _ E Z _ (k + n * E)]
    generalize run v k (adj X Y E Z n) = a at ih
    generalize run v k (adj 0 0 E Z n) = b at ih
    have hl := run_lin (seg false false E Z) a b (k + n * E)
    rw [len_seg] at hl
    have hd1 : Cg m (dl (k + n * E)) (dl k) := by
      unfold dl; exact (Cg.refl _ _).sub ((h2 n).mul_left 10)
    have hd2 : Cg m (dl (k + n * E + 1)) (dl (k + 1)) := by
      rw [dl_succ, dl_succ]; exact ((hd1.mul_left 2).sub (Cg.refl _ _))
    have hA : Cg m (if decide (n < X) = true then 3 ^ (E - 2 + Z + 2) * dl (k + n * E) else 0)
        ((if n < X then 1 else 0 : Int) * (3 ^ (E - 2 + Z + 2) * dl k)) := by
      by_cases hx : n < X <;> simp [hx]
      · exact hd1.mul_left _
      · exact Cg.refl _ _
    have hB : Cg m (if decide (n < Y) = true then 3 ^ (E - 2 + Z) * dl (k + n * E + 1) else 0)
        ((if n < Y then 1 else 0 : Int) * (3 ^ (E - 2 + Z) * dl (k + 1))) := by
      by_cases hy : n < Y <;> simp [hy]
      · exact hd2.mul_left _
      · exact Cg.refl _ _
    have hmain : Cg m (3 ^ (E - 2 + Z + 4) * (a - b)) (1 * (a - b)) := h3.mul (Cg.refl _ _)
    rw [Int.one_mul] at hmain
    have hX : ((min X (n + 1) : Nat) : Int) = (min X n : Nat) + (if n < X then 1 else 0 : Int) := by
      by_cases hx : n < X <;> simp [hx] <;> omega
    have hY : ((min Y (n + 1) : Nat) : Int) = (min Y n : Nat) + (if n < Y then 1 else 0 : Int) := by
      by_cases hy : n < Y <;> simp [hy] <;> omega
    have e : ∀ p q r s : Int, p - r - s - q = (p - q) - r - s := by intros; grind
    rw [e, hl, hX, hY]
    have := ((hmain.trans ih).sub hA).sub hB
    refine this.trans (Cg.of_eq ?_)
    grind

end RunLib

namespace RunLib
open CgLib

theorem split3 (M : Nat) (hM : 0 < M) : ∃ a m, M = 3 ^ a * m ∧ m % 3 ≠ 0 ∧ 0 < m := by
  by_cases h : M % 3 = 0
  · obtain ⟨a, m, e, h1, h2⟩ := split3 (M / 3) (by omega)
    exact ⟨a + 1, m, by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 3, ← Nat.mul_assoc, ← e]; omega, h1, h2⟩
  · exact ⟨0, M, by simp, h, hM⟩
termination_by M
decreasing_by omega

theorem res_cast (m : Nat) (hm : 0 < m) (x : Int) : Cg m (res m x : Int) x := by
  unfold res
  rw [Int.toNat_of_nonneg (Int.emod_nonneg x (b := (m : Int)) (by omega))]
  exact Cg.emod m x

theorem rep_le (c a : Nat) : ∀ d ∈ List.replicate c 1 ++ List.replicate a 0, d ≤ 1 := by
  intro d hd; simp only [List.mem_append, List.mem_replicate] at hd; omega

theorem run_affine (p : List Nat) (v : Int) (k : Nat) : run v k p = 3 ^ p.length * v + run 0 k p := by
  have := run_lin p v 0 k; grind

/-- **Every residue path is open.**  For every modulus `M`, from every value `v` at every level `k ≥ M`, some
sequence of level increments `d ∈ {0, 1}` leads to `v ≡ 0 (mod M)`. -/
theorem reach (M : Nat) (hM : 0 < M) (v : Int) (k : Nat) (hk : M ≤ k) :
    ∃ p : List Nat, (∀ d ∈ p, d ≤ 1) ∧ Cg M (run v k p) 0 := by
  obtain ⟨a, m, eM, hm3, hm⟩ := split3 M hM
  have hmM : m ≤ M := by rw [eM]; exact Nat.le_mul_of_pos_left m (Nat.pow_pos (n := a) (show 0 < 3 by omega))
  obtain ⟨i3, hi3⟩ := inv3 m hm3
  obtain ⟨L, hL, hL3⟩ := ord3 m hm hm3
  obtain ⟨j, P, hj, hP, hper⟩ := per2 m hm
  -- the segment shape
  let E := 2 * P
  let Z := (L - 1) * (E + 2)
  have hE : 2 ≤ E := by omega
  have hlen : E - 2 + Z + 4 = L * (E + 2) := by
    show 2 * P - 2 + (L - 1) * (2 * P + 2) + 4 = L * (2 * P + 2)
    have : L = (L - 1) + 1 := by omega
    conv => rhs; rw [this]
    rw [Nat.add_mul, Nat.one_mul]; omega
  have h3 : Cg m ((3 : Int) ^ (E - 2 + Z + 4)) 1 := by
    rw [hlen, Int.pow_mul]; have := hL3.pow (E + 2); rwa [Int.one_pow] at this
  have h2 : ∀ t, Cg m (tw (k + t * E)) (tw k) := by
    intro t; unfold tw; rw [Int.natCast_pow, Int.natCast_pow]
    have := hper (2 * t) k (by omega)
    rwa [show 2 * t * P = t * E by show 2 * t * P = t * (2 * P); rw [Nat.mul_comm 2 t, Nat.mul_assoc]] at this
  -- the tail: `c` level increments that make `2·3^a ∣ K + 2`, then `a` steps that keep the level
  let K1 := k + m * E
  let c := (2 * 3 ^ a - 1) * (K1 + 2)
  have hc : K1 + c + 2 = 2 * 3 ^ a * (K1 + 2) := by
    have : 1 ≤ 2 * 3 ^ a := by have := Nat.pow_pos (n := a) (show 0 < 3 by omega); omega
    show K1 + (2 * 3 ^ a - 1) * (K1 + 2) + 2 = _
    have e : 2 * 3 ^ a = (2 * 3 ^ a - 1) + 1 := by omega
    conv => rhs; rw [e]
    rw [Nat.add_mul, Nat.one_mul]; omega
  let tail := List.replicate c 1 ++ List.replicate a 0
  let R := run 0 K1 tail
  let τ : Int := -R * i3 ^ (c + a)
  -- any value `≡ τ (mod m)` at level `K1` is sent to `0 (mod M)` by the tail
  have htail : ∀ u : Int, Cg m u τ → Cg M (run u K1 tail) 0 := by
    intro u hu
    -- mod m
    have hlt : tail.length = c + a := by simp [tail]
    have e1 := run_affine tail u K1
    rw [hlt] at e1
    have hm1 : Cg m (run u K1 tail) 0 := by
      rw [e1]
      have q1 : Cg m ((3 : Int) ^ (c + a) * u + R) ((3 : Int) ^ (c + a) * τ + R) :=
        (hu.mul_left _).add (Cg.refl _ _)
      have q2 : (3 : Int) ^ (c + a) * τ + R = R * (1 - (3 * i3) ^ (c + a)) := by
        show (3 : Int) ^ (c + a) * (-R * i3 ^ (c + a)) + R = R * (1 - (3 * i3) ^ (c + a))
        rw [Int.mul_pow]; grind
      have q3 : Cg m ((3 * i3) ^ (c + a)) 1 := by have := hi3.pow (c + a); rwa [Int.one_pow] at this
      have q4 : Cg m (R * (1 - (3 * i3) ^ (c + a))) (R * (1 - 1)) := ((Cg.refl _ 1).sub q3).mul_left R
      rw [q2] at q1
      exact q1.trans (q4.trans (Cg.of_eq (by grind)))
    -- mod 3^a
    have h3a : ∃ z, run u K1 tail = 3 ^ a * z := by
      simp only [tail]
      rw [run_append, sm_rep1]
      have hz := run_zeros a (run u K1 (List.replicate c 1)) (K1 + c)
      generalize run u K1 (List.replicate c 1) = w at hz ⊢
      generalize run w (K1 + c) (List.replicate a 0) = x at hz ⊢
      have hc' : ((K1 + c : Nat) : Int) + 2 = 2 * 3 ^ a * ((K1 : Int) + 2) := by
        rw [show ((K1 + c : Nat) : Int) + 2 = ((K1 + c + 2 : Nat) : Int) by omega, hc, Int.natCast_mul,
          Int.natCast_mul, Int.natCast_pow]
        simp
      rw [hc'] at hz
      exact ⟨w + 3 ^ a * (K1 + 2) - (K1 + 2), by grind⟩
    -- combine: `3^a` and `m` are coprime (`3·i3 ≡ 1 mod m`)
    obtain ⟨z, hz⟩ := h3a
    obtain ⟨y, hy⟩ := hm1.zero_of
    obtain ⟨t, ht⟩ := (by have := hi3.pow a; rwa [Int.one_pow] at this : Cg m ((3 * i3) ^ a) 1)
    refine ⟨i3 ^ a * y - z * t, ?_⟩
    rw [eM, Int.natCast_mul, Int.natCast_pow]
    rw [Int.mul_pow] at ht
    generalize run u K1 tail = x at hz hy ⊢
    have f1 : x * (3 ^ a * i3 ^ a) = m * y * (3 ^ a * i3 ^ a) := by rw [hy]
    have f2 : x * (m * t) = 3 ^ a * z * (m * t) := by rw [hz]
    have f3 : x = x * (3 ^ a * i3 ^ a) - x * (3 ^ a * i3 ^ a - 1) := by grind
    rw [ht] at f3
    grind
  -- the swaps: choose how many of each
  let A : Int := -(3 ^ (E - 2 + Z + 2) * dl k)
  let B : Int := -(3 ^ (E - 2 + Z) * dl (k + 1))
  let T : Int := τ - run v k (adj 0 0 E Z m)
  let Y := res m (T * i3 ^ (E - 2 + Z + 1))
  let X := res m (-2 * (Y : Int) * i3 ^ 2)
  have hX : X < m := res_lt m hm _
  have hY : Y < m := res_lt m hm _
  have hXY : Cg m ((X : Int) * A + (Y : Int) * B) T := by
    have hYc := res_cast m hm (T * i3 ^ (E - 2 + Z + 1))
    have hXc := res_cast m hm (-2 * (Y : Int) * i3 ^ 2)
    have eAB : (X : Int) * A + (Y : Int) * B
        = -(3 ^ (E - 2 + Z)) * ((9 * X + 2 * Y) * dl k) + 3 ^ (E - 2 + Z + 1) * Y := by
      simp only [A, B]; rw [dl_succ]; grind
    have q1 : Cg m (9 * (X : Int) + 2 * Y) 0 := by
      have : Cg m (9 * (X : Int) + 2 * Y) (9 * (-2 * (Y : Int) * i3 ^ 2) + 2 * Y) :=
        (hXc.mul_left 9).add (Cg.refl _ _)
      refine this.trans ?_
      have q : Cg m ((3 * i3) ^ 2) 1 := by have := hi3.pow 2; rwa [Int.one_pow] at this
      have e : 9 * (-2 * (Y : Int) * i3 ^ 2) + 2 * Y = -2 * Y * ((3 * i3) ^ 2) + 2 * Y := by
        rw [Int.mul_pow]; grind
      rw [e]
      exact ((q.mul_left (-2 * (Y : Int))).add (Cg.refl _ _)).trans (Cg.of_eq (by grind))
    have q2 : Cg m ((3 : Int) ^ (E - 2 + Z + 1) * Y) T := by
      have : Cg m ((3 : Int) ^ (E - 2 + Z + 1) * Y) (3 ^ (E - 2 + Z + 1) * (T * i3 ^ (E - 2 + Z + 1))) :=
        hYc.mul_left _
      refine this.trans ?_
      have q : Cg m ((3 * i3) ^ (E - 2 + Z + 1)) 1 := by
        have := hi3.pow (E - 2 + Z + 1); rwa [Int.one_pow] at this
      have e : (3 : Int) ^ (E - 2 + Z + 1) * (T * i3 ^ (E - 2 + Z + 1)) = T * (3 * i3) ^ (E - 2 + Z + 1) := by
        rw [Int.mul_pow]; grind
      rw [e]
      exact (q.mul_left T).trans (Cg.of_eq (by grind))
    rw [eAB]
    have q3 : Cg m (-(3 ^ (E - 2 + Z)) * ((9 * (X : Int) + 2 * Y) * dl k)) (-(3 ^ (E - 2 + Z)) * (0 * dl k)) :=
      (q1.mul (Cg.refl _ (dl k))).mul_left _
    exact (q3.add q2).trans (Cg.of_eq (by grind))
  -- the path
  refine ⟨adj X Y E Z m ++ tail, ?_, ?_⟩
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact adj_le X Y E Z m d hd
    · exact rep_le c a d hd
  · rw [run_append, sm_adj _ _ _ _ hE]
    apply htail
    have hd := adj_diff m X Y E Z hE k v h3 h2 m
    rw [Nat.min_eq_left (Nat.le_of_lt hX), Nat.min_eq_left (Nat.le_of_lt hY)] at hd
    have : Cg m (run v k (adj X Y E Z m)) (run v k (adj 0 0 E Z m) + T) := by
      have := hd.trans hXY
      obtain ⟨w, hw⟩ := this
      exact ⟨w, by grind⟩
    exact this.trans (Cg.of_eq (by simp only [T]; grind))

end RunLib

namespace H50372
open CgLib RunLib

/-- `v = n - h k` as an integer. -/
def vN (k n : Nat) : Int := ((n + k + 6 - 5 * 2 ^ k : Nat) : Int)

theorem vN_step (k n d : Nat) (hd : d ≤ 1) (hn : h k ≤ n) (hF : h (k + d) ≤ F k n) :
    vN (k + d) (F k n) = vs (vN k n) k d := by
  obtain ⟨p1, p2⟩ := pow_facts k
  have hx : 2 ^ (k + d) = 2 ^ d * 2 ^ k := by rw [Nat.pow_add, Nat.mul_comm]
  unfold vN vs tw
  unfold h F at *
  rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
  · simp only [Nat.add_zero] at *; omega
  · simp only [Nat.pow_one] at hx; rw [hx] at hF ⊢; omega

theorem vs_cong (M : Nat) (a b : Int) (k d : Nat) (h : Cg M a b) : Cg M (vs a k d) (vs b k d) := by
  obtain ⟨c, hc⟩ := h; exact ⟨3 * c, by unfold vs; grind⟩

theorem run_cong (M : Nat) (p : List Nat) (a b : Int) (k : Nat) (h : Cg M a b) : Cg M (run a k p) (run b k p) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨3 ^ p.length * c, by rw [run_lin, hc]; grind⟩

theorem cg_nat_mod (M : Nat) (x y : Nat) (h : x % M = y % M) : Cg M (x : Int) (y : Int) := by
  have h1 := Nat.div_add_mod x M
  have h2 := Nat.div_add_mod y M
  refine ⟨((x / M : Nat) : Int) - ((y / M : Nat) : Int), ?_⟩
  have e1 : (x : Int) = (M : Int) * ((x / M : Nat) : Int) + ((x % M : Nat) : Int) := by
    rw [← Int.natCast_mul]; omega
  have e2 : (y : Int) = (M : Int) * ((y / M : Nat) : Int) + ((y % M : Nat) : Int) := by
    rw [← Int.natCast_mul]; omega
  rw [e1, e2, h]; grind

theorem nat_mod_of_cg (M : Nat) (hM : 0 < M) (x : Nat) (h : Cg M (x : Int) 0) : x % M = 0 := by
  obtain ⟨c, hc⟩ := h
  have : (M : Int) ∣ (x : Int) := ⟨c, by omega⟩
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.1 this)

/-- **No congruence invariant, for any modulus.**  Let `P` be any property of the residues mod `M` (of
`v = n - h k`, of `k` and of `2^k`) that excludes the halting values and is kept by the macro step from level `K`
on (`CongInv M K P`).  Then `P` holds at no value of any level `k ≥ K` with `k ≥ 3M + 12`.  Since a run that never
halts passes through values of every large level, no such property can hold along it. -/
theorem no_cong_any (M : Nat) (hM : 0 < M) (K : Nat) (P : Nat × Nat × Nat → Prop) (hI : CongInv M K P) :
    ∀ k n, K ≤ k → 3 * M + 12 ≤ k → h k ≤ n → n < h (k + 1) → ¬ P (cls M k n) := by
  have aux : ∀ p : List Nat, (∀ d ∈ p, d ≤ 1) → ∀ k n, K ≤ k → 3 * M + 12 ≤ k → h k ≤ n → n < h (k + 1) →
      P (cls M k n) → Cg M (run (vN k n) k p) 0 → False := by
    intro p
    induction p with
    | nil =>
      intro _ k n hK hk hn1 hn2 hP hc
      have hb := two_mul_le_pow k (by omega)
      obtain ⟨p1, p2⟩ := pow_facts k
      have h0 := nat_mod_of_cg M hM _ hc
      have hs : cls M k (h k) = cls M k n := by
        unfold cls h
        unfold h at hn1
        rw [show 5 * 2 ^ k - k - 6 + k + 6 - 5 * 2 ^ k = 0 by omega, Nat.zero_mod, h0]
      have hlt : h k < h (k + 1) := by unfold h; rw [p2]; omega
      exact (hI k (h k) hK (Nat.le_refl _) hlt (hs ▸ hP)).1 rfl
    | cons d ds ih =>
      intro hle k n hK hk hn1 hn2 hP hc
      have hd : d ≤ 1 := hle d (List.mem_cons_self ..)
      have hb := two_mul_le_pow k (by omega)
      obtain ⟨n', n1, n2, n3, n4, n5⟩ :=
        realize M k ((n + k + 6 - 5 * 2 ^ k) % M) d hM (by omega) (Nat.mod_lt _ hM) hd (by omega)
      have hs : cls M k n' = cls M k n := by unfold cls; rw [n3]
      have hn := (hI k n' hK (Nat.le_of_lt n1) n2 (hs ▸ hP)).2 d n4 n5
      apply ih (fun e he => hle e (List.mem_cons_of_mem _ he)) (k + d) (F k n') (by omega) (by omega) n4 n5 hn
      rw [vN_step k n' d hd (Nat.le_of_lt n1) n4]
      have hcg : Cg M (vN k n') (vN k n) := cg_nat_mod M _ _ (by rw [n3])
      exact (run_cong M ds _ _ (k + d) (vs_cong M _ _ k d hcg)).trans hc
  intro k n hK hk hn1 hn2 hP
  obtain ⟨p, hp, hc⟩ := reach M hM (vN k n) k (by omega)
  exact aux p hp k n hK hk hn1 hn2 hP hc

end H50372

namespace H50372
open CgLib RunLib

theorem h_ge (k : Nat) : k ≤ h k := by
  unfold h
  have hb : ∀ k, 2 * k + 5 ≤ 5 * 2 ^ k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ]; omega
  rcases k with _ | k
  · omega
  · have := hb (k + 1); have := hb k; rw [Nat.pow_succ] at *; omega

theorem h_mono (k : Nat) : h k ≤ h (k + 1) := by
  unfold h; obtain ⟨p1, p2⟩ := pow_facts k; rw [p2]; omega

/-- Every value has a level. -/
theorem level_of : ∀ f x k0, x + 1 - k0 ≤ f → h k0 ≤ x → ∃ k, k0 ≤ k ∧ h k ≤ x ∧ x < h (k + 1) := by
  intro f
  induction f with
  | zero => intro x k0 hf hx; have := h_ge k0; omega
  | succ f ih =>
    intro x k0 hf hx
    by_cases hlt : x < h (k0 + 1)
    · exact ⟨k0, Nat.le_refl _, hx, hlt⟩
    · have := h_ge (k0 + 1)
      obtain ⟨k, hk, h1, h2⟩ := ih x (k0 + 1) (by omega) (by omega)
      exact ⟨k, by omega, h1, h2⟩

theorem F_gt (k n : Nat) (hn : h k ≤ n) : n < F k n := by
  unfold F; unfold h at hn
  obtain ⟨p1, p2⟩ := pow_facts k
  omega

/-- **Every congruence invariant is empty above its starting level.**  A property of the residues mod `M` that
excludes the halting values and is kept by the macro step from level `K` on holds at no value of any level
`k ≥ K`.  So no congruence (of `n - h k`, `k` and `2^k`, mod any `M`) can trap the run of the map, from any start. -/
theorem no_cong_ever (M : Nat) (hM : 0 < M) (K : Nat) (P : Nat × Nat × Nat → Prop) (hI : CongInv M K P) :
    ∀ k n, K ≤ k → h k ≤ n → n < h (k + 1) → ¬ P (cls M k n) := by
  have main : ∀ f k n, h (K + 3 * M + 12) - n ≤ f → K ≤ k → h k ≤ n → n < h (k + 1) → ¬ P (cls M k n) := by
    intro f
    induction f with
    | zero =>
      intro k n hf hK hn1 hn2
      by_cases hk : 3 * M + 12 ≤ k
      · exact no_cong_any M hM K P hI k n hK hk hn1 hn2
      · -- n ≥ h (K + 3M + 12) but k < 3M + 12: impossible
        have : h (k + 1) ≤ h (K + 3 * M + 12) := by
          have mono : ∀ a b, a ≤ b → h a ≤ h b := by
            intro a b hab
            induction b with
            | zero => have : a = 0 := by omega
                      rw [this]; exact Nat.le_refl _
            | succ b ihb =>
              by_cases e : a = b + 1
              · rw [e]; exact Nat.le_refl _
              · exact Nat.le_trans (ihb (by omega)) (h_mono b)
          exact mono _ _ (by omega)
        omega
    | succ f ih =>
      intro k n hf hK hn1 hn2 hP
      by_cases hk : 3 * M + 12 ≤ k
      · exact no_cong_any M hM K P hI k n hK hk hn1 hn2 hP
      have hgt := F_gt k n hn1
      obtain ⟨k', hk', h1, h2⟩ := level_of (F k n + 1) (F k n) k (by omega) (by omega)
      have hP' := (hI k n hK hn1 hn2 hP).2 (k' - k) (by rw [Nat.add_sub_cancel' hk']; exact h1)
        (by rw [Nat.add_sub_cancel' hk']; exact h2)
      rw [Nat.add_sub_cancel' hk'] at hP'
      exact ih k' (F k n) (by omega) (by omega) h1 h2 hP'
  intro k n hK hn1 hn2
  exact main _ k n (Nat.le_refl _) hK hn1 hn2

end H50372
