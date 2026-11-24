import DigitMap

/-!
# 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA: what can be said in closed form about the digit map

`DigitMap.lean` reduces the machine to one question: where the orbit of 22 under

    fd (10a + d) = 31a + dK (d / 2),   dK = 15, 27, 47, 35, 36,

runs out of the 772-digit budget of level 2.  This file collects the exact structure of that map (kernel, core Lean
only, no `sorry`):

* `fd_parity`, `fd_half`: the last bit of a state never matters; on y = x / 2 the map is
  `gy (10c + j) = 31c + gK j` with ten constants 7, 13, 23, 17, 18, 23, 29, 39, 33, 33, so the orbit of 22 is the orbit
  of 11 under a mod-10 map of slope 31/10 in which every last digit counts.
* `orbit_identity`: the closed form in terms of the digits,
  10^k x_k + 31 Σ 31^(k-1-i) 10^i d_i = 31^k x_0 + 10 Σ 31^(k-1-i) 10^i K_i,
  i.e. the orbit is the expansion of the start in the rational base 31/10 (Akiyama, Frougny and Sakarovitch's
  rational base number systems).  The last digit of x_k is a function of all earlier digits.
* `rlist_mod`, `rlist_onto`: the first k values of r along an orbit depend only on the start mod 10^k, and every list
  of k values below 5 is realized by some start below 10^k (31 is invertible mod 10^k, `inv31`).  So the r sequence
  re-encodes the start's digits: any finite pattern can continue with anything, and no finite-state rule reading the
  orbit so far (or a bounded number of digits of the start) forbids a halting row.  Earlier this was a check for
  k <= 4 in `py/endgame.py`; here it is a theorem for every k.

None of this skips steps of the orbit; that the end of level 2 (about 2·10^770 steps along) is out of reach stays a
statement about what is known (README), not a theorem.  `py/orbitfast.py` uses `fd_split`-style splitting (the high
digits of a state are carried along as a multiple of 31^c) to follow the orbit exactly for 10^8 steps.
-/

namespace H66813

open TM

/-! ## The orbit, and the parity that does not matter -/

/-- `orb k x`: k steps of `fd` from x. -/
def orb : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => orb k (fd x)

theorem orb_succ' : ∀ k x, orb (k + 1) x = fd (orb k x) := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih => intro x; show orb (k + 1) (fd x) = _; rw [ih]; rfl

/-- The r of the first k states of the orbit of x. -/
def rlist (x : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => dr x :: rlist (fd x) k

theorem dK_le : ∀ r : Nat, dK r ≤ 47
  | 0 | 1 | 2 | 3 => by decide
  | _ + 4 => by simp [dK]

theorem dr_lt (x : Nat) : dr x < 5 := by unfold dr; omega

/-- The last bit of a state never matters: x and x with its last bit cleared have the same image. -/
theorem fd_parity (x : Nat) : fd (x / 2 * 2) = fd x := by
  have h1 : x / 2 * 2 / 10 = x / 10 := by omega
  have h2 : x / 2 * 2 % 10 / 2 = x % 10 / 2 := by omega
  unfold fd dr
  rw [h1, h2]

/-- The ten constants of the map on y = x / 2. -/
def gK : Nat → Nat
  | 0 => 7 | 1 => 13 | 2 => 23 | 3 => 17 | 4 => 18 | 5 => 23 | 6 => 29 | 7 => 39 | 8 => 33 | _ => 33

/-- The map on y = x / 2: a mod-10 map of slope 31/10 in which all ten last digits count. -/
def gy (y : Nat) : Nat := 31 * (y / 10) + gK (y % 10)

/-- `fd` seen on y = x / 2 is `gy`: so the orbit of 22 is, up to the dropped bit, the orbit of 11 under gy. -/
theorem fd_half (x : Nat) : fd x / 2 = gy (x / 2) := by
  have hx : x = 20 * (x / 20) + x % 20 := by omega
  have hs : x % 20 < 20 := Nat.mod_lt _ (by decide)
  generalize x / 20 = q at hx
  generalize x % 20 = s at hx hs
  subst hx
  unfold fd dr gy
  have e1 : (20 * q + s) / 10 = 2 * q + s / 10 := by omega
  have e2 : (20 * q + s) % 10 = s % 10 := by omega
  have e3 : (20 * q + s) / 2 / 10 = q := by omega
  have e4 : (20 * q + s) / 2 % 10 = s / 2 := by omega
  rw [e1, e2, e3, e4]
  match s, hs with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
  | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ =>
    simp only [Nat.reduceMod, Nat.reduceDiv, dK, gK] <;> omega
  | _ + 20, h => exact absurd h (by omega)

/-! ## The exact identity: the orbit is a rational base 31/10 expansion of its start -/

/-- `wsum v x k` = sum over i < k of 31^(k-1-i) 10^i v(x_i), x_i the orbit of x. -/
def wsum (v : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 31 * wsum v x k + 10 ^ k * v (orb k x)

/-- The high digits of a state ride along: f(10^(m+1) A + B) = 10^m (31 A) + f(B).  Iterated, c steps from
10^(c+M) H + L are 10^M 31^c H + f^c(L), which is how `py/orbitfast.py` follows the orbit (divide and conquer). -/
theorem fd_split (m A B : Nat) : fd (10 ^ (m + 1) * A + B) = 10 ^ m * (31 * A) + fd B := by
  have h1 : (10 ^ (m + 1) * A + B) / 10 = 10 ^ m * A + B / 10 := by
    rw [Nat.pow_succ, Nat.mul_comm (10 ^ m) 10, Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_left _ _ (by decide),
      Nat.add_comm]
  have h2 : (10 ^ (m + 1) * A + B) % 10 = B % 10 := by
    rw [Nat.pow_succ, Nat.mul_comm (10 ^ m) 10, Nat.mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_left]
  unfold fd dr
  rw [h1, h2, Nat.mul_add, Nat.add_assoc]
  congr 1
  rw [← Nat.mul_assoc, Nat.mul_comm 31 (10 ^ m), Nat.mul_assoc]

theorem orb_split : ∀ c n A B, orb c (10 ^ (c + n) * A + B) = 10 ^ n * (31 ^ c * A) + orb c B := by
  intro c
  induction c with
  | zero => intro n A B; simp [orb, Nat.add_comm]
  | succ c ih =>
    intro n A B
    show orb c (fd (10 ^ (c + 1 + n) * A + B)) = _
    have e : 31 ^ c * (31 * A) = 31 ^ (c + 1) * A := by rw [Nat.pow_succ, Nat.mul_assoc]
    rw [show c + 1 + n = (c + n) + 1 by omega, fd_split, ih, e]
    rfl

theorem fd_ten (y : Nat) : 10 * fd y + 31 * (y % 10) = 31 * y + 10 * dK (dr y) := by
  unfold fd; omega

/-- **The closed form, in terms of the digits.** With d_i = x_i mod 10 and K_i = dK(r_i):

    10^k x_k + 31 Σ_{i<k} 31^(k-1-i) 10^i d_i = 31^k x_0 + 10 Σ_{i<k} 31^(k-1-i) 10^i K_i.

Divided by 31^k: x_0 = (10/31)^k x_k + Σ_{i<k} (10/31)^i (31 d_i - 10 K_i)/31, the expansion of x_0 in the rational
base 31/10 with digits 31 d_i - 10 K_i.  The last digit of x_k is digit k of 31^k x_0 + 10 ΣK - 31 Σd, a sum over all
earlier digits: the identity is exact, but it does not skip any step. -/
theorem orbit_identity (x : Nat) : ∀ k,
    10 ^ k * orb k x + 31 * wsum (· % 10) x k = 31 ^ k * x + 10 * wsum (fun y => dK (dr y)) x k := by
  intro k
  induction k with
  | zero => simp [orb, wsum]
  | succ k ih =>
    simp only [wsum, orb_succ']
    have b := fd_ten (orb k x)
    rw [Nat.pow_succ, Nat.pow_succ]
    generalize fd (orb k x) = z at b
    generalize orb k x = y at b ih
    generalize 10 ^ k = P at ih
    generalize 31 ^ k = Q at ih
    generalize wsum (· % 10) x k = A at ih
    generalize wsum (fun y => dK (dr y)) x k = B at ih
    grind

/-! ## The digits of an orbit re-encode the digits of its start -/

theorem mod_succ_div (x k : Nat) : x % 10 ^ (k + 1) / 10 = x / 10 % 10 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]

theorem mod_succ_mod (x k : Nat) : x % 10 ^ (k + 1) % 10 = x % 10 := by
  rw [Nat.pow_succ, Nat.mod_mul_left_mod]

/-- fd x mod 10^k depends only on x mod 10^(k+1). -/
theorem fd_mod (x x' k : Nat) (h : x % 10 ^ (k + 1) = x' % 10 ^ (k + 1)) : fd x % 10 ^ k = fd x' % 10 ^ k := by
  have h1 : x / 10 % 10 ^ k = x' / 10 % 10 ^ k := by rw [← mod_succ_div, ← mod_succ_div, h]
  have h2 : x % 10 = x' % 10 := by rw [← mod_succ_mod x k, ← mod_succ_mod x' k, h]
  have key : ∀ z, fd z % 10 ^ k = (31 * (z / 10 % 10 ^ k) + dK (z % 10 / 2)) % 10 ^ k := by
    intro z
    unfold fd dr
    conv => lhs; rw [← Nat.div_add_mod (z / 10) (10 ^ k)]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 31 (10 ^ k), Nat.mul_assoc, Nat.add_assoc, Nat.mul_add_mod]
  rw [key, key, h1, h2]

/-- The first k values of r along the orbit depend only on the start mod 10^k. -/
theorem rlist_mod : ∀ k x x', x % 10 ^ k = x' % 10 ^ k → rlist x k = rlist x' k := by
  intro k
  induction k with
  | zero => intro x x' _; rfl
  | succ k ih =>
    intro x x' h
    simp only [rlist]
    have h2 : x % 10 = x' % 10 := by rw [← mod_succ_mod x k, ← mod_succ_mod x' k, h]
    rw [ih (fd x) (fd x') (fd_mod x x' k h)]
    unfold dr; rw [h2]

/-- 31 is invertible mod every power of 10. -/
theorem inv31 : ∀ k : Nat, ∃ u t : Nat, 31 * u = 1 + 10 ^ k * t := by
  intro k
  induction k with
  | zero => exact ⟨1, 30, by decide⟩
  | succ k ih =>
    obtain ⟨u, t, h⟩ := ih
    refine ⟨u + 10 ^ k * ((10 - t % 10) % 10), (t + 31 * ((10 - t % 10) % 10)) / 10, ?_⟩
    have e : t + 31 * ((10 - t % 10) % 10) = 10 * ((t + 31 * ((10 - t % 10) % 10)) / 10) := by omega
    rw [Nat.pow_succ]
    generalize (t + 31 * ((10 - t % 10) % 10)) / 10 = q at e
    generalize (10 - t % 10) % 10 = s at e
    generalize 10 ^ k = P at h
    grind

theorem rlist_length : ∀ k x, (rlist x k).length = k := by
  intro k; induction k with
  | zero => intro x; rfl
  | succ k ih => intro x; simp [rlist, ih]

/-- **Every list of r values is the start of some orbit.** For every list of k values below 5 there is a start
x < 10^k whose orbit has exactly these r values in its first k states.  So no rule that reads a bounded number of
low digits of the start, or any finite pattern of the orbit so far, can exclude what comes next: every continuation
occurs.  (Each list comes from exactly 2^k residues mod 10^k, and `fd_half` says the last bit is the only freedom; on
y = x / 2 the full digit lists j_0 .. j_(k-1) are in bijection with y mod 10^k.) -/
theorem rlist_onto : ∀ rs : List Nat, (∀ r ∈ rs, r < 5) → ∃ x, x < 10 ^ rs.length ∧ rlist x rs.length = rs := by
  intro rs
  induction rs with
  | nil => intro _; exact ⟨0, by decide, rfl⟩
  | cons r rs ih =>
    intro hr
    have hr0 : r < 5 := hr r (List.mem_cons_self ..)
    obtain ⟨y, hy, hyl⟩ := ih (fun r' h => hr r' (List.mem_cons_of_mem _ h))
    obtain ⟨u, t, hu⟩ := inv31 rs.length
    generalize hP : 10 ^ rs.length = P at hy hu
    have hP1 : 1 ≤ P := by rw [← hP]; exact Nat.pow_pos (by decide)
    have hK := dK_le r
    let w := y + 47 * P - dK r
    let a := u * w % P
    have ha : a < P := Nat.mod_lt _ (by omega)
    refine ⟨10 * a + 2 * r, ?_, ?_⟩
    · show 10 * a + 2 * r < 10 ^ (rs.length + 1)
      rw [Nat.pow_succ, hP]; omega
    · show rlist (10 * a + 2 * r) (rs.length + 1) = r :: rs
      simp only [rlist]
      have hd : dr (10 * a + 2 * r) = r := by unfold dr; omega
      have hf : fd (10 * a + 2 * r) = 31 * a + dK r := by
        unfold fd; rw [hd]; congr 2; omega
      -- 31 a + dK r ≡ y (mod P)
      have hm : (31 * a + dK r) % P = y := by
        have e1 : 31 * a % P = w % P := by
          show 31 * (u * w % P) % P = w % P
          rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, hu, Nat.add_mul, Nat.one_mul,
            Nat.mul_assoc, Nat.add_mul_mod_self_left]
        have e2 : w + dK r = y + P * 47 := by show y + 47 * P - dK r + dK r = _; omega
        rw [Nat.add_mod, e1, ← Nat.add_mod, e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
      rw [hd, hf, rlist_mod rs.length (31 * a + dK r) y (by rw [hP, hm, Nat.mod_eq_of_lt hy]), hyl]

/-- The first ten r values of the orbit of 22, by evaluation. -/
theorem rlist_22 : rlist 22 10 = [1, 4, 2, 2, 4, 1, 3, 3, 3, 0] := by decide

end H66813
