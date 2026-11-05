import Cycles

/-! # The low bits of N come from the last blocks alone

`N mod 2^k` depends only on the last `k` blocks (`bigN_append_mod`), and those run on their own (`bs`, `Cycles.lean`),
so on the orbit from blank tape it follows the bottom's cycle (`bigN_bottom`). Two facts about the residues it takes:

- **`N ≡ 2 mod 4` once in eight super steps** (`mod4_blank`): from super step 7 on, the last two blocks run through
  their cycle of eight, and only at `[12, 26]` does the wave pass the last block and turn at the one before it. A
  uniform law would give one in four; this is the half share of every class `2 mod 4`.
- **Three super steps after `[12, 26]`, N has grown by exactly 106** (`plus106`, for any blocks to the left): the
  three steps only add 18 to the third block, and the fourth sends the wave on with `[14, 42]` at the bottom. So
  `N ≡ −42 mod 2^k` at `[12, 26]` exactly when `N ≡ 64 mod 2^k` at `[14, 42]` three steps later (`neg42_iff`).

`ResidueRun.lean` adds the residues mod `2^12` over the cycle of the last 12 blocks (it needs `CycleRun.lean`). -/

namespace BB6b.Res

open BB6b

theorem S_append : ∀ (B U : List Nat), S (B ++ U) = S B + 2 ^ B.length * S U
  | [], U => by simp [S]
  | p :: B, U => by
    simp only [List.cons_append, S, S_append B U, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ B.length)]
    omega

/-- **`N mod 2^k` is a function of the last `k` blocks.** -/
theorem bigN_append_mod (B U : List Nat) : bigN (B ++ U) % 2 ^ B.length = bigN B % 2 ^ B.length := by
  simp only [bigN, S_append]
  rw [← Nat.add_assoc, Nat.add_mul_mod_self_left]

theorem low_length : ∀ (B : List Nat) (e : Ev), (low B e).1.length = B.length
  | [], _ => rfl
  | p :: B, e => by
    simp only [low]
    generalize lev p e = x
    obtain ⟨p', e', c⟩ := x
    simp only
    generalize hy : low B e' = y
    obtain ⟨B', e'', c'⟩ := y
    have := low_length B e'
    rw [hy] at this
    simp [this]

theorem bs_length : ∀ (i : Nat) (B : List Nat), (bs i B).length = B.length
  | 0, _ => rfl
  | i + 1, B => by simp only [bs]; rw [bs_length i, bstep, low_length]

/-- **On the orbit, the low bits of N follow the bottom**: if the last blocks are `B` at super step `j`, then at
super step `j + i` N mod `2 ^ B.length` is that of `bs i B`. -/
theorem bigN_bottom (j : Nat) (B U : List Nat) (hU : U ≠ []) (h : orbit j [6, 1] = some (B ++ U)) (i : Nat)
    (W : List Nat) (hW : orbit (j + i) [6, 1] = some W) :
    bigN W % 2 ^ B.length = bigN (bs i B) % 2 ^ B.length := by
  rw [orbit_add, h, Option.bind_some] at hW
  rcases orbit_split i B U hU with e | ⟨U', _, e⟩
  · rw [e] at hW; cases hW
  · rw [e] at hW
    cases hW
    have := bigN_append_mod (bs i B) U'
    rw [bs_length] at this
    exact this

theorem bs_mul (B : List Nat) (P : Nat) (hP : bs P B = B) : ∀ q, bs (P * q) B = B
  | 0 => rfl
  | q + 1 => by rw [Nat.mul_succ, Nat.add_comm, bs_add, hP, bs_mul B P hP q]

theorem bs_mod (B : List Nat) (P : Nat) (hP : bs P B = B) (i : Nat) : bs i B = bs (i % P) B := by
  conv => lhs; rw [← Nat.div_add_mod i P, bs_add, bs_mul B P hP]

/-! ## N mod 4 -/

theorem orbit7 : orbit 7 [6, 1] = some ([12, 26] ++ [33, 9, 10, 1]) := by decide

theorem mod4_cycle : ∀ r, r < 8 → (bigN (bs r [12, 26]) % 4 = 2 ↔ r = 0) := by decide

/-- **From super step 7 on, N ≡ 2 mod 4 exactly when the step is 7 plus a multiple of 8**: one super step in eight. -/
theorem mod4_blank (i : Nat) (W : List Nat) (hW : orbit (7 + i) [6, 1] = some W) :
    (bigN W % 4 = 2 ↔ i % 8 = 0) := by
  have h := bigN_bottom 7 [12, 26] _ (by simp) orbit7 i W hW
  rw [bs_mod [12, 26] 8 (by decide) i] at h
  have := mod4_cycle (i % 8) (Nat.mod_lt _ (by decide))
  simp only [List.length_cons, List.length_nil] at h
  rw [show (2 : Nat) ^ (0 + 1 + 1) = 4 from rfl] at h
  rw [h]; exact this

/-! ## Three steps from `[12, 26]` -/

/-- The three super steps from `[12, 26]` with any blocks `q :: U` to the left: the third block gains 18, and the
bottom comes to `[14, 42]`. -/
theorem three (q : Nat) (U : List Nat) : orbit 3 (12 :: 26 :: q :: U) = some (14 :: 42 :: (q + 18) :: U) := by
  have h1 := superL_split [12, 26] (q :: U) (by simp)
  have h2 := superL_split [11, 21] ((q + 18) :: U) (by simp)
  have h3 := superL_split [13, 31] ((q + 18) :: U) (by simp)
  have e1 : bstep [12, 26] = ([11, 21], .add 18, (bstep [12, 26]).2.2) := by decide
  have e2 : bstep [11, 21] = ([13, 31], .none, (bstep [11, 21]).2.2) := by decide
  have e3 : bstep [13, 31] = ([14, 42], .none, (bstep [13, 31]).2.2) := by decide
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  simp only [push, Option.map_some, List.cons_append, List.nil_append] at h1 h2 h3
  simp only [orbit] at *
  rw [h1, Option.bind_some, h2, Option.bind_some, h3, Option.bind_some]

theorem bigN_cons2 (a b : Nat) (U : List Nat) : bigN (a :: b :: U) = 10 + a + 2 * b + 4 * S U := by
  simp only [bigN, S]; omega

/-- **Three super steps after `[12, 26]`, N is larger by exactly 106**, whatever the blocks to the left. -/
theorem plus106 (q : Nat) (U W : List Nat) (h : orbit 3 (12 :: 26 :: q :: U) = some W) :
    bigN W = bigN (12 :: 26 :: q :: U) + 106 := by
  rw [three] at h; cases h
  simp only [bigN_cons2, S]; omega

/-- So `N ≡ −42 mod 2^k` at `[12, 26]` iff `N ≡ 64 mod 2^k` three super steps later (`k ≥ 7`). -/
theorem neg42_iff (k : Nat) (hk : 7 ≤ k) (q : Nat) (U W : List Nat) (h : orbit 3 (12 :: 26 :: q :: U) = some W) :
    (bigN (12 :: 26 :: q :: U) + 42) % 2 ^ k = 0 ↔ bigN W % 2 ^ k = 64 := by
  rw [plus106 q U W h]
  have hM : 64 < 2 ^ k :=
    Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hk : 2 ^ 7 ≤ 2 ^ k)
  generalize bigN (12 :: 26 :: q :: U) = n
  generalize 2 ^ k = M at hM
  have h64 : 64 % M = 64 := Nat.mod_eq_of_lt hM
  have hr : (n + 42) % M < M := Nat.mod_lt _ (by omega)
  rw [show n + 106 = (n + 42) + 64 by omega, Nat.add_mod (n + 42) 64, h64]
  generalize (n + 42) % M = r at hr
  constructor
  · intro e; rw [e, Nat.zero_add, h64]
  · intro e
    rcases Nat.lt_or_ge (r + 64) M with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at e; omega
    · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at e; omega

/-! ## A checker for residues along the bottom

`runMiss bad n B` runs `n` super steps of the bottom `B` and returns where it ends, or `none` if some step on the way
has `bad (bigN _)`. `ResidueRun.lean` uses it on the cycle of the last 12 blocks, in pieces. -/

def runMiss (bad : Nat → Bool) : Nat → List Nat → Option (List Nat)
  | 0, B => some B
  | n + 1, B => if bad (bigN B) then none else runMiss bad n (bstep B).1

theorem runMiss_add (bad : Nat → Bool) : ∀ (a b : Nat) (B B' B'' : List Nat), runMiss bad a B = some B' →
    runMiss bad b B' = some B'' → runMiss bad (a + b) B = some B''
  | 0, b, B, B', B'', h₁, h₂ => by cases h₁; simpa using h₂
  | a + 1, b, B, B', B'', h₁, h₂ => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [runMiss] at h₁ ⊢
    split at h₁
    · cases h₁
    · rename_i hb; simp only [hb]; exact runMiss_add bad a b _ B' B'' h₁ h₂

theorem runMiss_sound (bad : Nat → Bool) : ∀ (n : Nat) (B B' : List Nat), runMiss bad n B = some B' →
    bs n B = B' ∧ ∀ r, r < n → bad (bigN (bs r B)) = false
  | 0, B, B', h => by cases h; exact ⟨rfl, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | n + 1, B, B', h => by
    simp only [runMiss] at h
    split at h
    · cases h
    · rename_i hb
      obtain ⟨h1, h2⟩ := runMiss_sound bad n _ B' h
      refine ⟨h1, fun r hr => ?_⟩
      cases r with
      | zero => simpa [bs] using hb
      | succ r => exact h2 r (by omega)

/-- **A residue that the bottom's cycle never takes is never taken again**: if the last blocks are `B` at super step
`j`, `B` comes back after `P` steps, and no step of that cycle has `bad (N mod 2^k)`, then no later super step has. -/
theorem never_bad (bad : Nat → Bool) (j P : Nat) (B U : List Nat) (hU : U ≠ []) (h : orbit j [6, 1] = some (B ++ U))
    (hP : 0 < P) (hc : runMiss (fun n => bad (n % 2 ^ B.length)) P B = some B) (i : Nat) (W : List Nat)
    (hW : orbit (j + i) [6, 1] = some W) : bad (bigN W % 2 ^ B.length) = false := by
  obtain ⟨hB, hr⟩ := runMiss_sound _ P B B hc
  rw [bigN_bottom j B U hU h i W hW, bs_mod B P hB i]
  exact hr _ (Nat.mod_lt _ hP)

/-- The two residues mod `2^12` that the blank-tape orbit never takes after its last 12 blocks settle. -/
def bad12 (n : Nat) : Bool := n % 4096 == 3030 || n % 4096 == 4054

end BB6b.Res
