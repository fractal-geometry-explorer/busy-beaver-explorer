/-!
# The arithmetic of a descent

A *descent* is a run of eater phases.  Phase j has a fuel `F j` (a run of the 20-digit rung, counted in rungs)
and makes `K j = (F j - m) / 4 + 1` super-cycles of the ×64 kind (4 units of fuel each).  The next fuel is
written by the `21 * K j` hits that the phase passes down.  The phase log of the accelerator (`py/lsa_laws.py`)
shows two laws for a fresh fuel, each with a small offset:

* law A:  `11 * F (j+1) = 21 * K j + e`  with `−lo ≤ e ≤ hi` (one rung every 11 hits, a ratio of 44/21),
* law B:  `F (j+1) = K j + δ`            with `0 ≤ δ ≤ d`    (one rung every 21 hits, a ratio of 4).

Everything here is proved for every value: the offsets are hypotheses, the constants of the run are
instances.

* `descent_A_lower`, `descent_A_upper`: under law A the fuel after j phases is pinned between
  `21^j/44^j` times the start, up to an additive constant that does not grow with j (a potential
  `23 F + c` that is multiplied by at least 21/44 per phase).  So a descent on a fuel of D digits lasts about
  D / log10(44/21) ≈ 3.1 D phases, as observed.
* `descent_B_lower`, `descent_B_upper`: under law B the fuel drops by a factor of 4 per phase, up to a constant.
* `phases_compose`: the hits needed from above a stack of phases.  Each phase j maps the hits its region
  needs to the hits needed above it by a monotone map `g j` with `g j x ≥ 64 ^ K j * x`
  (`blk_ge`, the block recursion of `Accel.blocks` in the twin's folder); then the whole stack needs at least `64 ^ (K 0 + ... + K (n-1))` times
  the hits needed below it.  This is the bound on the wall visit of the next right-end event.
-/

namespace Descent

/-! ## One phase

Phase j burns 4 units of its fuel `F j` per super-cycle and makes k super-cycles, with a slack of at most m
left over: `4 k ≤ F ≤ 4 k + m` (in the run, k = (F − mmin)/4 + 1 and the slack F − 4k is 5 to 9). -/

/-- law A: one rung every 11 hits, `11 F' = 21 k + e` with `−lo ≤ e ≤ hi` -/
def LawA (m lo hi F F' : Nat) : Prop :=
  ∃ k, 4 * k ≤ F ∧ F ≤ 4 * k + m ∧ 21 * k ≤ 11 * F' + lo ∧ 11 * F' ≤ 21 * k + hi

/-- law B: one rung every 21 hits, `F' = k + δ` with `0 ≤ δ ≤ d` -/
def LawB (m d F F' : Nat) : Prop :=
  ∃ k, 4 * k ≤ F ∧ F ≤ 4 * k + m ∧ k ≤ F' ∧ F' ≤ k + d

theorem lawA_step_lower {m lo hi F F' : Nat} (h : LawA m lo hi F F') : 21 * F ≤ 44 * F' + (21 * m + 4 * lo) := by
  obtain ⟨k, h1, h2, h3, h4⟩ := h; omega

theorem lawA_step_upper {m lo hi F F' : Nat} (h : LawA m lo hi F F') : 44 * F' ≤ 21 * F + 4 * hi := by
  obtain ⟨k, h1, h2, h3, h4⟩ := h; omega

theorem lawB_step {m d F F' : Nat} (h : LawB m d F F') : 4 * F' ≤ F + 4 * d ∧ F ≤ 4 * F' + m := by
  obtain ⟨k, h1, h2, h3, h4⟩ := h; omega

/-! ## Geometric bounds over many phases -/

theorem pow_succ_mul (a j x : Nat) : a ^ (j + 1) * x = a * (a ^ j * x) := by
  rw [Nat.pow_succ, Nat.mul_comm (a ^ j) a, Nat.mul_assoc]

/-- if a x_j ≤ b x_{j+1} for all j, then a^j x_0 ≤ b^j x_j -/
theorem geo_lower (a b : Nat) (x : Nat → Nat) (h : ∀ j, a * x j ≤ b * x (j + 1)) :
    ∀ j, a ^ j * x 0 ≤ b ^ j * x j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc a ^ (j + 1) * x 0 = a * (a ^ j * x 0) := pow_succ_mul a j _
      _ ≤ a * (b ^ j * x j) := Nat.mul_le_mul_left _ ih
      _ = b ^ j * (a * x j) := Nat.mul_left_comm _ _ _
      _ ≤ b ^ j * (b * x (j + 1)) := Nat.mul_le_mul_left _ (h j)
      _ = b ^ (j + 1) * x (j + 1) := by rw [Nat.mul_left_comm, ← pow_succ_mul]

/-- if (a + d) x_{j+1} ≤ a x_j + d c for all j, then (a + d)^j x_j ≤ a^j x_0 + (a + d)^j c -/
theorem geo_upper (a d c : Nat) (x : Nat → Nat) (h : ∀ j, (a + d) * x (j + 1) ≤ a * x j + d * c) :
    ∀ j, (a + d) ^ j * x j ≤ a ^ j * x 0 + (a + d) ^ j * c := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (a + d) ^ (j + 1) * x (j + 1) ≤ (a + d) ^ j * (a * x j + d * c) := by
      calc (a + d) ^ (j + 1) * x (j + 1) = (a + d) ^ j * ((a + d) * x (j + 1)) := by
            rw [Nat.mul_left_comm, ← pow_succ_mul]
        _ ≤ (a + d) ^ j * (a * x j + d * c) := Nat.mul_le_mul_left _ (h j)
    have h2 : (a + d) ^ j * (a * x j + d * c) = a * ((a + d) ^ j * x j) + d * ((a + d) ^ j * c) := by
      rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_left_comm ((a + d) ^ j) d]
    have h3 : a * ((a + d) ^ j * x j) ≤ a * (a ^ j * x 0 + (a + d) ^ j * c) := Nat.mul_le_mul_left _ ih
    have h4 : a * (a ^ j * x 0 + (a + d) ^ j * c) + d * ((a + d) ^ j * c)
        = a ^ (j + 1) * x 0 + (a + d) ^ (j + 1) * c := by
      rw [pow_succ_mul a j, pow_succ_mul (a + d) j, Nat.mul_add, Nat.add_mul, Nat.add_assoc]
    omega

/-- law A, lower bound: the potential G = 23 F + c, c = 21 m + 4 lo, shrinks at most by 44/21 per phase:
21^j G_0 ≤ 44^j G_j.  So a fresh descent on a fuel F_0 lasts at least until 44^j / 21^j ≥ G_0 / G_j. -/
theorem descent_A_lower (m lo hi : Nat) (F : Nat → Nat) (hA : ∀ j, LawA m lo hi (F j) (F (j + 1))) :
    ∀ j, 21 ^ j * (23 * F 0 + (21 * m + 4 * lo)) ≤ 44 ^ j * (23 * F j + (21 * m + 4 * lo)) :=
  geo_lower 21 44 (fun j => 23 * F j + (21 * m + 4 * lo)) (fun j => by
    have s := lawA_step_lower (hA j)
    show 21 * (23 * F j + (21 * m + 4 * lo)) ≤ 44 * (23 * F (j + 1) + (21 * m + 4 * lo))
    omega)

/-- law A, upper bound: 44^j (23 F_j) ≤ 21^j (23 F_0) + 44^j (4 hi), i.e. F_j ≤ (21/44)^j F_0 + 4 hi / 23 -/
theorem descent_A_upper (m lo hi : Nat) (F : Nat → Nat) (hA : ∀ j, LawA m lo hi (F j) (F (j + 1))) :
    ∀ j, 44 ^ j * (23 * F j) ≤ 21 ^ j * (23 * F 0) + 44 ^ j * (4 * hi) :=
  geo_upper 21 23 (4 * hi) (fun j => 23 * F j) (fun j => by
    have s := lawA_step_upper (hA j)
    show (21 + 23) * (23 * F (j + 1)) ≤ 21 * (23 * F j) + 23 * (4 * hi)
    omega)

/-- law B, upper bound: 4^j (3 F_j) ≤ 3 F_0 + 4^j (4 d), i.e. F_j ≤ F_0 / 4^j + 4 d / 3 -/
theorem descent_B_upper (m d : Nat) (F : Nat → Nat) (hB : ∀ j, LawB m d (F j) (F (j + 1))) :
    ∀ j, 4 ^ j * (3 * F j) ≤ 3 * F 0 + 4 ^ j * (4 * d) := by
  intro j
  have g := geo_upper 1 3 (4 * d) (fun j => 3 * F j) (fun j => by
    have s := (lawB_step (hB j)).1
    show (1 + 3) * (3 * F (j + 1)) ≤ 1 * (3 * F j) + 3 * (4 * d)
    omega) j
  simpa using g

/-- law B, lower bound: 3 F_0 + m ≤ 4^j (3 F_j + m) -/
theorem descent_B_lower (m d : Nat) (F : Nat → Nat) (hB : ∀ j, LawB m d (F j) (F (j + 1))) :
    ∀ j, 3 * F 0 + m ≤ 4 ^ j * (3 * F j + m) := by
  intro j
  have g := geo_lower 1 4 (fun j => 3 * F j + m) (fun j => by
    have s := (lawB_step (hB j)).2
    show 1 * (3 * F j + m) ≤ 4 * (3 * F (j + 1) + m)
    omega) j
  simpa using g

/-! ## Stacks of phases: the top-hit bound multiplies -/

/-- the hits needed above phases j, j+1, ..., n-1 when the region below them needs z -/
def stack (g : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, z => z
  | n + 1, j, z => g j (stack g n (j + 1) z)

/-- sum of K over phases j .. j+n-1 -/
def ksum (k : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, j => k j + ksum k n (j + 1)

theorem phases_compose (a : Nat) (g : Nat → Nat → Nat) (k : Nat → Nat)
    (hg : ∀ j x, a ^ k j * x ≤ g j x) : ∀ n j z, a ^ ksum k n j * z ≤ stack g n j z := by
  intro n
  induction n with
  | zero => intro j z; simp [stack, ksum]
  | succ n ih =>
    intro j z
    simp only [stack, ksum]
    calc a ^ (k j + ksum k n (j + 1)) * z = a ^ k j * (a ^ ksum k n (j + 1) * z) := by
          rw [Nat.pow_add, Nat.mul_assoc]
      _ ≤ a ^ k j * stack g n (j + 1) z := Nat.mul_le_mul_left _ (ih (j + 1) z)
      _ ≤ g j (stack g n (j + 1) z) := hg j _

/-- the hits above a run of k + 1 blocks of a phase (the recursion `Accel.blocks` of the twin's folder,
block map x ↦ (c + 1) x + b, P hits per super-cycle) -/
def blk (c b P Z : Nat) : Nat → Nat
  | 0 => (c + 1) * Z + b
  | k + 1 => (c + 1) * (P + blk c b P Z k) + b

/-- so a phase of K super-cycles needs at least (c + 1)^K times the hits needed below it: the hypothesis of
`phases_compose` with a = 64 for the ×64 kind (c = 63) -/
theorem blk_ge (c b P Z : Nat) : ∀ k, (c + 1) ^ (k + 1) * Z ≤ blk c b P Z k
  | 0 => by simp [blk]
  | k + 1 => by
    have ih := blk_ge c b P Z k
    simp only [blk]
    calc (c + 1) ^ (k + 1 + 1) * Z = (c + 1) * ((c + 1) ^ (k + 1) * Z) := pow_succ_mul _ _ _
      _ ≤ (c + 1) * blk c b P Z k := Nat.mul_le_mul_left _ ih
      _ ≤ (c + 1) * (P + blk c b P Z k) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
      _ ≤ (c + 1) * (P + blk c b P Z k) + b := Nat.le_add_right _ _

/-! ## The constants of the run

Over the 12,071 transitions logged from the twin's word at wall visit 10^3200 (`py/lsa_laws.py`), every
×64 phase leaves a slack of 5 to 9 (m = 9); a fresh fuel follows law A with −913 ≤ e ≤ 224 (6,907 times) or
law B with 2 ≤ δ ≤ 12 (1,392 times); the other 3,691 next fuels are older runs of the list. -/

abbrev mRun := 9
abbrev loRun := 913
abbrev hiRun := 224
abbrev dRun := 12

/-- with the run's constants: a fresh law-A descent shrinks its fuel by at most 44/21 per phase up to an
additive 21·9 + 4·913 = 3841 (scaled by 23), and by at least that factor up to 4·224 -/
theorem run_A (F : Nat → Nat) (hA : ∀ j, LawA mRun loRun hiRun (F j) (F (j + 1))) (j : Nat) :
    21 ^ j * (23 * F 0 + 3841) ≤ 44 ^ j * (23 * F j + 3841) ∧
    44 ^ j * (23 * F j) ≤ 21 ^ j * (23 * F 0) + 44 ^ j * 896 :=
  ⟨descent_A_lower mRun loRun hiRun F hA j, descent_A_upper mRun loRun hiRun F hA j⟩

/-- a phase of the log (phase 4 to 5 of the run, fuel 1574058...: here a small instance) -/
example : LawA mRun loRun hiRun 1001 478 := ⟨248, by decide, by decide, by decide, by decide⟩

end Descent
