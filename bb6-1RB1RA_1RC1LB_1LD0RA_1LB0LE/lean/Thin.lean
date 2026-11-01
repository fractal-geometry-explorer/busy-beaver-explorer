import Return

/-!
# The excursions that could fail form a thin 2-adic set, for every `a`

`Return.lean` proves the return map for `a < 2^62` by running each open class's members below the bound one by one.
Here the open classes are not run: `thin` returns their residues instead, and `thin_ok` says that an `a` whose
excursion from `[a, 2a+1]` does not return (halts, meets a stop block of 1, or never comes back) has its residue in
that list.  This holds for every `a`, with no upper bound.

`returns_off_open34`: every `a = 1 mod 4`, `a ≥ 5`, returns unless `a mod 2^34` is one of 67 residues (kernel,
about 40 s and 3.6 GB; the same search to mod 2^42 leaves 261 residues but needs 13.6 GB in one `decide`).

So a failing excursion needs `a` in a set of density 67/2^32 ≈ 1.6·10⁻⁸ among `a = 1 mod 4`, and finer residues
shrink it further (about 2^(-0.81 m) of the classes stay open at depth m, `notes/LAB_NOTES.md`).  It does not prove
the machine never halts: the open set is infinite at every depth (it contains `a = 1`, whose excursion meets the
stop block of 1), and the blank orbit's counter visits values in
it (computed: every `a = 2^r + 1` with r even, in the range run).
-/

namespace BB6d

/-- The classes of `p + q*u` that are left open: run the class symbolically, split by the parity of `u` (at most `d`
times), set `u = 0` aside when a comparison is not uniform (that member is run concretely), and at the depth limit
record the residue `p % M` of the open class (whose modulus `q` must be a multiple of `M`). -/
def thin (M : Nat) : Nat → Nat → Nat → Nat → Option (List Nat)
  | 0, _, _, _ => none
  | f + 1, d, p, q =>
    match sgood p q with
    | .ok _ => some []
    | .split => match d with
      | 0 => if q % M = 0 then some [p % M] else none
      | d + 1 => match thin M f d p (2 * q), thin M f d (p + q) (2 * q) with
        | some l, some r => some (l ++ r)
        | _, _ => none
    | .small => if cgood p then thin M f d (p + q) q else none
    | .bad => none

theorem thin_ok (M : Nat) (f : Nat) : ∀ (d p q : Nat) (L : List Nat), thin M f d p q = some L →
    ∀ u, ¬ Returns (p + q * u) → (p + q * u) % M ∈ L := by
  induction f with
  | zero => intro d p q L h; simp [thin] at h
  | succ f ih =>
    intro d p q L h u hu
    simp only [thin] at h
    split at h
    · rename_i l hs
      cases l with
      | nil => exact absurd (sgood_ok p q hs u) hu
      | cons _ _ =>
        unfold sgood at hs
        split at hs <;> (try split at hs) <;> simp_all
    · split at h
      · split at h
        · rename_i hq
          cases h
          simp only [List.mem_singleton]
          obtain ⟨c, hc⟩ : ∃ c, q = M * c := ⟨q / M, by have := Nat.div_add_mod q M; omega⟩
          rw [hc, Nat.mul_assoc, Nat.add_mul_mod_self_left]
        · cases h
      · rename_i d
        split at h
        · rename_i l r h0 h1
          cases h
          obtain ⟨v, rfl | rfl⟩ : ∃ v, u = 2 * v ∨ u = 2 * v + 1 := ⟨u / 2, by omega⟩
          · have e : 2 * q * v = q * (2 * v) := by rw [Nat.mul_comm 2 q, Nat.mul_assoc]
            have := ih d p (2 * q) l h0 v (by rw [e]; exact hu)
            rw [e] at this; exact List.mem_append_left _ this
          · have e : p + q + 2 * q * v = p + q * (2 * v + 1) := by
              rw [Nat.mul_add, Nat.mul_one, show 2 * q * v = q * (2 * v) by rw [Nat.mul_comm 2 q, Nat.mul_assoc]]
              omega
            have := ih d (p + q) (2 * q) r h1 v (by rw [e]; exact hu)
            rw [e] at this; exact List.mem_append_right _ this
        · cases h
    · split at h
      · rename_i hc
        cases u with
        | zero => exact absurd (by simpa using cgood_ok p hc) hu
        | succ v =>
          have e : p + q + q * v = p + q * (v + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
          have := ih d (p + q) q L h v (by rw [e]; exact hu)
          rwa [e] at this
      · cases h
    · cases h

/-- Every non-returning member of the class `p + q*u` has its residue mod `M` in `L`. -/
def ThinP (M p q : Nat) (L : List Nat) : Prop := ∀ u, ¬ Returns (p + q * u) → (p + q * u) % M ∈ L

theorem ThinP.of_thin {M f d p q : Nat} {L : List Nat} (h : thin M f d p q = some L) : ThinP M p q L :=
  thin_ok M f d p q L h

theorem ThinP.all {M : Nat} {L : List Nat} (h : ThinP M 5 4 L) :
    ∀ a, a % 4 = 1 → 5 ≤ a → a % M ∉ L → Returns a := by
  intro a h1 h5 ho
  refine Classical.byContradiction fun hr => ho ?_
  have := h ((a - 5) / 4)
  rw [show 5 + 4 * ((a - 5) / 4) = a by omega] at this
  exact this hr

/-- The 67 open residues mod 2^34 (in the order `thin` finds them). -/
def open34 : List Nat := [
  1051003137, 11788421377, 7493454081, 3517253889, 12107188481, 15261305089, 8651081985, 5429856513, 11872307457,
  4602136833, 2454653185, 6749620481, 15630010625, 14556268801, 16703752449, 2430535937, 9946728705, 10483599617,
  5498669313, 7109282049, 8451459329, 11435866625, 7140899329, 15730833921, 1671526913, 14556428801, 8113977857,
  8986393089, 2678159873, 5219121665, 11661572609, 8440347137, 14136211969, 11988728321, 16283695617, 1066760705,
  9656695297, 13951662593, 439596033, 13324497921, 6882046977, 2738074625, 11328009217, 7033041921, 2662577153,
  16621220865, 13936866305, 13978547201, 8207184897, 10690212865, 14985180161, 12837696513, 4214207489, 8509174785,
  17099109377, 2634547201, 11224481793, 6929514497, 7231504385, 15821438977, 8388608001, 16978542593, 2013265921,
  6308233217, 14898167809, 5637144577, 1]

/-- **For every `a`, unbounded**: the excursion from `[a, 2a+1]` returns unless `a mod 2^34` is one of 67 residues,
a fraction 67/2^32 ≈ 1.6·10⁻⁸ of the `a = 1 mod 4`.  Kernel only (about 40 s). -/
theorem returns_off_open34 : ∀ a, a % 4 = 1 → 5 ≤ a → a % 2 ^ 34 ∉ open34 → Returns a :=
  ThinP.all (ThinP.of_thin (f := 200) (d := 32) (by decide +kernel))

theorem open34_length : open34.length = 67 := by decide

end BB6d
