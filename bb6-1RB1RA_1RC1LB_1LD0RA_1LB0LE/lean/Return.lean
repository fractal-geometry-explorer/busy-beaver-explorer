import Pass

/-!
# The return map on two-block states, in Lean

`py/returnmap.py` runs the closed form `next` on residue classes `a = p + q*u` (u ≥ 0 free) and finds that every
excursion from the two-block state `[a, 2a+1]` (left to right; `[2a+1, a]` nearest first, as `next` reads it) comes
back to `[a + 12k, 2(a + 12k) + 1]` after `9k` passes, for every `a = 1 mod 4` with `5 ≤ a < 2^62`.  Here the same
computation is written in Lean and proved sound:

* `Aff` is a value `p + q*u`; `snext` is `next` on lists of them, failing (`split`, `small`, `bad`) wherever a parity
  or a comparison is not the same on the whole class; `snext_ok`: where it does not fail it agrees with `next` at every
  `u`.  `srun` runs it until a two-block state `[2a'+1, a']` (`srun_ok`).
* `explore B fuel d p q` covers the class `p + q*u` below `B`: it runs the class symbolically, splits it in two by the
  parity of `u` (at most `d` times), sets the single value `u = 0` aside (run concretely, `crun`) when a comparison is
  not uniform, and at the depth limit runs the one member below `B` concretely.  `explore_ok`: if it returns `true`,
  every member below `B` returns (`Returns`).
* `orbit_ok_upto`: if every `a = 1 mod 4` with `5 ≤ a < B` returns, then the first `(3B + 4)/4` passes from blank tape
  never stop at a block of 1 and the machine reaches each of their pass starts (`reach_upto`).

The six short chains from `[a, 2a+d]`, `|d| ≤ 3`, to the next two-block state hold for every `a ≥ 5`
(`chain_0` … `chain_m3`).  The return map is checked here for every `a < 2^16` by the kernel alone (`returns_2_16`),
and for every `a < 2^62`, which gives the first 3·2^60 + 1 ≈ 3.46·10¹⁸ passes, with `native_decide` (`returns_2_62`,
`no_one_3e18`: they trust Lean's compiler for the evaluation of `explore`, while everything that says what `explore`
means is checked by the kernel).  The same range by the kernel alone is `Return62.lean` (`returns_2_62_kernel`,
`no_one_3e18_kernel`): there the class is cut into pieces small enough for one kernel `decide` each.
-/

namespace BB6d

open TM

/-! ## Iterating the pass map -/

/-- One pass on an outcome: `.halt` and `.one` stay. -/
def stepN : Next → Next
  | .ok zs => next zs
  | e => e

/-- `n` passes. -/
def iterN : Nat → Next → Next
  | 0, x => x
  | n + 1, x => iterN n (stepN x)

theorem iterN_add (m n : Nat) (x : Next) : iterN (m + n) x = iterN n (iterN m x) := by
  induction m generalizing x with
  | zero => simp [iterN]
  | succ m ih => rw [show m + 1 + n = (m + n) + 1 by omega]; simp only [iterN]; exact ih _

theorem orbit_succ (n : Nat) : orbit (n + 1) = stepN (orbit n) := by
  simp only [orbit]; cases orbit n <;> rfl

theorem orbit_add (n m : Nat) : orbit (n + m) = iterN m (orbit n) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih => rw [show n + (m + 1) = (n + 1) + m by omega, ih, orbit_succ]; rfl

theorem iterN_not_ok (n : Nat) (x : Next) (hx : ∀ zs, x ≠ .ok zs) : ∀ zs, iterN n x ≠ .ok zs := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih =>
    apply ih
    cases x with
    | ok zs => exact absurd rfl (hx zs)
    | halt => exact hx
    | one => exact hx

/-- An outcome that is a block list was a block list at every earlier pass. -/
theorem orbit_ok_of_le {m r : Nat} (hmr : m ≤ r) {zs : List Nat} (h : orbit r = .ok zs) :
    ∃ ys, orbit m = .ok ys := by
  cases hm : orbit m with
  | ok ys => exact ⟨ys, rfl⟩
  | halt =>
    have := orbit_add m (r - m); rw [show m + (r - m) = r by omega, hm, h] at this
    exact absurd this.symm (iterN_not_ok _ _ (fun _ h => Next.noConfusion h) zs)
  | one =>
    have := orbit_add m (r - m); rw [show m + (r - m) = r by omega, hm, h] at this
    exact absurd this.symm (iterN_not_ok _ _ (fun _ h => Next.noConfusion h) zs)

/-- From `[2a+1, a]` (nearest first) the closed form comes back to `[2a'+1, a']` with `a' = a + 12k` after `9k`
passes, `k ≥ 1`. -/
def Returns (a : Nat) : Prop :=
  ∃ k, 1 ≤ k ∧ iterN (9 * k) (.ok [2 * a + 1, a]) = .ok [2 * (a + 12 * k) + 1, a + 12 * k]

/-! ## The orbit from blank tape, given the return map below a bound -/

theorem orbit_4 : orbit 4 = .ok [11, 5] := by decide

/-- If every `a = 1 mod 4` with `5 ≤ a < B` returns, the first `(3B + 4)/4` passes from blank tape are block lists. -/
theorem orbit_ok_upto (B : Nat) (H : ∀ a, a % 4 = 1 → 5 ≤ a → a < B → Returns a) :
    ∀ n, 4 * n ≤ 3 * B + 4 → ∃ zs, orbit n = .ok zs := by
  -- some pass at or after `j` is a two-block state `[2a+1, a]`
  have Q : ∀ j, 4 * j ≤ 3 * B + 4 → ∃ n, j ≤ n ∧ ∃ a, orbit n = .ok [2 * a + 1, a] := by
    intro j
    induction j with
    | zero => intro _; exact ⟨4, by omega, 5, orbit_4⟩
    | succ j ih =>
      intro hj
      obtain ⟨n, hn, a, ha⟩ := ih (by omega)
      by_cases hlt : j + 1 ≤ n
      · exact ⟨n, hlt, a, ha⟩
      by_cases h3 : j + 1 ≤ 4
      · exact ⟨4, h3, 5, orbit_4⟩
      have hnj : n = j := by omega
      subst hnj
      obtain ⟨hs, _, _⟩ := orbit_ok n _ ha
      simp only [List.sum_cons, List.sum_nil] at hs
      obtain ⟨k, hk, hr⟩ := H a (by omega) (by omega) (by omega)
      refine ⟨n + 9 * k, by omega, a + 12 * k, ?_⟩
      rw [orbit_add, ha]; exact hr
  intro n hn
  obtain ⟨r, hr, a, ha⟩ := Q n hn
  exact orbit_ok_of_le hr ha

/-- The same, for the machine: it reaches each of these pass starts, so it runs at least that many steps. -/
theorem reach_upto (B : Nat) (H : ∀ a, a % 4 = 1 → 5 ≤ a → a < B → Returns a) (n : Nat) (hn : 4 * n ≤ 3 * B + 4) :
    ∃ zs t, orbit n = .ok zs ∧ zs.sum = 4 * n ∧ n ≤ t ∧ steps t init = some ⟨enc zs, blank, .A⟩ := by
  obtain ⟨zs, h⟩ := orbit_ok_upto B H n hn
  obtain ⟨hs, _, t, ht, hr⟩ := orbit_ok n zs h
  exact ⟨zs, t, h, hs, ht, hr⟩

/-! ## The closed form on residue classes -/

/-- The value `p + q*u` of a class, `u ≥ 0`. -/
structure Aff where
  p : Nat
  q : Nat
  deriving DecidableEq, Repr

namespace Aff

def ev (u : Nat) (x : Aff) : Nat := x.p + x.q * u
def add (x y : Aff) : Aff := ⟨x.p + y.p, x.q + y.q⟩
def addc (x : Aff) (c : Nat) : Aff := ⟨x.p + c, x.q⟩
def half (x : Aff) : Aff := ⟨x.p / 2, x.q / 2⟩
def sub1 (x : Aff) : Aff := ⟨x.p - 1, x.q⟩

theorem ev_add (u : Nat) (x y : Aff) : (x.add y).ev u = x.ev u + y.ev u := by
  simp only [ev, add, Nat.add_mul]; omega

theorem ev_addc (u c : Nat) (x : Aff) : (x.addc c).ev u = x.ev u + c := by
  simp only [ev, addc]; omega

theorem ev_sub1 (u : Nat) (x : Aff) (h : 1 ≤ x.p) : x.sub1.ev u = x.ev u - 1 := by
  simp only [ev, sub1]; omega

theorem even_split (u : Nat) (x : Aff) (h : x.q % 2 = 0) : x.q * u = 2 * (x.q / 2 * u) := by
  rw [← Nat.mul_assoc]; congr 1; omega

theorem ev_mod (u : Nat) (x : Aff) (h : x.q % 2 = 0) : x.ev u % 2 = x.p % 2 := by
  simp only [ev]; rw [even_split u x h]; omega

theorem ev_half (u : Nat) (x : Aff) (h : x.q % 2 = 0) : x.half.ev u = x.ev u / 2 := by
  simp only [ev, half]; rw [even_split u x h]; omega

theorem ev_ge (u : Nat) (x : Aff) : x.p ≤ x.ev u := by simp only [ev]; omega

end Aff

/-- The outcome of a symbolic pass: a block list on the whole class, or why not. -/
inductive SR where
  | ok (l : List Aff)
  | split   -- a parity depends on `u`
  | small   -- a comparison with 0 or 1 holds for `u = 0` only, or the class is a single value that fails
  | bad     -- fails on the whole class (or out of fuel)
  deriving Repr

/-- `bump` on classes. -/
def sbump (k : Aff) : List Aff → Aff × List Aff
  | [] => (k, [k])
  | [b] => (b.add k, [k])
  | b :: a :: ms => (b.add k, (a.add k) :: ms)

/-- `zag` on classes. -/
def szag (q : Aff) (ms : List Aff) : List Aff → List Aff
  | [] => q :: ms
  | g :: gs => szag g (((q.add g).addc 2) :: ms) gs

/-- `sweep` on classes. -/
def ssweep (gs : List Aff) : List Aff → SR
  | [] => .bad
  | y :: ys =>
    if y.q % 2 = 0 then
      if y.p % 2 = 0 then
        if y.p = 0 then (if y.q = 0 then .bad else .small)
        else ssweep (y.half.sub1 :: gs) ys
      else
        if y.p = 1 then (if y.q = 0 then .bad else .small)
        else .ok (szag (sbump y.sub1.half ys).1 (sbump y.sub1.half ys).2 gs)
    else .split

/-- `next` on classes. -/
def snext : List Aff → SR
  | [] => .bad
  | y :: ys =>
    if y.q % 2 = 0 then
      if y.p % 2 = 0 then .ok ((sbump (y.half.addc 2) ys).1 :: (sbump (y.half.addc 2) ys).2)
      else ssweep [(y.addc 3).half] ys
    else .split

theorem sbump_ev (u : Nat) (k : Aff) (ys : List Aff) :
    bump (k.ev u) (ys.map (Aff.ev u)) = ((sbump k ys).1.ev u, (sbump k ys).2.map (Aff.ev u)) := by
  match ys with
  | [] => rfl
  | [b] => simp [bump, sbump, Aff.ev_add]
  | b :: a :: ms => simp [bump, sbump, Aff.ev_add]

theorem szag_ev (u : Nat) (gs : List Aff) : ∀ (q : Aff) (ms : List Aff),
    zag (q.ev u) (ms.map (Aff.ev u)) (gs.map (Aff.ev u)) = (szag q ms gs).map (Aff.ev u) := by
  induction gs with
  | nil => intro q ms; rfl
  | cons g gs ih =>
    intro q ms
    simp only [List.map, zag, szag]
    rw [← ih]; simp [Aff.ev_add, Aff.ev_addc]

theorem ssweep_ok (u : Nat) (ys : List Aff) : ∀ (gs out : List Aff), ssweep gs ys = .ok out →
    sweep (gs.map (Aff.ev u)) (ys.map (Aff.ev u)) = .ok (out.map (Aff.ev u)) := by
  induction ys with
  | nil => intro gs out h; simp [ssweep] at h
  | cons y ys ih =>
    intro gs out h
    simp only [ssweep] at h
    have hge := Aff.ev_ge u y
    by_cases hq : y.q % 2 = 0
    · rw [if_pos hq] at h
      have hm := Aff.ev_mod u y hq
      by_cases hp : y.p % 2 = 0
      · rw [if_pos hp] at h
        by_cases h0 : y.p = 0
        · rw [if_pos h0] at h; split at h <;> cases h
        rw [if_neg h0] at h
        have hh := ih _ out h
        simp only [List.map] at hh
        simp only [List.map, sweep]
        rw [if_pos (by omega), if_neg (by omega)]
        rw [Aff.ev_sub1 u _ (by simp only [Aff.half]; omega), Aff.ev_half u y hq] at hh
        exact hh
      · rw [if_neg hp] at h
        by_cases h1 : y.p = 1
        · rw [if_pos h1] at h; split at h <;> cases h
        rw [if_neg h1] at h
        cases h
        simp only [List.map, sweep]
        rw [if_neg (by omega), if_neg (by omega)]
        have hk : (y.ev u - 1) / 2 = y.sub1.half.ev u := by
          rw [Aff.ev_half u _ (by simp only [Aff.sub1]; exact hq), Aff.ev_sub1 u y (by omega)]
        rw [hk, sbump_ev, szag_ev]
    · rw [if_neg hq] at h; cases h

theorem snext_ok (u : Nat) (zs out : List Aff) (h : snext zs = .ok out) :
    next (zs.map (Aff.ev u)) = .ok (out.map (Aff.ev u)) := by
  match zs with
  | [] => simp [snext] at h
  | y :: ys =>
    simp only [snext] at h
    by_cases hq : y.q % 2 = 0
    · rw [if_pos hq] at h
      have hm := Aff.ev_mod u y hq
      by_cases hp : y.p % 2 = 0
      · rw [if_pos hp] at h
        cases h
        simp only [List.map, next]
        rw [if_pos (by omega)]
        have hk : y.ev u / 2 + 2 = (y.half.addc 2).ev u := by rw [Aff.ev_addc, Aff.ev_half u y hq]
        rw [hk, sbump_ev]
      · rw [if_neg hp] at h
        have hh := ssweep_ok u ys _ out h
        simp only [List.map, next]
        rw [if_neg (by omega)]
        have hk : (y.ev u + 3) / 2 = (y.addc 3).half.ev u := by
          rw [Aff.ev_half u _ (by simp only [Aff.addc]; exact hq), Aff.ev_addc]
        rw [hk]; exact hh
    · rw [if_neg hq] at h; cases h

/-- `n` symbolic passes. -/
def srunN : Nat → List Aff → Option (List Aff)
  | 0, l => some l
  | n + 1, l => match snext l with
    | .ok l' => srunN n l'
    | _ => none

theorem srunN_ok (u : Nat) (n : Nat) : ∀ (l out : List Aff), srunN n l = some out →
    iterN n (.ok (l.map (Aff.ev u))) = .ok (out.map (Aff.ev u)) := by
  induction n with
  | zero => intro l out h; simp [srunN] at h; subst h; rfl
  | succ n ih =>
    intro l out h
    simp only [srunN] at h
    split at h
    · rename_i l' hl
      simp only [iterN, stepN]; rw [snext_ok u l l' hl]; exact ih _ _ h
    · cases h

/-- A two-block state `[2a'+1, a']` on the whole class. -/
def isRet : List Aff → Bool
  | [b, a] => b.q == 2 * a.q && b.p == 2 * a.p + 1
  | _ => false

/-- Symbolic passes (at most `fuel`) until a two-block state `[2a'+1, a']`: that state and the number of passes. -/
def srun : Nat → List Aff → SR × Nat
  | 0, _ => (.bad, 0)
  | f + 1, l => match snext l with
    | .ok l' => if isRet l' then (.ok l', 1) else
        match srun f l' with
        | (.ok l'', n) => (.ok l'', n + 1)
        | r => r
    | r => (r, 0)

theorem srun_ok (u : Nat) (f : Nat) : ∀ (l out : List Aff) (n : Nat), srun f l = (.ok out, n) →
    iterN n (.ok (l.map (Aff.ev u))) = .ok (out.map (Aff.ev u)) := by
  induction f with
  | zero => intro l out n h; simp [srun] at h
  | succ f ih =>
    intro l out n h
    simp only [srun] at h
    cases hs : snext l with
    | ok l' =>
      rw [hs] at h; dsimp only at h
      have h1 := snext_ok u l l' hs
      by_cases hr : isRet l' = true
      · rw [if_pos hr] at h; cases h; simp only [iterN, stepN]; rw [h1]
      · rw [if_neg hr] at h
        cases hm : srun f l' with
        | mk r m =>
          rw [hm] at h
          cases r with
          | ok l'' =>
            simp only [Prod.mk.injEq, SR.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            simp only [iterN, stepN]; rw [h1]; exact ih _ _ _ hm
          | split => simp at h
          | small => simp at h
          | bad => simp at h
    | split => rw [hs] at h; simp at h
    | small => rw [hs] at h; simp at h
    | bad => rw [hs] at h; simp at h

/-- Concrete passes (at most `fuel`) until a two-block state `[2a'+1, a']`. -/
def crun : Nat → List Nat → Option (List Nat × Nat)
  | 0, _ => none
  | f + 1, l => match next l with
    | .ok l' => match l' with
      | [b, a] => if b = 2 * a + 1 then some (l', 1) else (crun f l').map fun r => (r.1, r.2 + 1)
      | _ => (crun f l').map fun r => (r.1, r.2 + 1)
    | _ => none

theorem crun_ok (f : Nat) : ∀ (l out : List Nat) (n : Nat), crun f l = some (out, n) →
    iterN n (.ok l) = .ok out := by
  induction f with
  | zero => intro l out n h; simp [crun] at h
  | succ f ih =>
    intro l out n h
    simp only [crun] at h
    split at h
    · rename_i l' hl
      have tail : ∀ {out n}, (crun f l').map (fun r => (r.1, r.2 + 1)) = some (out, n) →
          iterN n (.ok l) = .ok out := by
        intro out n h
        cases hc : crun f l' with
        | none => rw [hc] at h; cases h
        | some r =>
          rw [hc] at h; cases h
          simp only [iterN, stepN]; rw [hl]; exact ih _ _ _ hc
      split at h
      · split at h
        · cases h; simp only [iterN, stepN]; rw [hl]
        · exact tail h
      · exact tail h
    · cases h

/-- The return from `[2a+1, a]`, checked concretely. -/
def cgood (a : Nat) : Bool :=
  match crun 1000 [2 * a + 1, a] with
  | some ([b, a'], n) => n % 9 == 0 && 9 ≤ n && a' == a + 12 * (n / 9) && b == 2 * a' + 1
  | _ => false

theorem cgood_ok (a : Nat) (h : cgood a = true) : Returns a := by
  unfold cgood at h
  split at h
  · rename_i b a' n hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h9, hn⟩, ha⟩, hb⟩ := h
    have := crun_ok _ _ _ _ hc
    refine ⟨n / 9, by omega, ?_⟩
    rw [show 9 * (n / 9) = n by omega, this, hb, ha]
  · cases h

/-- The class `p + q*u` returns as a whole: one route, `9k` passes, `a' = a + 12k`. -/
def sgood (p q : Nat) : SR :=
  match srun 200 [⟨2 * p + 1, 2 * q⟩, ⟨p, q⟩] with
  | (.ok [b, a'], n) =>
    if n % 9 == 0 && 9 ≤ n && a'.q == q && a'.p == p + 12 * (n / 9) && b.q == 2 * q && b.p == 2 * a'.p + 1
    then .ok [] else .bad
  | (.ok _, _) => .bad
  | (r, _) => r

theorem sgood_ok (p q : Nat) (h : sgood p q = .ok []) (u : Nat) : Returns (p + q * u) := by
  unfold sgood at h
  split at h
  · rename_i b a' n hs
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨h9, hn⟩, hq⟩, hp⟩, hbq⟩, hbp⟩ := hc
      have hr := srun_ok u _ _ _ _ hs
      refine ⟨n / 9, by omega, ?_⟩
      rw [show 9 * (n / 9) = n by omega]
      simp only [List.map, Aff.ev] at hr
      have e1 : 2 * p + 1 + 2 * q * u = 2 * (p + q * u) + 1 := by rw [Nat.mul_assoc]; omega
      have e2 : b.p + b.q * u = 2 * (p + q * u + 12 * (n / 9)) + 1 := by
        rw [hbq, hbp, hp, Nat.mul_assoc]; omega
      have e3 : a'.p + a'.q * u = p + q * u + 12 * (n / 9) := by rw [hq, hp]; omega
      rw [e1, e2, e3] at hr; exact hr
    · cases h
  · cases h
  · rename_i r n _ _; cases r <;> simp_all

/-- Every member below `B` of the class `p + q*u` returns: run the class, split it by the parity of `u` (`d` more
times), set `u = 0` aside, or run the one member below `B` at the depth limit. -/
def explore (B : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | f + 1, d, p, q =>
    if B ≤ p then true else
    match sgood p q with
    | .ok _ => true
    | .split => match d with
      | 0 => decide (B ≤ q) && cgood p
      | d + 1 => explore B f d p (2 * q) && explore B f d (p + q) (2 * q)
    | .small => cgood p && explore B f d (p + q) q
    | .bad => false

theorem explore_ok (B : Nat) (f : Nat) : ∀ (d p q : Nat), explore B f d p q = true →
    ∀ u, p + q * u < B → Returns (p + q * u) := by
  induction f with
  | zero => intro d p q h; simp [explore] at h
  | succ f ih =>
    intro d p q h u hu
    simp only [explore] at h
    by_cases hB : B ≤ p
    · omega
    rw [if_neg hB] at h
    split at h
    · rename_i l hs
      cases l with
      | nil => exact sgood_ok p q hs u
      | cons _ _ =>
        unfold sgood at hs
        split at hs <;> (try split at hs) <;> simp_all
    · split at h
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hq, hc⟩ := h
        cases u with
        | zero => simpa using cgood_ok p hc
        | succ v => exfalso; have : q ≤ q * (v + 1) := Nat.le_mul_of_pos_right q (by omega); omega
      · rename_i d
        simp only [Bool.and_eq_true] at h
        obtain ⟨h0, h1⟩ := h
        obtain ⟨v, rfl | rfl⟩ : ∃ v, u = 2 * v ∨ u = 2 * v + 1 := ⟨u / 2, by omega⟩
        · have e : 2 * q * v = q * (2 * v) := by rw [Nat.mul_comm 2 q, Nat.mul_assoc]
          have := ih d p (2 * q) h0 v (by rw [e]; exact hu)
          rwa [e] at this
        · have := ih d (p + q) (2 * q) h1 v (by
            rw [Nat.mul_add, Nat.mul_one] at hu
            rw [show 2 * q * v = q * (2 * v) by rw [Nat.mul_comm 2 q, Nat.mul_assoc]]; omega)
          rwa [show p + q + 2 * q * v = p + q * (2 * v + 1) by
            rw [Nat.mul_add, Nat.mul_one, show 2 * q * v = q * (2 * v) by rw [Nat.mul_comm 2 q, Nat.mul_assoc]]
            omega] at this
    · simp only [Bool.and_eq_true] at h
      obtain ⟨hc, h1⟩ := h
      cases u with
      | zero => simpa using cgood_ok p hc
      | succ v =>
        have := ih d (p + q) q h1 v (by rw [Nat.mul_add, Nat.mul_one] at hu; omega)
        rwa [show p + q + q * v = p + q * (v + 1) by rw [Nat.mul_add, Nat.mul_one]; omega] at this
    · cases h

/-- `explore` from the class `a = 5 + 4u` covers every `a = 1 mod 4` with `5 ≤ a < B`. -/
theorem returns_of_explore (B f d : Nat) (h : explore B f d 5 4 = true) :
    ∀ a, a % 4 = 1 → 5 ≤ a → a < B → Returns a := by
  intro a h1 h5 hB
  have := explore_ok B f d 5 4 h ((a - 5) / 4) (by omega)
  rwa [show 5 + 4 * ((a - 5) / 4) = a by omega] at this

/-- Every member below `B` of the class `p + q*u` returns. -/
def Cov (B p q : Nat) : Prop := ∀ u, p + q * u < B → Returns (p + q * u)

theorem Cov.of_explore {B f d p q : Nat} (h : explore B f d p q = true) : Cov B p q := explore_ok B f d p q h

/-- A class is covered when both halves (`u` even, `u` odd) are. -/
theorem Cov.split {B p q p' q' : Nat} (hp : p' = p + q) (hq : q' = 2 * q) (h0 : Cov B p q') (h1 : Cov B p' q') :
    Cov B p q := by
  intro u hu
  subst hp hq
  have e : ∀ v, 2 * q * v = q * (2 * v) := fun v => by rw [Nat.mul_comm 2 q, Nat.mul_assoc]
  obtain ⟨v, rfl | rfl⟩ : ∃ v, u = 2 * v ∨ u = 2 * v + 1 := ⟨u / 2, by omega⟩
  · have := h0 v (by rw [e]; exact hu); rwa [e] at this
  · rw [Nat.mul_add, Nat.mul_one] at hu ⊢
    have := h1 v (by rw [e]; omega)
    rwa [e, show p + q + q * (2 * v) = p + (q * (2 * v) + q) by omega] at this

/-- The class `a = 5 + 4u` covered: every `a = 1 mod 4` with `5 ≤ a < B` returns. -/
theorem returns_of_cov {B : Nat} (h : Cov B 5 4) : ∀ a, a % 4 = 1 → 5 ≤ a → a < B → Returns a := by
  intro a h1 h5 hB
  have := h ((a - 5) / 4) (by omega)
  rwa [show 5 + 4 * ((a - 5) / 4) = a by omega] at this

/-! ## The short chains, for every `a ≥ 5` (kernel) -/

/-- `srunN n` from the class `p + 4u` of `[2a+d, a]` ends at `[2(a+s)+d', a+s]` (with `2p + d = e`, `2(p+s) + d' = e'`).
-/
theorem chain_of (p e s e' n : Nat) (h : srunN n [⟨e, 8⟩, ⟨p, 4⟩] = some [⟨e', 8⟩, ⟨p + s, 4⟩]) (u : Nat) :
    iterN n (.ok [e + 8 * u, p + 4 * u]) = .ok [e' + 8 * u, p + 4 * u + s] := by
  have := srunN_ok u n _ _ h
  simp only [List.map, Aff.ev] at this
  rw [this]; congr 3; omega

/-- `[a, 2a]`, `a = 0 mod 4`: one pass to `[a+2, 2(a+2)-2]`. -/
theorem chain_0 (a : Nat) (h4 : a % 4 = 0) (h5 : 5 ≤ a) :
    iterN 1 (.ok [2 * a, a]) = .ok [2 * (a + 2) - 2, a + 2] := by
  have := chain_of 8 16 2 18 1 (by decide) ((a - 8) / 4)
  rw [show 16 + 8 * ((a - 8) / 4) = 2 * a by omega, show 8 + 4 * ((a - 8) / 4) = a by omega,
    show 18 + 8 * ((a - 8) / 4) = 2 * (a + 2) - 2 by omega] at this
  exact this

/-- `[a, 2a-2]`, `a = 2 mod 4`: one pass to `[a+1, 2(a+1)-1]`. -/
theorem chain_m2 (a : Nat) (h4 : a % 4 = 2) (h5 : 5 ≤ a) :
    iterN 1 (.ok [2 * a - 2, a]) = .ok [2 * (a + 1) - 1, a + 1] := by
  have := chain_of 6 10 1 13 1 (by decide) ((a - 6) / 4)
  rw [show 10 + 8 * ((a - 6) / 4) = 2 * a - 2 by omega, show 6 + 4 * ((a - 6) / 4) = a by omega,
    show 13 + 8 * ((a - 6) / 4) = 2 * (a + 1) - 1 by omega] at this
  exact this

/-- `[a, 2a+2]`, `a = 2 mod 4`: one pass to `[a+3, 2(a+3)-3]`. -/
theorem chain_2 (a : Nat) (h4 : a % 4 = 2) (h5 : 5 ≤ a) :
    iterN 1 (.ok [2 * a + 2, a]) = .ok [2 * (a + 3) - 3, a + 3] := by
  have := chain_of 6 14 3 15 1 (by decide) ((a - 6) / 4)
  rw [show 14 + 8 * ((a - 6) / 4) = 2 * a + 2 by omega, show 6 + 4 * ((a - 6) / 4) = a by omega,
    show 15 + 8 * ((a - 6) / 4) = 2 * (a + 3) - 3 by omega] at this
  exact this

/-- `[a, 2a-1]`, `a = 3 mod 4`: two passes to `[a+2, 2(a+2)+1]`. -/
theorem chain_m1 (a : Nat) (h4 : a % 4 = 3) (h5 : 5 ≤ a) :
    iterN 2 (.ok [2 * a - 1, a]) = .ok [2 * (a + 2) + 1, a + 2] := by
  have := chain_of 7 13 2 19 2 (by decide) ((a - 7) / 4)
  rw [show 13 + 8 * ((a - 7) / 4) = 2 * a - 1 by omega, show 7 + 4 * ((a - 7) / 4) = a by omega,
    show 19 + 8 * ((a - 7) / 4) = 2 * (a + 2) + 1 by omega] at this
  exact this

/-- `[a, 2a+3]`, `a = 3 mod 4`: two passes to `[a+3, 2(a+3)+2]`. -/
theorem chain_3 (a : Nat) (h4 : a % 4 = 3) (h5 : 5 ≤ a) :
    iterN 2 (.ok [2 * a + 3, a]) = .ok [2 * (a + 3) + 2, a + 3] := by
  have := chain_of 7 17 3 22 2 (by decide) ((a - 7) / 4)
  rw [show 17 + 8 * ((a - 7) / 4) = 2 * a + 3 by omega, show 7 + 4 * ((a - 7) / 4) = a by omega,
    show 22 + 8 * ((a - 7) / 4) = 2 * (a + 3) + 2 by omega] at this
  exact this

/-- `[a, 2a-3]`, `a = 1 mod 4`: three passes to `[a+3, 2(a+3)]`. -/
theorem chain_m3 (a : Nat) (h4 : a % 4 = 1) (h5 : 5 ≤ a) :
    iterN 3 (.ok [2 * a - 3, a]) = .ok [2 * (a + 3), a + 3] := by
  have := chain_of 5 7 3 16 3 (by decide) ((a - 5) / 4)
  rw [show 7 + 8 * ((a - 5) / 4) = 2 * a - 3 by omega, show 5 + 4 * ((a - 5) / 4) = a by omega,
    show 16 + 8 * ((a - 5) / 4) = 2 * (a + 3) by omega] at this
  exact this

/-! ## The return map, checked -/

/-- Every `a = 1 mod 4` with `5 ≤ a < 2^16` returns: checked by the kernel, no `native_decide`. -/
theorem returns_2_16 : ∀ a, a % 4 = 1 → 5 ≤ a → a < 2 ^ 16 → Returns a :=
  returns_of_explore _ 100 14 (by decide)

/-- Every `a = 1 mod 4` with `5 ≤ a < 2^62` returns: the evaluation of `explore` trusts Lean's compiler
(`native_decide`). -/
theorem returns_2_62 : ∀ a, a % 4 = 1 → 5 ≤ a → a < 2 ^ 62 → Returns a :=
  returns_of_explore _ 200 60 (by native_decide)

/-- **The first 3·2^60 + 1 ≈ 3.46·10¹⁸ passes** from blank tape never stop at a block of 1: each is a block list,
and the machine reaches its pass start (so it runs at least that many steps without halting).  Rests on
`returns_2_62`, so on `native_decide`. -/
theorem no_one_3e18 (n : Nat) (hn : n ≤ 3 * 2 ^ 60 + 1) :
    ∃ zs t, orbit n = .ok zs ∧ zs.sum = 4 * n ∧ n ≤ t ∧ steps t init = some ⟨enc zs, blank, .A⟩ :=
  reach_upto _ returns_2_62 n (by omega)

/-- The same from `returns_2_16`, kernel only: the first 49,153 passes. -/
theorem no_one_49153 (n : Nat) (hn : n ≤ 49153) :
    ∃ zs t, orbit n = .ok zs ∧ zs.sum = 4 * n ∧ n ≤ t ∧ steps t init = some ⟨enc zs, blank, .A⟩ :=
  reach_upto _ returns_2_16 n (by omega)

end BB6d
