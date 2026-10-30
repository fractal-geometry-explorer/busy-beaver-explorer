import Cascade

/-!
# Every level cycles or goes silent, and silent means no halt

The bottom `k` levels of the super orbit run on their own (`superL_split`): one super step takes them by `bstep`, and
what happens further left never comes back.  Here, for every `k` and every state `B` of the bottom `k` levels:

* `cycles_or_silent`: after some `n` super steps the bottom either **cycles** (comes back to itself after `m > 0`
  more super steps) or is **silent** (never passes anything on to the levels further left again);
* `rep_of_cycles`: a cycling bottom has a table in the sense of `Cascade.lean` (`Rep`), of length its period;
* `never_halts_of_silent`: if a silent bottom occurs on the super orbit from blank tape, the machine never halts
  (the wave never again reaches the left end, so `N` is never a power of two);
* `cycles_or_never_halts`: so on the orbit, after the bottom `k` levels have appeared, either the machine halts
  within `n` more super steps, or at super step `j + n` the bottom `k` levels cycle with a table, or the machine never
  halts.

The proof is by induction on `k`.  If the bottom `B` is silent, so is `B ++ [p]`.  If `B` cycles with period `m` and
passes at least one wave on in a period, the next level's block goes from `q` to `F q` per period with
`2 F q ≤ q + 2 W` (each wave halves it; `W` bounds what a period adds), so it stays below `q₀ + 2 W` and, by
pigeonhole, repeats: `B ++ [p]` cycles.  If `B` passes no wave on, the next level only receives adds and passes
nothing on: `B ++ [p]` is silent.

Which of the cases holds on the actual orbit is not decided here.  For the first six levels the cycle is checked by
`decide` at the end of the file.
-/

namespace BB6b

open TM

/-! ## The bottom on its own -/

/-- `n` super steps of the bottom on its own. -/
def bs : Nat → List Nat → List Nat
  | 0, B => B
  | n + 1, B => bs n (bstep B).1

theorem bs_add : ∀ (a b : Nat) (B : List Nat), bs (a + b) B = bs b (bs a B) := by
  intro a
  induction a with
  | zero => intro b B; simp [bs]
  | succ a ih => intro b B; rw [show a + 1 + b = (a + b) + 1 by omega]; exact ih b _

/-- The bottom cycles. -/
def Cycles (B : List Nat) : Prop := ∃ m, 0 < m ∧ bs m B = B

/-- The bottom never passes anything on again. -/
def Silent (B : List Nat) : Prop := ∀ i, (bstep (bs i B)).2.1 = .none

def isWave : Ev → Bool
  | .wave _ => true
  | _ => false

/-- The block of one more level (with block `q` at the start) after `i` super steps of the bottom `C`. -/
def topv : Nat → List Nat → Nat → Nat
  | 0, _, q => q
  | i + 1, C, q => topv i (bstep C).1 (lev q (bstep C).2.1).1

theorem bs_append : ∀ (i : Nat) (C : List Nat) (q : Nat), bs i (C ++ [q]) = bs i C ++ [topv i C q] := by
  intro i
  induction i with
  | zero => intro C q; rfl
  | succ i ih => intro C q; simp only [bs, topv, bstep_append]; exact ih _ _

/-! ## Silent -/

theorem lev_quiet (x : Nat) : ∀ e, isWave e = false → (lev x e).2.1 = .none
  | .none, _ => rfl
  | .add _, _ => rfl
  | .wave _, h => by simp [isWave] at h

/-- A bottom that never passes a wave on makes one more level silent. -/
theorem silent_append (C : List Nat) (q : Nat) (h : ∀ i, isWave (bstep (bs i C)).2.1 = false) :
    Silent (C ++ [q]) := by
  intro i
  rw [bs_append, bstep_append]
  exact lev_quiet _ _ (h i)

/-- Whether the bottom passes a wave on in its next `i` super steps. -/
def hasW : Nat → List Nat → Bool
  | 0, _ => false
  | i + 1, C => isWave (bstep C).2.1 || hasW i (bstep C).1

theorem hasW_false : ∀ (i : Nat) (C : List Nat), hasW i C = false → ∀ j, j < i → isWave (bstep (bs j C)).2.1 = false := by
  intro i
  induction i with
  | zero => intro C _ j hj; omega
  | succ i ih =>
    intro C h j hj
    simp only [hasW, Bool.or_eq_false_iff] at h
    cases j with
    | zero => exact h.1
    | succ j => exact ih _ h.2 j (by omega)

/-- A cycling bottom that passes no wave on in a period never does. -/
theorem nowave_of_cycle (C : List Nat) (m : Nat) (hm : 0 < m) (hC : bs m C = C) (hw : hasW m C = false) :
    ∀ i, isWave (bstep (bs i C)).2.1 = false := by
  have key : ∀ n i, i < n → isWave (bstep (bs i C)).2.1 = false := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      by_cases h : i < m
      · exact hasW_false m C hw i h
      · rw [show i = m + (i - m) by omega, bs_add, hC]
        exact ih _ (by omega)
  exact fun i => key (i + 1) i (by omega)

/-! ## Bounded -/

/-- A bound on what an event adds to a block. -/
def wt : Ev → Nat
  | .none => 0
  | .add a => a
  | .wave h => h + 5

theorem lev_le (q : Nat) : ∀ e, (lev q e).1 ≤ q + wt e
  | .none => by simp [lev, wt]
  | .add a => by simp [lev, wt]
  | .wave h => by
    simp only [lev, wt]
    split <;> (try simp only) <;> omega

theorem lev_wave (q h : Nat) : 2 * (lev q (.wave h)).1 ≤ q + 2 * wt (.wave h) := by
  simp only [lev, wt]
  split <;> (try simp only) <;> omega

def wsum : Nat → List Nat → Nat
  | 0, _ => 0
  | i + 1, C => wt (bstep C).2.1 + wsum i (bstep C).1

theorem topv_le : ∀ (i : Nat) (C : List Nat) (q : Nat), topv i C q ≤ q + wsum i C := by
  intro i
  induction i with
  | zero => intro C q; simp [topv, wsum]
  | succ i ih =>
    intro C q
    have h₁ := ih (bstep C).1 (lev q (bstep C).2.1).1
    have h₂ := lev_le q (bstep C).2.1
    simp only [topv, wsum]
    omega

/-- **A wave halves the block**: over a stretch with a wave, the next level ends below half its start plus a
constant. -/
theorem topv_half : ∀ (i : Nat) (C : List Nat) (q : Nat), hasW i C = true → 2 * topv i C q ≤ q + 2 * wsum i C := by
  intro i
  induction i with
  | zero => intro C q h; simp [hasW] at h
  | succ i ih =>
    intro C q h
    simp only [topv, wsum]
    simp only [hasW, Bool.or_eq_true] at h
    have h₂ := lev_le q (bstep C).2.1
    by_cases hw : isWave (bstep C).2.1 = true
    · have h₁ := topv_le i (bstep C).1 (lev q (bstep C).2.1).1
      have h₃ : 2 * (lev q (bstep C).2.1).1 ≤ q + 2 * wt (bstep C).2.1 := by
        generalize (bstep C).2.1 = e at hw
        cases e with
        | wave h => exact lev_wave q h
        | _ => simp [isWave] at hw
      omega
    · have h₁ := ih (bstep C).1 (lev q (bstep C).2.1).1 (by simpa [hw] using h)
      omega

/-! ## Pigeonhole -/

theorem pigeon : ∀ (n : Nat) (g : Nat → Nat), (∀ i, i ≤ n → g i < n) → ∃ i j, i < j ∧ j ≤ n ∧ g i = g j := by
  intro n
  induction n with
  | zero => intro g hg; have := hg 0 (Nat.le_refl 0); omega
  | succ n ih =>
    intro g hg
    by_cases hx : ∃ i, i < n + 1 ∧ g i = g (n + 1)
    · obtain ⟨i, hi, he⟩ := hx
      exact ⟨i, n + 1, hi, Nat.le_refl _, he⟩
    · have hne : ∀ i, i ≤ n → g i ≠ g (n + 1) := fun i hi e => hx ⟨i, by omega, e⟩
      have hl := hg (n + 1) (Nat.le_refl _)
      obtain ⟨i, j, hij, hj, he⟩ := ih (fun i => if g i = n then g (n + 1) else g i) (by
        intro i hi
        have := hg i (by omega)
        have := hne i hi
        split <;> omega)
      refine ⟨i, j, hij, by omega, ?_⟩
      have := hne i (by omega)
      have := hne j hj
      split at he <;> split at he <;> omega

/-- `F` applied `r` times. -/
def iter (F : Nat → Nat) : Nat → Nat → Nat
  | 0, q => q
  | r + 1, q => iter F r (F q)

theorem iter_add (F : Nat → Nat) : ∀ (a b q : Nat), iter F (a + b) q = iter F a (iter F b q) := by
  intro a b
  induction b with
  | zero => intro q; rfl
  | succ b ih => intro q; rw [← Nat.add_assoc]; exact ih (F q)

theorem iter_le (F : Nat → Nat) (M : Nat) (hF : ∀ q, q ≤ M → F q ≤ M) : ∀ r q, q ≤ M → iter F r q ≤ M := by
  intro r
  induction r with
  | zero => intro q h; exact h
  | succ r ih => intro q h; exact ih (F q) (hF q h)

/-- Over whole periods of a cycling bottom, one more level just iterates `topv m C`. -/
theorem bs_iter (C : List Nat) (m : Nat) (hC : bs m C = C) : ∀ r q, bs (r * m) (C ++ [q]) = C ++ [iter (topv m C) r q] := by
  intro r
  induction r with
  | zero => intro q; simp [bs, iter]
  | succ r ih =>
    intro q
    rw [Nat.succ_mul, Nat.add_comm, bs_add, bs_append, hC, ih]
    rfl

/-! ## Cycles or silent -/

theorem cycles_or_silent_rev : ∀ (R : List Nat), ∃ n, Cycles (bs n R.reverse) ∨ Silent (bs n R.reverse) := by
  intro R
  induction R with
  | nil => exact ⟨0, Or.inl ⟨1, by decide, rfl⟩⟩
  | cons p R ih =>
    obtain ⟨n, h⟩ := ih
    rw [List.reverse_cons]
    have hb := bs_append n R.reverse p
    rcases h with ⟨m, hm, hC⟩ | hS
    · cases hw : hasW m (bs n R.reverse) with
      | false =>
        refine ⟨n, Or.inr ?_⟩
        rw [hb]
        exact silent_append _ _ (nowave_of_cycle _ m hm hC hw)
      | true =>
        let C := bs n R.reverse
        let F := topv m C
        let q₀ := topv n R.reverse p
        have hF : ∀ q, q ≤ q₀ + 2 * wsum m C → F q ≤ q₀ + 2 * wsum m C := by
          intro q hq
          show topv m C q ≤ _
          have := topv_half m C q hw
          omega
        obtain ⟨i, j, hij, _, he⟩ := pigeon (q₀ + 2 * wsum m C + 1) (fun r => iter F r q₀)
          (fun r _ => Nat.lt_succ_of_le (iter_le F _ hF r q₀ (by omega)))
        have key : bs (n + i * m) (R.reverse ++ [p]) = C ++ [iter F i q₀] := by
          rw [bs_add, hb]
          exact bs_iter C m hC i q₀
        refine ⟨n + i * m, Or.inl ⟨(j - i) * m, Nat.mul_pos (by omega) hm, ?_⟩⟩
        rw [key, bs_iter C m hC (j - i), ← iter_add, show j - i + i = j by omega]
        rw [← he]
    · refine ⟨n, Or.inr ?_⟩
      rw [hb]
      exact silent_append _ _ (fun i => by rw [hS i]; rfl)

/-- **Every bottom cycles or goes silent.** -/
theorem cycles_or_silent (B : List Nat) : ∃ n, Cycles (bs n B) ∨ Silent (bs n B) := by
  simpa using cycles_or_silent_rev B.reverse

/-! ## A cycling bottom has a table -/

theorem chain_of_bs : ∀ (m : Nat) (D : List Nat), ∃ (T : List Entry) (tl : Nat × Nat) (Dx : List Nat), Chain D T Dx ∧ Quiet tl.1 Dx tl.2 (bs m D) ∧
    lenT T + tl.1 = m := by
  intro m
  induction m with
  | zero => intro D; exact ⟨[], (0, 0), D, rfl, ⟨rfl, rfl⟩, by simp [lenT]⟩
  | succ m ih =>
    intro D
    obtain ⟨T, tl, Dx, hc, hq, hl⟩ := ih (bstep D).1
    by_cases he : (bstep D).2.1 = .none
    · cases T with
      | nil =>
        cases hc
        refine ⟨[], (tl.1 + 1, (bstep D).2.2 + tl.2), D, rfl, ⟨he, tl.2, rfl, hq⟩, ?_⟩
        simp only [lenT, List.map_nil, List.sum_nil] at hl ⊢
        omega
      | cons x T =>
        obtain ⟨dt, e, c⟩ := x
        obtain ⟨n, c₁, Bm, rfl, hq₁, he₁, rfl, hc'⟩ := hc
        refine ⟨(n + 2, e, ((bstep D).2.2 + c₁) + (bstep Bm).2.2) :: T, tl, Dx,
          ⟨n + 1, (bstep D).2.2 + c₁, Bm, rfl, ⟨he, c₁, rfl, hq₁⟩, he₁, rfl, hc'⟩, hq, ?_⟩
        simp only [lenT, List.map_cons, List.sum_cons] at hl ⊢
        omega
    · refine ⟨(1, (bstep D).2.1, (bstep D).2.2) :: T, tl, Dx,
        ⟨0, 0, D, rfl, ⟨rfl, rfl⟩, rfl, by omega, hc⟩, hq, ?_⟩
      simp only [lenT, List.map_cons, List.sum_cons] at hl ⊢
      omega

/-- **A cycling bottom has a table** whose length is its period. -/
theorem rep_of_cycles (D : List Nat) (m : Nat) (hD : bs m D = D) :
    ∃ T tl, Rep D T tl ∧ lenT T + tl.1 = m := by
  obtain ⟨T, tl, Dx, hc, hq, hl⟩ := chain_of_bs m D
  rw [hD] at hq
  exact ⟨T, tl, ⟨Dx, hc, hq⟩, hl⟩

/-! ## On the orbit -/

theorem orbit_add : ∀ (a b : Nat) (L : List Nat), orbit (a + b) L = (orbit a L).bind (orbit b) := by
  intro a
  induction a with
  | zero => intro b L; simp [orbit]
  | succ a ih =>
    intro b L
    rw [show a + 1 + b = (a + b) + 1 by omega]
    cases e : superL L with
    | none => simp [orbit, e]
    | some L' => simp [orbit, e, ih]

theorem orbit_good : ∀ (j : Nat) (L W : List Nat), GoodL L → orbit j L = some W → GoodL W := by
  intro j
  induction j with
  | zero => intro L W hL h; cases h; exact hL
  | succ j ih =>
    intro L W hL h
    cases e : superL L with
    | none => simp [orbit, e] at h
    | some L' => simp only [orbit, e, Option.bind_some] at h; exact ih L' W (superL_good L L' hL e) h

/-- **The bottom of the orbit is `bs`**, as long as the orbit runs. -/
theorem orbit_split : ∀ (i : Nat) (B U : List Nat), U ≠ [] →
    orbit i (B ++ U) = none ∨ ∃ U', U' ≠ [] ∧ orbit i (B ++ U) = some (bs i B ++ U') := by
  intro i
  induction i with
  | zero => intro B U hU; exact Or.inr ⟨U, hU, rfl⟩
  | succ i ih =>
    intro B U hU
    have hs := superL_split B U hU
    cases hp : push (bstep B).2.1 U with
    | none => left; simp [orbit, hs, hp]
    | some U₁ =>
      have h₁ : orbit (i + 1) (B ++ U) = orbit i ((bstep B).1 ++ U₁) := by simp [orbit, hs, hp]
      rw [h₁]
      exact ih _ _ (push_ne _ U U₁ hU hp)

/-- A silent bottom with something to its left: the orbit runs on forever and only the bottom changes. -/
theorem silent_orbit : ∀ (i : Nat) (B U : List Nat), U ≠ [] → Silent B → orbit i (B ++ U) = some (bs i B ++ U) := by
  intro i
  induction i with
  | zero => intro B U _ _; rfl
  | succ i ih =>
    intro B U hU hS
    have hs := superL_split B U hU
    rw [show (bstep B).2.1 = .none from hS 0] at hs
    simp only [push, Option.map_some] at hs
    simp only [orbit, hs, Option.bind_some]
    exact ih _ U hU (fun j => hS (j + 1))

/-- The orbit from blank tape stops only by halting. -/
theorem halts_of_orbit_none (i : Nat) (h : orbit i [6, 1] = none) : HaltsFromBlank := by
  have key : ∀ (i : Nat) (L : List Nat), orbit i L = none → ∃ i' W, orbit i' L = some W ∧ superL W = none := by
    intro i
    induction i with
    | zero => intro L h; cases h
    | succ i ih =>
      intro L h
      cases e : superL L with
      | none => exact ⟨0, L, rfl, e⟩
      | some L' =>
        simp only [orbit, e, Option.bind_some] at h
        obtain ⟨i', W, h₁, h₂⟩ := ih L' h
        exact ⟨i' + 1, W, by simp [orbit, e, h₁], h₂⟩
  obtain ⟨i', W, h₁, h₂⟩ := key i _ h
  have hg := orbit_good i' _ W ⟨by simp, by simp⟩ h₁
  exact halts_iff_pow2.2 ⟨i', W, h₁, (superL_none_iff W hg).1 h₂⟩

/-- **Silent means no halt**: once a silent bottom is on the orbit from blank tape, with blocks to its left, the wave
never reaches the left end again and `N` is never a power of two. -/
theorem never_halts_of_silent (j : Nat) (B U : List Nat) (h : orbit j [6, 1] = some (B ++ U)) (hU : U ≠ [])
    (hS : Silent B) : ¬HaltsFromBlank := by
  intro hH
  rw [halts_iff_pow2] at hH
  obtain ⟨j', W, hW, a, ha⟩ := hH
  have hs : superL W = none := (superL_none_iff W (orbit_good j' _ W ⟨by simp, by simp⟩ hW)).2 ⟨a, ha⟩
  have hn : ∀ r, orbit (j' + 1 + r) [6, 1] = none := by
    intro r
    rw [orbit_add, orbit_add, hW]
    simp [orbit, hs]
  have hr : ∀ r, orbit (j + r) [6, 1] = some (bs r B ++ U) := by
    intro r
    rw [orbit_add, h]
    exact silent_orbit r B U hU hS
  by_cases hj : j ≤ j' + 1
  · have := hr (j' + 1 - j)
    rw [show j + (j' + 1 - j) = j' + 1 + 0 by omega, hn] at this
    cases this
  · have := hn (j - (j' + 1))
    rw [show j' + 1 + (j - (j' + 1)) = j + 0 by omega, hr] at this
    cases this

/-- **Each level cycles, or the machine never halts.**  Once the orbit from blank tape has the bottom `k` levels `B`
with blocks `U` to their left (at super step `j`), there is an `n` such that either the machine halts within `n` more
super steps, or at super step `j + n` the bottom is `bs n B` and it cycles, with a table (`Rep`) as long as its
period, or it is silent and the machine never halts. -/
theorem cycles_or_never_halts (j : Nat) (B U : List Nat) (h : orbit j [6, 1] = some (B ++ U)) (hU : U ≠ []) :
    ∃ n, (orbit (j + n) [6, 1] = none ∧ HaltsFromBlank) ∨
      ∃ U', U' ≠ [] ∧ orbit (j + n) [6, 1] = some (bs n B ++ U') ∧
        ((∃ m T tl, 0 < m ∧ bs m (bs n B) = bs n B ∧ Rep (bs n B) T tl ∧ lenT T + tl.1 = m) ∨
          (Silent (bs n B) ∧ ¬HaltsFromBlank)) := by
  obtain ⟨n, hc⟩ := cycles_or_silent B
  refine ⟨n, ?_⟩
  rw [orbit_add, h, Option.bind_some]
  rcases orbit_split n B U hU with hn | ⟨U', hU', hn⟩
  · rw [hn]
    have : orbit (j + n) [6, 1] = none := by rw [orbit_add, h]; exact hn
    exact Or.inl ⟨rfl, halts_of_orbit_none _ this⟩
  · rw [hn]
    refine Or.inr ⟨U', hU', rfl, ?_⟩
    rcases hc with ⟨m, hm, hD⟩ | hS
    · obtain ⟨T, tl, hR, hl⟩ := rep_of_cycles _ m hD
      exact Or.inl ⟨m, T, tl, hm, hD, hR, hl⟩
    · have : orbit (j + n) [6, 1] = some (bs n B ++ U') := by rw [orbit_add, h]; exact hn
      exact Or.inr ⟨hS, never_halts_of_silent _ _ _ this hU' hS⟩

/-! ## The first six levels, checked

At super step `j` of the orbit from blank tape the bottom `k` levels are `B` (nearest first), and `B` comes back after
`P` super steps of the bottom but not after `P / 2`; since `P` is a power of two, `P` is the least period. -/

theorem cycle₁ : (orbit 3 [6, 1]).map (·.take 1) = some [12] ∧ bs 4 [12] = [12] ∧ bs 2 [12] ≠ [12] := by decide

theorem cycle₂ : (orbit 7 [6, 1]).map (·.take 2) = some [12, 26] ∧ bs 8 [12, 26] = [12, 26] ∧
    bs 4 [12, 26] ≠ [12, 26] := by decide

theorem cycle₃ : (orbit 11 [6, 1]).map (·.take 3) = some [12, 27, 39] ∧ bs 32 [12, 27, 39] = [12, 27, 39] ∧
    bs 16 [12, 27, 39] ≠ [12, 27, 39] := by decide

set_option maxRecDepth 100000 in
theorem cycle₄ : (orbit 31 [6, 1]).map (·.take 4) = some [12, 26, 27, 38] ∧
    bs 128 [12, 26, 27, 38] = [12, 26, 27, 38] ∧ bs 64 [12, 26, 27, 38] ≠ [12, 26, 27, 38] := by decide

set_option maxRecDepth 100000 in
theorem cycle₅ : (orbit 60 [6, 1]).map (·.take 5) = some [11, 19, 28, 47, 111] ∧
    bs 256 [11, 19, 28, 47, 111] = [11, 19, 28, 47, 111] ∧ bs 128 [11, 19, 28, 47, 111] ≠ [11, 19, 28, 47, 111] := by
  decide

set_option maxRecDepth 100000 in
theorem cycle₆ : (orbit 163 [6, 1]).map (·.take 6) = some [12, 27, 36, 37, 93, 184] ∧
    bs 1024 [12, 27, 36, 37, 93, 184] = [12, 27, 36, 37, 93, 184] ∧
    bs 512 [12, 27, 36, 37, 93, 184] ≠ [12, 27, 36, 37, 93, 184] := by decide

end BB6b

#print axioms BB6b.cycles_or_silent
#print axioms BB6b.never_halts_of_silent
#print axioms BB6b.cycles_or_never_halts
#print axioms BB6b.cycle₆
