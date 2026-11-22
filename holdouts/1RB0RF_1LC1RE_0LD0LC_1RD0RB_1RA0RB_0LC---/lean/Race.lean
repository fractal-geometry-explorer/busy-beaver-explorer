import Full

/-!
# The macro map fails only after a lost race

`Full.lean` proves `not_halts_of_arun`: if the macro map `astep` can be applied for ever from the first Q
configuration, the machine never halts.  Here we show where `astep` can fail at all.

A gap is *aligned* when its length is `3p + 2` (the gaps the regular steps write).  The invariant `Inv` says: the
word is a valid word (the first block even and at least 2, every other block odd), the counter's low part is at
least 1, and at most one gap is misaligned.  The start configuration satisfies it, and

* `inv_step`: from a configuration with `Inv`, `astep` is defined and keeps `Inv`, unless the configuration is a
  *lost race*: the word has run out (it is one block, or one block and a single 1, so an anomaly comes next) while a
  misaligned gap is still pending.

So the map can only fail after a lost race, and

* `not_halts_of_races`: if no configuration of the orbit of `astep` from the start is a lost race, the machine
  never halts from blank tape.

In the accelerated run every one of the 108 anomalies of 300 transients finds all gaps aligned.  The converse does
not hold for the map as it stands: a lost race can halt (`qc_short_halts` in `Transients.lean`) or go on (in
simulation many do), and after one the counter can hold several misaligned gaps, which the head then works through
in a computation of its own; so this machine has no "halts if and only if the map gets stuck" statement of the
kind proved for 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD, only this one direction.
-/

namespace H67116

open TM

/-! ## Words and gaps -/

/-- A valid word (last block first): the first block (the last of the list) even and at least 2, the others odd. -/
def goodW : List Nat → Prop
  | [] => False
  | [x] => x % 2 = 0 ∧ 2 ≤ x
  | b :: x :: W => b % 2 = 1 ∧ goodW (x :: W)

/-- A gap of length `3p + 2`. -/
def al (g : Nat) : Bool := g % 3 == 2

/-- The number of misaligned gaps. -/
def nmis : List Nat → Nat
  | [] => 0
  | g :: G => (if al g then 0 else 1) + nmis G

/-- The invariant. -/
def Inv (c : AC) : Prop := goodW c.W ∧ 1 ≤ c.a ∧ nmis c.G ≤ 1

/-- The word has run out: one block, or one block and a single 1. -/
def ended : List Nat → Bool
  | [_] => true
  | [1, _] => true
  | _ => false

/-- A lost race: the word has run out while a misaligned gap is pending. -/
def lost (c : AC) : Prop := ended c.W = true ∧ 1 ≤ nmis c.G

theorem nmis_twos (t : Nat) (R : List Nat) : nmis (List.replicate t 2 ++ R) = nmis R := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [List.replicate_succ, List.cons_append, nmis, ih]; simp [al]

theorem nmis_lead2 (G : List Nat) : nmis G = nmis (lead2 G).2 := by
  conv => lhs; rw [lead2_spec G]
  exact nmis_twos _ _

theorem goodW_cons_odd {b : Nat} {W : List Nat} (hb : b % 2 = 1) (hW : goodW W) : goodW (b :: W) := by
  match W, hW with
  | x :: W', hW => exact ⟨hb, hW⟩

theorem goodW_append {C W : List Nat} (hC : ∀ b ∈ C, b % 2 = 1) (hW : goodW W) : goodW (C ++ W) := by
  induction C with
  | nil => exact hW
  | cons b C ih =>
    exact goodW_cons_odd (hC b (List.mem_cons_self ..)) (ih fun x hx => hC x (List.mem_cons_of_mem _ hx))

theorem ones_odd (n : Nat) : ∀ b ∈ List.replicate n 1, b % 2 = 1 := by
  intro b hb; rw [List.eq_of_mem_replicate hb]

theorem goodW_tail {b : Nat} {W : List Nat} (h : goodW (b :: W)) (hW : W ≠ []) : goodW W := by
  match W, h with
  | x :: W', h => exact h.2

theorem goodW_head2 {b x : Nat} {W : List Nat} (h : goodW (b :: x :: W)) : b % 2 = 1 := h.1

/-- The second block keeps its parity under `+ 2`. -/
theorem goodW_add2 {x : Nat} {W : List Nat} (h : goodW (x :: W)) : goodW ((x + 2) :: W) := by
  match W, h with
  | [], h => exact ⟨by have := h.1; omega, by omega⟩
  | y :: W', h => exact ⟨by have := h.1; omega, h.2⟩

theorem goodW_phi {W : List Nat} (h : goodW W) : goodW (phi W) := by
  match W, h with
  | [x], h => exact h
  | b :: x :: W', h =>
    simp only [phi]
    exact goodW_append (ones_odd _) (goodW_add2 h.2)

theorem goodW_bump {W : List Nat} (h : goodW W) : goodW (bump W) := by
  match W, h with
  | b :: W', h => exact goodW_add2 h

theorem goodW_fresh {x : Nat} (_hx : x % 2 = 0 ∧ 2 ≤ x) : goodW (fresh x) :=
  goodW_append (ones_odd _) ⟨by decide, Nat.le_refl 2⟩

theorem ne_nil_of_goodW {W : List Nat} (h : goodW W) : W ≠ [] := by
  intro e; subst e; exact h

/-- A valid word of at least two blocks other than `[1, x]` has one of the shapes of the regular step. -/
theorem wshape_of_goodW {W : List Nat} (h : goodW W) (h1 : ∀ x, W ≠ [x]) (h2 : ∀ x, W ≠ [1, x]) :
    wshape W = true := by
  match W, h with
  | [x], _ => exact absurd rfl (h1 x)
  | b :: x :: V, h =>
    have hb := h.1
    simp only [wshape, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    by_cases hb1 : b = 1
    · subst hb1
      cases V with
      | nil => exact absurd rfl (h2 x)
      | cons y V' =>
        right
        refine ⟨⟨rfl, ?_⟩, ?_⟩
        · exact h.2.1
        · simp
    · left; exact ⟨hb, by omega⟩

/-! ## The collision table -/

theorem coll_some (s p g U : Nat) (hp : p < 2) (hg : g ≤ 1) : (coll s p g U).isSome = true := by
  match p, g, U with
  | 0, 0, 0 | 0, 0, 1 | 0, 0, 2 | 0, 0, _ + 3 | 0, 1, 0 | 0, 1, 1 | 0, 1, _ + 2
  | 1, 0, 0 | 1, 0, 1 | 1, 0, _ + 2 | 1, 1, 0 | 1, 1, 1 | 1, 1, _ + 2 => rfl

theorem coll_spec {s p g U : Nat} {C : List Nat} {a' d : Nat} (h : coll s p g U = some (C, a', d)) :
    1 ≤ a' ∧ ∀ b ∈ C, b % 2 = 1 := by
  unfold coll at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h <;>
    refine ⟨by omega, ?_⟩ <;> intro b hb <;>
    simp only [List.mem_cons, List.mem_replicate] at hb <;> omega

/-! ## The invariant is kept -/

theorem al_false {g : Nat} (h : al g = false) : g % 3 ≠ 2 := by
  simp only [al, beq_eq_false_iff_ne] at h; exact h

theorem al_true {g : Nat} (h : al g = true) : g % 3 = 2 := by
  simp only [al, beq_iff_eq] at h; exact h

theorem nmis_cons_le {g : Nat} {G : List Nat} (h : nmis (g :: G) ≤ 1) : nmis G ≤ 1 := by
  simp [nmis] at h; omega

theorem nmis_cons_mis {g : Nat} {G : List Nat} (h : nmis (g :: G) ≤ 1) (hg : al g = false) : nmis G = 0 := by
  simp [nmis, hg] at h; omega

theorem nmis_zero_head {g : Nat} {G : List Nat} (h : nmis (g :: G) = 0) : al g = true ∧ nmis G = 0 := by
  simp only [nmis] at h
  cases e : al g
  · simp [e] at h
  · simp [e] at h; exact ⟨rfl, h⟩

/-- An aligned gap of at least 3 loses 3 and stays aligned; a misaligned one stays misaligned. -/
theorem al_sub3 {h : Nat} (h3 : 3 ≤ h) : al (h - 3) = al h := by
  simp only [al]
  have : (h - 3) % 3 = h % 3 := by omega
  rw [this]

theorem nmis_sub3 {h : Nat} {G : List Nat} (h3 : 3 ≤ h) : nmis ((h - 3) :: G) = nmis (h :: G) := by
  simp only [nmis, al_sub3 h3]

theorem al_32 (a : Nat) : al (3 * a + 2) = true := by
  have : (3 * a + 2) % 3 = 2 := by omega
  simp [al, this]

/-- **The invariant is kept** wherever the race is not lost. -/
theorem inv_step (c : AC) (hI : Inv c) (hl : ¬ lost c) : ∃ c', astep c = some c' ∧ Inv c' := by
  obtain ⟨W, a, G⟩ := c
  obtain ⟨hW, ha, hG⟩ := hI
  simp only at hW ha hG
  simp only [lost, not_and, Nat.not_le] at hl
  unfold astep
  split
  · -- one block: the anomaly; all gaps aligned
    rename_i x hWx
    simp only at hWx; subst hWx
    have h0 : nmis G = 0 := by have := hl rfl; omega
    have hx : x % 2 = 0 ∧ 2 ≤ x := hW
    rw [if_pos ⟨hx.1, hx.2, ha⟩]
    refine ⟨⟨fresh x, 1, (3 * (a - 1)) :: G⟩, rfl, goodW_fresh hx, Nat.le_refl 1, ?_⟩
    show nmis ((3 * (a - 1)) :: G) ≤ 1
    simp only [nmis, h0]; split <;> omega
  · -- a block and a single 1
    rename_i x hWx
    simp only at hWx; subst hWx
    have h0 : nmis G = 0 := by have := hl rfl; omega
    have hx : x % 2 = 0 ∧ 2 ≤ x := hW.2
    rw [if_pos hx]
    have g3 : goodW (3 :: fresh x) := goodW_cons_odd (by decide) (goodW_fresh hx)
    have g5 : goodW (5 :: fresh x) := goodW_cons_odd (by decide) (goodW_fresh hx)
    by_cases h2 : 2 ≤ a
    · rw [if_pos h2]
      refine ⟨⟨3 :: fresh x, 1, (3 * (a - 2) + 1) :: G⟩, rfl, g3, Nat.le_refl 1, ?_⟩
      show nmis ((3 * (a - 2) + 1) :: G) ≤ 1
      simp only [nmis, h0]; split <;> omega
    · rw [if_neg h2, if_pos (by omega : a = 1)]
      have hs := nmis_lead2 G
      rw [h0] at hs
      split
      · exact ⟨⟨5 :: fresh x, 1, []⟩, rfl, g5, Nat.le_refl 1, Nat.zero_le 1⟩
      · rename_i h' G' e
        have e2 := congrArg Prod.snd e
        simp only at e2
        rw [e2] at hs
        obtain ⟨hal, hG'⟩ := nmis_zero_head hs.symm
        have hne := lead2_head G h' G' e2
        have h5 : 3 ≤ h' := by have := al_true hal; omega
        rw [if_pos h5]
        refine ⟨⟨5 :: fresh x, 1, (h' - 3) :: G'⟩, rfl, g5, Nat.le_refl 1, ?_⟩
        show nmis ((h' - 3) :: G') ≤ 1
        rw [nmis_sub3 h5]; simp [nmis, hal, hG']
      · rename_i t e
        exact ⟨⟨5 :: fresh x, t + 2, []⟩, rfl, g5, Nat.succ_le_succ (Nat.zero_le _), Nat.zero_le 1⟩
      · rename_i t h' G' e
        have e2 := congrArg Prod.snd e
        simp only at e2
        rw [e2] at hs
        obtain ⟨hal, hG'⟩ := nmis_zero_head hs.symm
        have hne := lead2_head G h' G' e2
        have h5 : 3 ≤ h' := by have := al_true hal; omega
        rw [if_pos h5]
        refine ⟨⟨5 :: fresh x, t + 2, (h' - 3) :: G'⟩, rfl, g5, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
        show nmis ((h' - 3) :: G') ≤ 1
        rw [nmis_sub3 h5]; simp [nmis, hal, hG']
  · -- the regular shapes
    rename_i hne1 hne2
    have hw := wshape_of_goodW hW (fun x e => hne1 x e) (fun x e => hne2 x e)
    rw [if_pos hw]
    have gp := goodW_phi (goodW_phi hW)
    by_cases h2 : 2 ≤ a
    · rw [if_pos h2]
      refine ⟨⟨phi (phi W), 1, (3 * (a - 2) + 2) :: G⟩, rfl, gp, Nat.le_refl 1, ?_⟩
      show nmis ((3 * (a - 2) + 2) :: G) ≤ 1
      simp [nmis, al_32 (a - 2)]; omega
    · rw [if_neg h2, if_pos (by omega : a = 1)]
      have hs := nmis_lead2 G
      split
      · rename_i t e
        exact ⟨⟨phi (phi W), t + 2, []⟩, rfl, gp, Nat.succ_le_succ (Nat.zero_le _), Nat.zero_le 1⟩
      · rename_i t h' G0 e
        have e2 := congrArg Prod.snd e
        simp only at e2
        rw [e2] at hs
        have hne := lead2_head G h' G0 e2
        have hG1 : nmis (h' :: G0) ≤ 1 := by omega
        by_cases h3 : 3 ≤ h'
        · rw [if_pos h3]
          refine ⟨⟨phi (phi W), t + 2, (h' - 3) :: G0⟩, rfl, gp, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
          show nmis ((h' - 3) :: G0) ≤ 1
          rw [nmis_sub3 h3]; exact hG1
        · rw [if_neg h3, if_pos (by omega : h' ≤ 1)]
          have hmis : al h' = false := by
            cases e3 : al h'
            · rfl
            · have := al_true e3; omega
          have h00 := nmis_cons_mis hG1 hmis
          have hs0 := nmis_lead2 G0
          rw [h00] at hs0
          have hsome := coll_some (t / 2) (t % 2) h' (lead2 G0).1 (Nat.mod_lt _ (by decide)) (by omega)
          cases ec : coll (t / 2) (t % 2) h' (lead2 G0).1 with
          | none => rw [ec] at hsome; cases hsome
          | some r =>
            obtain ⟨C, a', d⟩ := r
            obtain ⟨ha', hC⟩ := coll_spec ec
            have gw : goodW (C ++ bump (phi (phi W))) := goodW_append hC (goodW_bump gp)
            cases e2 : (lead2 G0).2 with
            | nil => exact ⟨⟨C ++ bump (phi (phi W)), a', []⟩, by simp only [], gw, ha', Nat.zero_le 1⟩
            | cons h2' G' =>
              rw [e2] at hs0
              obtain ⟨hal, hG'⟩ := nmis_zero_head hs0.symm
              have hne' := lead2_head G0 h2' G' e2
              have h5 : 5 ≤ h2' := by have := al_true hal; omega
              refine ⟨⟨C ++ bump (phi (phi W)), a', (h2' - 5 + d) :: G'⟩, by simp only []; rw [if_pos h5], gw,
                ha', ?_⟩
              show nmis ((h2' - 5 + d) :: G') ≤ 1
              simp only [nmis, hG']; split <;> omega

/-! ## Non-halting reduced to the races -/

theorem inv_start : Inv start := ⟨⟨rfl, rfl, Nat.le_refl 2⟩, Nat.le_refl 1, Nat.zero_le 1⟩

/-- Along an orbit with no lost race, `astep` is defined at every step and the invariant holds. -/
theorem arun_of_races (c : AC) (hI : Inv c) :
    ∀ k, (∀ j c', j < k → arun j c = some c' → ¬ lost c') → ∃ c', arun k c = some c' ∧ Inv c' := by
  intro k
  induction k generalizing c with
  | zero => intro _; exact ⟨c, rfl, hI⟩
  | succ k ih =>
    intro hno
    obtain ⟨c1, e1, hI1⟩ := inv_step c hI (hno 0 c (by omega) rfl)
    have hno' : ∀ j c', j < k → arun j c1 = some c' → ¬ lost c' := by
      intro j c' hj hr
      exact hno (j + 1) c' (by omega) (by simp only [arun, e1, Option.bind_some]; exact hr)
    obtain ⟨c', e', hI'⟩ := ih c1 hI1 hno'
    exact ⟨c', by simp only [arun, e1, Option.bind_some]; exact e', hI'⟩

/-- **Halting needs a lost race**: if no configuration on the orbit of the macro map from the first Q
configuration (step 27) is a lost race, the machine never halts from blank tape. -/
theorem not_halts_of_races (h : ∀ k c, arun k start = some c → ¬ lost c) : ¬ HaltsFromBlank := by
  apply not_halts_of_arun
  intro k
  obtain ⟨c, e, _⟩ := arun_of_races start inv_start k (fun j c' _ hr => h j c' hr)
  rw [e]; rfl

end H67116
