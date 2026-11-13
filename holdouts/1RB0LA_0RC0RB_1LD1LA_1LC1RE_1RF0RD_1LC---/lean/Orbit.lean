import Ctx
import Blank

/-!
# The run from blank tape follows the E-pass map

`nextE c n` is the next E-event after `Ev c n` according to the proved table (`Ctx.lean`): with `b = ⌈n/2⌉ mod 2`
the context becomes the table's `c'` for that bit and the block

    n ≡ 0 (mod 4):  6⌊n/4⌋ + 2 + a₀      n ≡ 3:  6⌊n/4⌋ + 8 + a₀      (b = 0)
    n ≡ 1, 2:       6⌊n/4⌋ + 5 + a₁                                  (b = 1)

that is n' = (3n + δ)/2.  `nextE_sound`: the machine really goes from `Ev c n` to that event, for every `n ≥ 6` and
every context of the table (`pass0`..`pass3` of `Pass.lean` for the block, which hold for every context, then the
context's own rewrite).  `blank_reaches_E`: from blank tape the machine reaches `Ev [1] 19` after 153 steps.  So the
run is the orbit of `([1], 19)` under `nextE` for as long as that stays inside the table (`oiter_sound`);
`orbit_kernel` and `orbit_native` check it for 10,000 and 2^18 (262,144) passes, which gives runs without a halt
of more than 10^1700 and 10^45000 steps (`no_halt_kernel`, `no_halt_native`).  `halts_of_orbit`: reaching the
context `11111` or `1111011` with ⌈n/2⌉ odd makes the machine halt; `not_halts_of_forall`: staying in the table
forever makes it run forever.  (2^22 passes by `native_decide` also check, in 29 minutes; c/orbit.c runs 2^32.)
-/

namespace H121010

open TM

/-! ## The table lookup -/

def look (c : List Bool) : Option (Option (List Bool × Nat) × Option (List Bool × Nat)) :=
  (tbl.find? (fun e => e.1 == c)).map (·.2)

theorem look_sound {c : List Bool} {x : Option (List Bool × Nat) × Option (List Bool × Nat)}
    (h : look c = some x) : EntryOK (c, x) := by
  unfold look at h
  cases hf : tbl.find? (fun e => e.1 == c) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hc := List.find?_some hf
    have ok := tbl_sound e hm
    have hc' : e.1 = c := by simpa using hc
    obtain ⟨e1, e2⟩ := e
    simp only at h hc'
    subst h hc'
    exact ok

/-! ## One pass, for each residue of n mod 4 -/

theorem step0 (c c' : List Bool) (a i : Nat)
    (ok : ∀ j, Reaches (Cn (app c.reverse blank) (2 * j + 2)) (Ev c' (2 * j + 2 + a)) 0) :
    Reaches (Ev c (4 * i + 4)) (Ev c' (6 * i + 8 + a)) (4 * i + 4) := by
  have h₁ := pass0 (app c.reverse blank) i
  have h₂ := ok (3 * i + 3)
  rw [show 2 * (3 * i + 3) + 2 = 6 * i + 8 by omega] at h₂
  have h := h₁.trans' h₂
  rw [Nat.add_zero] at h
  exact h

theorem step3 (c c' : List Bool) (a i : Nat)
    (ok : ∀ j, Reaches (Cn (app c.reverse blank) (2 * j + 2)) (Ev c' (2 * j + 2 + a)) 0) :
    Reaches (Ev c (4 * i + 3)) (Ev c' (6 * i + 8 + a)) (4 * i + 3) := by
  have h₁ := pass3 (app c.reverse blank) i
  have h₂ := ok (3 * i + 3)
  rw [show 2 * (3 * i + 3) + 2 = 6 * i + 8 by omega] at h₂
  have h := h₁.trans' h₂
  rw [Nat.add_zero] at h
  exact h

theorem step1 (c c' : List Bool) (a i : Nat)
    (ok : ∀ j, Reaches (Cn (cons true (app c.reverse blank)) (2 * j + 5)) (Ev c' (2 * j + 5 + a)) 0) :
    Reaches (Ev c (4 * i + 5)) (Ev c' (6 * i + 11 + a)) (4 * i + 5) := by
  have h₁ := pass1 (app c.reverse blank) i
  have h₂ := ok (3 * i + 3)
  rw [show 2 * (3 * i + 3) + 5 = 6 * i + 11 by omega] at h₂
  have h := h₁.trans' h₂
  rw [Nat.add_zero] at h
  exact h

theorem step2 (c c' : List Bool) (a i : Nat)
    (ok : ∀ j, Reaches (Cn (cons true (app c.reverse blank)) (2 * j + 5)) (Ev c' (2 * j + 5 + a)) 0) :
    Reaches (Ev c (4 * i + 2)) (Ev c' (6 * i + 5 + a)) (4 * i + 2) := by
  have h₁ := pass2 (app c.reverse blank) i
  have h₂ := ok (3 * i)
  rw [show 2 * (3 * i) + 5 = 6 * i + 5 by omega] at h₂
  have h := h₁.trans' h₂
  rw [Nat.add_zero] at h
  exact h

/-! ## The map -/

/-- The next E-event after `Ev c n` by the table, or `none` (a halting rule, a context outside the table, or n < 6). -/
def nextE (c : List Bool) (n : Nat) : Option (List Bool × Nat) :=
  match look c with
  | none => none
  | some (e0, e1) =>
    if n < 6 then none
    else if n % 4 = 0 then e0.map (fun x => (x.1, 6 * (n / 4) + 2 + x.2))
    else if n % 4 = 3 then e0.map (fun x => (x.1, 6 * (n / 4) + 8 + x.2))
    else e1.map (fun x => (x.1, 6 * (n / 4) + 5 + x.2))

theorem nextE_sound {c : List Bool} {n : Nat} {y : List Bool × Nat} (h : nextE c n = some y) :
    Reaches (Ev c n) (Ev y.1 y.2) n := by
  unfold nextE at h
  cases hl : look c with
  | none => rw [hl] at h; cases h
  | some x =>
    rw [hl] at h
    obtain ⟨e0, e1⟩ := x
    obtain ⟨ok0, ok1⟩ := look_sound hl
    simp only at ok0 ok1 h
    by_cases h6 : n < 6
    · simp only [h6, ↓reduceIte] at h; cases h
    simp only [h6, ↓reduceIte] at h
    by_cases h0 : n % 4 = 0
    · simp only [h0, ↓reduceIte] at h
      cases he : e0 with
      | none => rw [he] at h; cases h
      | some p =>
        rw [he] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨i, rfl⟩ : ∃ i, n = 4 * i + 4 := ⟨n / 4 - 1, by omega⟩
        have r := step0 c p.1 p.2 i (ok0 p.1 p.2 he)
        rw [show 6 * ((4 * i + 4) / 4) + 2 + p.2 = 6 * i + 8 + p.2 by omega]
        exact r
    simp only [h0, ↓reduceIte] at h
    by_cases h3 : n % 4 = 3
    · simp only [h3, ↓reduceIte] at h
      cases he : e0 with
      | none => rw [he] at h; cases h
      | some p =>
        rw [he] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨i, rfl⟩ : ∃ i, n = 4 * i + 3 := ⟨n / 4, by omega⟩
        have r := step3 c p.1 p.2 i (ok0 p.1 p.2 he)
        rw [show 6 * ((4 * i + 3) / 4) + 8 + p.2 = 6 * i + 8 + p.2 by omega]
        exact r
    simp only [h3, ↓reduceIte] at h
    cases he : e1 with
    | none => rw [he] at h; cases h
    | some p =>
      rw [he] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      by_cases h1 : n % 4 = 1
      · obtain ⟨i, rfl⟩ : ∃ i, n = 4 * i + 5 := ⟨n / 4 - 1, by omega⟩
        have r := step1 c p.1 p.2 i (ok1 p.1 p.2 he)
        rw [show 6 * ((4 * i + 5) / 4) + 5 + p.2 = 6 * i + 11 + p.2 by omega]
        exact r
      · obtain ⟨i, rfl⟩ : ∃ i, n = 4 * i + 2 := ⟨n / 4, by omega⟩
        have r := step2 c p.1 p.2 i (ok1 p.1 p.2 he)
        rw [show 6 * ((4 * i + 2) / 4) + 5 + p.2 = 6 * i + 5 + p.2 by omega]
        exact r

/-! ## From blank tape -/

/-- Drop trailing `false`s. -/
def strip : List Bool → List Bool
  | [] => []
  | b :: l => if strip l = [] ∧ b = false then [] else b :: strip l

theorem app_strip (l : List Bool) : app (strip l) blank = app l blank := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : strip l = [] ∧ b = false
    · rw [strip, ite_eq_left_of_eq_true _ _ (eq_true h)]
      obtain ⟨h1, rfl⟩ := h
      rw [app_cons, ← ih, h1]
      exact cons_false_blank.symm
    · rw [strip, ite_eq_right_of_eq_false _ _ (eq_false h), app_cons, app_cons, ih]

theorem app_ones (n : Nat) : app (List.replicate n true) blank = ones n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, app_cons, ih]; rfl

/-- After 153 steps from blank tape: `1 E> 1^19`, the first E-event. -/
theorem blank_reaches_E : steps 153 init = some (Ev [true] 19) := by
  have h : (TM.fsteps trans 153 (FCfg.blank St.A)).map (fun c => (strip c.l, strip c.r, c.st)) =
      some ([true], List.replicate 19 true, St.E) := by decide +kernel
  cases e : TM.fsteps trans 153 (FCfg.blank St.A) with
  | none => rw [e] at h; cases h
  | some c =>
    rw [e] at h
    obtain ⟨l, r, q⟩ := c
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hl, hr, rfl⟩ := h
    have h2 := blank_reaches trans e
    show TM.steps trans 153 (blankCfg St.A) = _
    rw [h2]
    simp only [FCfg.toCfg, Ev, EvT]
    rw [← app_strip l, ← app_strip r, hl, hr, app_ones]
    rfl

/-! ## The orbit -/

/-- `K` passes on (context, block, steps so far). -/
def oiter : Nat → List Bool × Nat × Nat → Option (List Bool × Nat × Nat)
  | 0, x => some x
  | K + 1, x =>
    match nextE x.1 x.2.1 with
    | none => none
    | some y => oiter K (y.1, y.2, x.2.2 + x.2.1)

theorem oiter_sound : ∀ (K : Nat) (x y : List Bool × Nat × Nat), oiter K x = some y →
    Reaches init (Ev x.1 x.2.1) x.2.2 → Reaches init (Ev y.1 y.2.1) y.2.2 := by
  intro K
  induction K with
  | zero => intro x y h r; simp only [oiter, Option.some.injEq] at h; subst h; exact r
  | succ K ih =>
    intro x y h r
    simp only [oiter] at h
    cases hn : nextE x.1 x.2.1 with
    | none => rw [hn] at h; cases h
    | some z =>
      rw [hn] at h
      exact ih _ y h (r.trans' (nextE_sound hn))

theorem nextE_ge {c : List Bool} {n : Nat} {y : List Bool × Nat} (h : nextE c n = some y) : 6 ≤ n := by
  unfold nextE at h
  cases hl : look c with
  | none => rw [hl] at h; cases h
  | some x =>
    rw [hl] at h
    obtain ⟨e0, e1⟩ := x
    simp only at h
    by_cases h6 : n < 6
    · simp only [h6, ↓reduceIte] at h; cases h
    · omega

theorem oiter_steps_ge : ∀ (K : Nat) (x y : List Bool × Nat × Nat), oiter K x = some y → x.2.2 + K ≤ y.2.2 := by
  intro K
  induction K with
  | zero => intro x y h; simp only [oiter, Option.some.injEq] at h; subst h; omega
  | succ K ih =>
    intro x y h
    simp only [oiter] at h
    cases hn : nextE x.1 x.2.1 with
    | none => rw [hn] at h; cases h
    | some z =>
      rw [hn] at h
      have := ih _ y h
      have := nextE_ge hn
      simp only at *
      omega

/-- The first E-event, at step 153. -/
def x0 : List Bool × Nat × Nat := ([true], 19, 153)

theorem x0_reaches : Reaches init (Ev x0.1 x0.2.1) x0.2.2 := ⟨153, Nat.le_refl _, blank_reaches_E⟩

/-- The state after `K` passes (or `x0` if the orbit left the table). -/
def after (K : Nat) : List Bool × Nat × Nat := (oiter K x0).getD x0

theorem no_halt_of {K : Nat} (h : (oiter K x0).isSome = true) : ∃ c, steps (after K).2.2 init = some c := by
  cases e : oiter K x0 with
  | none => rw [e] at h; cases h
  | some y =>
    have r := oiter_sound K x0 y e x0_reaches
    obtain ⟨t, ht, s⟩ := r
    have s' : steps (y.2.2 + (t - y.2.2)) init = some (Ev y.1 y.2.1) := by
      rw [show y.2.2 + (t - y.2.2) = t by omega]; exact s
    simp only [after, e, Option.getD_some]
    exact steps_le trans s'

theorem orbit_kernel : (oiter 10000 x0).isSome = true := by decide +kernel

/-- No halt in the first `(after 10000).2.2` steps, by the kernel. -/
theorem no_halt_kernel : ∃ c, steps (after 10000).2.2 init = some c := no_halt_of orbit_kernel

theorem kernel_bound : 10 ^ 1700 < (after 10000).2.2 := by decide +kernel

theorem orbit_native : (oiter (2 ^ 18) x0).isSome = true := by native_decide

/-- No halt in the first `(after 2^22).2.2` steps (more than 45,000 digits), with `native_decide`. -/
theorem no_halt_native : ∃ c, steps (after (2 ^ 18)).2.2 init = some c := no_halt_of orbit_native

theorem native_bound : 10 ^ 45000 < (after (2 ^ 18)).2.2 := by native_decide

/-! ## The halting rules -/

theorem halts_of_reaches {a b : Config} {N : Nat} (r : Reaches a b N) (h : Halts trans b) : Halts trans a := by
  obtain ⟨t, _, s⟩ := r
  obtain ⟨n, c, s', hc⟩ := h
  exact ⟨t + n, c, steps_seq trans s s', hc⟩

/-- An E-event with a context that halts on b = 1 (`ok`: the context's rewrite halts for every odd block of at
least 5), and ⌈n/2⌉ odd, halts. -/
theorem halts_b1 (c : List Bool) (n : Nat) (hn : n % 4 = 1 ∨ n % 4 = 2) (h6 : 6 ≤ n)
    (ok : ∀ j, Halts trans (Cn (cons true (app c.reverse blank)) (2 * j + 5))) : Halts trans (Ev c n) := by
  rcases hn with h1 | h2
  · obtain ⟨i, rfl⟩ : ∃ i, n = 4 * i + 5 := ⟨n / 4 - 1, by omega⟩
    have r := pass1 (app c.reverse blank) i
    have k := ok (3 * i + 3)
    rw [show 2 * (3 * i + 3) + 5 = 6 * i + 11 by omega] at k
    exact halts_of_reaches r k
  · obtain ⟨i, rfl⟩ : ∃ i, n = 4 * i + 2 := ⟨n / 4, by omega⟩
    have r := pass2 (app c.reverse blank) i
    have k := ok (3 * i)
    rw [show 2 * (3 * i) + 5 = 6 * i + 5 by omega] at k
    exact halts_of_reaches r k

/-- **The halting criterion**: if the orbit reaches the context `11111` or `1111011` with ⌈n/2⌉ odd, the machine
halts from blank tape.  (These two rules carry all but 10⁻¹⁶ of the halting rate of the Markov model.) -/
theorem halts_of_orbit (K : Nat) (y : List Bool × Nat × Nat) (h : oiter K x0 = some y)
    (hc : y.1 = [true, true, true, true, true] ∨ y.1 = [true, true, true, true, false, true, true])
    (hn : y.2.1 % 4 = 1 ∨ y.2.1 % 4 = 2) (h6 : 6 ≤ y.2.1) : HaltsFromBlank := by
  have r := oiter_sound K x0 y h x0_reaches
  apply halts_of_reaches r
  rcases hc with e | e
  · rw [e]; exact halts_b1 _ _ hn h6 halt_11111_1
  · rw [e]; exact halts_b1 _ _ hn h6 halt_1111011_1

/-- If the orbit stays inside the table forever, the machine never halts from blank tape. -/
theorem not_halts_of_forall (h : ∀ K, (oiter K x0).isSome = true) : ¬ HaltsFromBlank := by
  apply TM.not_halts_of_forall trans
  intro t
  have hK := h t
  cases e : oiter t x0 with
  | none => rw [e] at hK; cases hK
  | some y =>
    obtain ⟨u, hu, s⟩ := oiter_sound t x0 y e x0_reaches
    have ge := oiter_steps_ge t x0 y e
    have s' : steps (t + (u - t)) init = some (Ev y.1 y.2.1) := by
      rw [show t + (u - t) = u by simp [x0] at ge; omega]; exact s
    exact steps_le trans s'

end H121010
