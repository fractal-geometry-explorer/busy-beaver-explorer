import VisitPow

/-! # 1011 and 111 are met only at the right end, for 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---

A round is one visit to the stream `X = 1 0 S` (`Visit.lean`). Its nested visits form a *cascade*: the visit at
offset 0 handles a block of 3 or 4 cells and passes its nested visits on to the block that follows, that block
passes its own on, and so on, until a block receives visits but passes none on. That block's offset is where the
cascade *stops*.

`Blk n w w' m`: `n` visits to a block `w` (3 or 4 cells, read in place) rewrite it to `w'` and send `m` visits
to the stream after it. `Casc n s s' f E`: `n` visits to `s` rewrite it to `s'`, the cascade stops at offset `f`,
and `E` lists the offsets where a visit met `1011`. `CascH n s p`: one of the `n` visits halts, at offset `p`,
on `111`. The relations are sound for the machine (`Casc.vis`, `CascH.vis`, from the theorems of `Visit.lean`) and
cover every eventually blank stream (`total`).

`Clean b s`: no two adjacent 1s at offsets `i, i+1` with `i < b`. A block that passes visits on is always left as
`000`, `100` or `1010` (`Blk.out`), so a cascade leaves its stream clean up to the offset where it stopped
(`Casc.clean`). A visit meets `1011` or `111` only on two adjacent 1s, so in the next round both can happen only
at offsets `p` with `F ≤ p + 2`, where `F` is where the previous round's cascade stopped (`right_end_1011`,
`right_end_halt`). `Reach r S F` is the run in this model: after `r` rounds the machine is at `0^∞ A> 1 0 S`
and round `r` stopped at offset `F` of `1 0 S` (`reach_steps`). The machine halts from blank tape exactly when
some round's cascade halts (`halts_iff`), and then at `p ≥ F - 2` (`halts_iff_right_end`).

Kernel only (no `native_decide`). -/

namespace H173741

open TM

/-! ## Counting visits -/

/-- Some visit among the first `n` visits to `s` halts. -/
def VisNH (n : Nat) (s : Tape) : Prop := ∃ j u, j < n ∧ VisN j s u ∧ VisHalts u

theorem visN_split : ∀ (a : Nat) {b : Nat} {s u : Tape}, VisN (a + b) s u → ∃ t, VisN a s t ∧ VisN b t u
  | 0, b, s, u, h => ⟨s, rfl, by simpa using h⟩
  | a + 1, b, s, u, h => by
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e] at h
    obtain ⟨t1, h1, h2⟩ := h
    obtain ⟨t, ht, hr⟩ := visN_split a h2
    exact ⟨t, ⟨t1, h1, ht⟩, hr⟩

theorem visN_snoc {a : Nat} {s u : Tape} (h : VisN (a + 1) s u) : ∃ t, VisN a s t ∧ Vis t u := by
  obtain ⟨t, h1, h2⟩ := visN_split a h
  obtain ⟨u', hv, hr⟩ := h2
  cases hr
  exact ⟨t, h1, hv⟩

theorem visN_one_inv {s u : Tape} (h : VisN 1 s u) : Vis s u := by
  obtain ⟨t, hv, he⟩ := h
  cases he
  exact hv

theorem visN_add' {a b : Nat} {s t u : Tape} (h1 : VisN a s t) (h2 : VisN b t u) : VisN (a + b) s u := by
  rw [Nat.add_comm]; exact visN_add h1 h2

theorem visNH_mono {a b : Nat} {s : Tape} (h : VisNH a s) (hab : a ≤ b) : VisNH b s := by
  obtain ⟨j, u, hj, h1, h2⟩ := h
  exact ⟨j, u, by omega, h1, h2⟩

theorem visNH_cons {n : Nat} {s t : Tape} (hv : Vis s t) (h : VisNH n t) : VisNH (n + 1) s := by
  obtain ⟨j, u, hj, h1, h2⟩ := h
  exact ⟨j + 1, u, by omega, ⟨t, hv, h1⟩, h2⟩

/-! ## The blocks: closed forms for `n` visits -/

theorem l100 : ∀ (j : Nat) {t u : Tape}, VisN j t u →
    VisN (2 * j) (app [true, false, false] t) (app [true, false, false] u)
  | 0, t, u, h => by cases h; rfl
  | j + 1, t, u, h => by
    obtain ⟨t1, h1, h2⟩ := h
    have e : 2 * (j + 1) = 2 + 2 * j := by omega
    rw [e]
    exact visN_add' ⟨_, vis_100 h1, _, vis_0, rfl⟩ (l100 j h2)

theorem b000_odd {j : Nat} {t u : Tape} (h : VisN j t u) :
    VisN (2 * j + 1) (app [false, false, false] t) (app [true, false, false] u) :=
  ⟨_, vis_0, l100 j h⟩

theorem b000_even {j : Nat} {t u : Tape} (h : VisN j t u) :
    VisN (2 * j) (app [false, false, false] t) (app [false, false, false] u) := by
  cases j with
  | zero => cases h; rfl
  | succ j =>
    obtain ⟨x, h1, h2⟩ := visN_snoc h
    have e : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    rw [e]
    exact visN_add' (b000_odd h1) (visN_one (vis_100 h2))

theorem b100_odd {k : Nat} {t u : Tape} (h : VisN (k + 1) t u) :
    VisN (2 * k + 1) (app [true, false, false] t) (app [false, false, false] u) := by
  obtain ⟨x, h1, h2⟩ := visN_snoc h
  exact visN_add' (l100 k h1) (visN_one (vis_100 h2))

theorem b110_0 {j : Nat} {t u : Tape} (h : VisN (j + 1) t u) :
    VisN (2 * j + 1) (app [true, true, false] t) (app [false, false, false] u) := by
  obtain ⟨t1, h1, h2⟩ := h
  exact ⟨_, vis_110 h1, b000_even h2⟩

theorem b110_1 {j : Nat} {t u : Tape} (h : VisN (j + 1) t u) :
    VisN (2 * j + 2) (app [true, true, false] t) (app [true, false, false] u) := by
  obtain ⟨t1, h1, h2⟩ := h
  exact ⟨_, vis_110 h1, b000_odd h2⟩

/-! ## Blocks -/

/-- `n` visits to the block `w` (followed by any stream) rewrite it to `w'` and send `m` visits on to the stream
after it. The cases are every block a cascade can meet, other than `1011`, `0011`, `011` and `111`. -/
inductive Blk : Nat → List Bool → List Bool → Nat → Prop
  | z0 (k : Nat) : Blk (2 * k + 1) [false, false, false] [true, false, false] k
  | z1 (k : Nat) : Blk (2 * k + 2) [false, false, false] [false, false, false] (k + 1)
  | o0 (k : Nat) : Blk (2 * k + 1) [true, false, false] [false, false, false] (k + 1)
  | o1 (k : Nat) : Blk (2 * k + 2) [true, false, false] [true, false, false] (k + 1)
  | t0 (k : Nat) : Blk (2 * k + 1) [true, true, false] [false, false, false] (k + 1)
  | t1 (k : Nat) : Blk (2 * k + 2) [true, true, false] [true, false, false] (k + 1)
  | w1 : Blk 1 [false, true, false] [true, true, false] 0
  | w0 (k : Nat) : Blk (2 * k + 2) [false, true, false] [false, false, false] (k + 1)
  | w2 (k : Nat) : Blk (2 * k + 3) [false, true, false] [true, false, false] (k + 1)
  | p (n : Nat) : Blk (n + 1) [true, false, true, false] [true, false, true, false] (2 * (n + 1))
  | q (n : Nat) : Blk (n + 1) [false, false, true, false] [true, false, true, false] (2 * n)

theorem Blk.vis {n m : Nat} {w w' : List Bool} (hb : Blk n w w' m) {t t' : Tape} (h : VisN m t t') :
    VisN n (app w t) (app w' t') := by
  cases hb with
  | z0 k => exact b000_odd h
  | z1 k =>
    have e : 2 * k + 2 = 2 * (k + 1) := by omega
    rw [e]; exact b000_even h
  | o0 k => exact b100_odd h
  | o1 k =>
    have e : 2 * k + 2 = 2 * (k + 1) := by omega
    rw [e]; exact l100 (k + 1) h
  | t0 k => exact b110_0 h
  | t1 k => exact b110_1 h
  | w1 => cases h; exact visN_one vis_0
  | w0 k =>
    exact ⟨_, vis_0, b110_0 h⟩
  | w2 k =>
    exact ⟨_, vis_0, b110_1 h⟩
  | p n => exact visN_1010 h
  | q n =>
    cases n with
    | zero => cases h; exact visN_one vis_0
    | succ n => exact ⟨_, vis_0, visN_1010 h⟩

/-! Halting inside a block: the `j`-th visit sent on halts. -/

theorem h100 {j : Nat} {t u : Tape} (h : VisN j t u) (hu : VisHalts u) :
    VisNH (2 * j + 1) (app [true, false, false] t) :=
  ⟨2 * j, _, by omega, l100 j h, vis_100_halts_1 hu⟩

theorem h000 {j : Nat} {t u : Tape} (h : VisN j t u) (hu : VisHalts u) :
    VisNH (2 * j + 2) (app [false, false, false] t) :=
  visNH_cons vis_0 (h100 h hu)

theorem h110 {j : Nat} {t u : Tape} (h : VisN j t u) (hu : VisHalts u) :
    VisNH (2 * j + 1) (app [true, true, false] t) := by
  cases j with
  | zero => cases h; exact ⟨0, _, by omega, rfl, vis_110_halts_1 hu⟩
  | succ j =>
    obtain ⟨t1, h1, h2⟩ := h
    have e : 2 * (j + 1) + 1 = (2 * j + 2) + 1 := by omega
    rw [e]
    exact visNH_cons (vis_110 h1) (h000 h2 hu)

theorem h1010 {j : Nat} {t u : Tape} (h : VisN j t u) (hu : VisHalts u) :
    VisNH (j / 2 + 1) (app [true, false, true, false] t) := by
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have e : j = 2 * (j / 2) := by omega
    rw [e] at h
    exact ⟨j / 2, _, by omega, visN_1010 h, vis_1010_halts_1 hu⟩
  · have e : j = 2 * (j / 2) + 1 := by omega
    rw [e] at h
    obtain ⟨x, h1, h2⟩ := visN_snoc h
    exact ⟨j / 2, _, by omega, visN_1010 h1, vis_1010_halts_2 h2 hu⟩

theorem Blk.halts {n m : Nat} {w w' : List Bool} (hb : Blk n w w' m) {t : Tape} (h : VisNH m t) :
    VisNH n (app w t) := by
  obtain ⟨j, u, hj, h1, h2⟩ := h
  cases hb with
  | z0 k => exact visNH_mono (h000 h1 h2) (by omega)
  | z1 k => exact visNH_mono (h000 h1 h2) (by omega)
  | o0 k => exact visNH_mono (h100 h1 h2) (by omega)
  | o1 k => exact visNH_mono (h100 h1 h2) (by omega)
  | t0 k => exact visNH_mono (h110 h1 h2) (by omega)
  | t1 k => exact visNH_mono (h110 h1 h2) (by omega)
  | w1 => omega
  | w0 k =>
    have e : 2 * k + 2 = (2 * k + 1) + 1 := by omega
    rw [e]; exact visNH_cons vis_0 (visNH_mono (h110 h1 h2) (by omega))
  | w2 k =>
    have e : 2 * k + 3 = (2 * k + 2) + 1 := by omega
    rw [e]; exact visNH_cons vis_0 (visNH_mono (h110 h1 h2) (by omega))
  | p n => exact visNH_mono (h1010 h1 h2) (by omega)
  | q n => exact visNH_cons vis_0 (visNH_mono (h1010 h1 h2) (by omega))

theorem Blk.len_le {n m : Nat} {w w' : List Bool} (hb : Blk n w w' m) : w.length ≤ 4 := by
  cases hb <;> simp

theorem Blk.len {n m : Nat} {w w' : List Bool} (hb : Blk n w w' m) : w'.length = w.length := by
  cases hb <;> rfl

/-! ## Cascades -/

/-- `n` visits to `s` (n ≥ 1) rewrite it to `s'`; the cascade stops at offset `f`; `E` lists the offsets where a
visit meets `1011`. -/
inductive Casc : Nat → Tape → Tape → Nat → List Nat → Prop
  /-- The block passes no visit on: the cascade stops here. -/
  | fin {n : Nat} {w w' : List Bool} {t : Tape} : Blk n w w' 0 → Casc n (app w t) (app w' t) 0 []
  /-- The block passes `m + 1` visits on to the stream after it. -/
  | fwd {n m f : Nat} {w w' : List Bool} {t t' : Tape} {E : List Nat} :
      Blk n w w' (m + 1) → Casc (m + 1) t t' f E →
      Casc n (app w t) (app w' t') (w.length + f) (E.map (w.length + ·))
  /-- One visit to `1011` leaves `1000`. -/
  | e1 {t : Tape} : Casc 1 (app [true, false, true, true] t) (app [true, false, false, false] t) 0 [0]
  /-- The first visit to `1011` leaves `1000`, the rest are visits to `1000`. -/
  | e {n f : Nat} {t s' : Tape} {E : List Nat} : Casc n (app [true, false, false, false] t) s' f E →
      Casc (n + 1) (app [true, false, true, true] t) s' f (0 :: E)
  /-- One visit to `0011` leaves `1011`. -/
  | d1 {t : Tape} : Casc 1 (app [false, false, true, true] t) (app [true, false, true, true] t) 0 []
  /-- The first visit to `0011` leaves `1011`, the rest are visits to `1011`. -/
  | d {n f : Nat} {t s' : Tape} {E : List Nat} : Casc n (app [true, false, true, true] t) s' f E →
      Casc (n + 1) (app [false, false, true, true] t) s' f E
  /-- One visit to `011` leaves `111`. -/
  | u1 {t : Tape} : Casc 1 (app [false, true, true] t) (app [true, true, true] t) 0 []

/-- One of the `n` visits to `s` halts, in the block at offset `p`, on `111`. -/
inductive CascH : Nat → Tape → Nat → Prop
  | h111 {n : Nat} {t : Tape} : CascH (n + 1) (app [true, true, true] t) 0
  | h011 {n : Nat} {t : Tape} : CascH (n + 2) (app [false, true, true] t) 0
  | fwd {n m p : Nat} {w w' : List Bool} {t : Tape} :
      Blk n w w' (m + 1) → CascH (m + 1) t p → CascH n (app w t) (w.length + p)
  | e {n p : Nat} {t : Tape} : CascH n (app [true, false, false, false] t) p →
      CascH (n + 1) (app [true, false, true, true] t) p
  | d {n p : Nat} {t : Tape} : CascH n (app [true, false, true, true] t) p →
      CascH (n + 1) (app [false, false, true, true] t) p

/-- A cascade is `n` visits of the machine. -/
theorem Casc.vis {n f : Nat} {s s' : Tape} {E : List Nat} (h : Casc n s s' f E) : VisN n s s' := by
  induction h with
  | fin hb => exact hb.vis rfl
  | fwd hb _ ih => exact hb.vis ih
  | e1 => exact visN_one vis_1011
  | e _ ih => exact ⟨_, vis_1011, ih⟩
  | d1 => exact visN_one vis_0
  | d _ ih => exact ⟨_, vis_0, ih⟩
  | u1 => exact visN_one vis_0

/-- A halting cascade: one of the `n` visits of the machine halts. -/
theorem CascH.vis {n p : Nat} {s : Tape} (h : CascH n s p) : VisNH n s := by
  induction h with
  | h111 => exact ⟨0, _, by omega, rfl, vis_111_halts⟩
  | h011 => exact visNH_cons vis_0 ⟨0, _, by omega, rfl, vis_111_halts⟩
  | fwd hb _ ih => exact hb.halts ih
  | e _ ih => exact visNH_cons vis_1011 ih
  | d _ ih => exact visNH_cons vis_0 ih

/-! ## Clean up to where the cascade stopped -/

/-- No two adjacent 1s at offsets `i, i + 1` with `i < b`. -/
def Clean (b : Nat) (s : Tape) : Prop := ∀ i, i < b → s i = true → s (i + 1) = false

theorem app_at : ∀ (w : List Bool) (t : Tape) (i : Nat), app w t (w.length + i) = t i
  | [], t, i => by simp
  | a :: w, t, i => by
    have e : (a :: w).length + i = (w.length + i) + 1 := by simp; omega
    rw [e]; exact app_at w t i

theorem app_ge (w : List Bool) (t : Tape) {i : Nat} (h : w.length ≤ i) : app w t i = t (i - w.length) := by
  have e : i = w.length + (i - w.length) := by omega
  conv => lhs; rw [e]
  exact app_at w t _

theorem clean_zero (s : Tape) : Clean 0 s := fun _ h => absurd h (Nat.not_lt_zero _)

theorem clean_app {b : Nat} {w : List Bool} {t : Tape} (h : Clean b (app w t)) : Clean (b - w.length) t := by
  intro i hi h1
  have := h (w.length + i) (by omega)
  have e : w.length + i + 1 = w.length + (i + 1) := by omega
  rw [app_at, e, app_at] at this
  exact this h1

theorem clean_cons_false {b : Nat} {t : Tape} (h : Clean b t) : Clean (b + 1) (cons false t) := by
  intro i hi h1
  cases i with
  | zero => cases h1
  | succ i => exact h i (by omega) h1

theorem clean_cons_true {b : Nat} {t : Tape} (h : Clean b t) (h0 : t 0 = false) : Clean (b + 1) (cons true t) := by
  intro i hi h1
  cases i with
  | zero => exact h0
  | succ i => exact h i (by omega) h1

/-- Two adjacent 1s at offsets 2 and 3. -/
theorem dirty2 {b : Nat} {x y : Bool} {t : Tape} (h : Clean b (app [x, y, true, true] t)) : b ≤ 2 := by
  have := h 2
  revert this
  show (2 < b → true = true → true = false) → b ≤ 2
  intro h'; rcases Nat.lt_or_ge 2 b with hb | hb
  · exact absurd (h' hb rfl) (by decide)
  · omega

theorem dirty1 {b : Nat} {x : Bool} {t : Tape} (h : Clean b (app [x, true, true] t)) : b ≤ 1 := by
  have := h 1
  revert this
  show (1 < b → true = true → true = false) → b ≤ 1
  intro h'; rcases Nat.lt_or_ge 1 b with hb | hb
  · exact absurd (h' hb rfl) (by decide)
  · omega

theorem dirty0 {b : Nat} {t : Tape} (h : Clean b (app [true, true] t)) : b ≤ 0 := by
  have := h 0
  revert this
  show (0 < b → true = true → true = false) → b ≤ 0
  intro h'; rcases Nat.lt_or_ge 0 b with hb | hb
  · exact absurd (h' hb rfl) (by decide)
  · omega

/-- A block that passes visits on is left as `000`, `100` or `1010`: clean, and ending in 0. -/
theorem Blk.out {n m f : Nat} {w w' : List Bool} (hb : Blk n w w' m) (hm : 0 < m) {t : Tape} (h : Clean f t) :
    Clean (w.length + f) (app w' t) := by
  have c3 : ∀ a : Bool, Clean (3 + f) (app [a, false, false] t) := by
    intro a
    have e : 3 + f = ((f + 1) + 1) + 1 := by omega
    rw [e]
    cases a
    · exact clean_cons_false (clean_cons_false (clean_cons_false h))
    · exact clean_cons_true (clean_cons_false (clean_cons_false h)) rfl
  have c4 : Clean (4 + f) (app [true, false, true, false] t) := by
    have e : 4 + f = (((f + 1) + 1) + 1) + 1 := by omega
    rw [e]
    exact clean_cons_true (clean_cons_false (clean_cons_true (clean_cons_false h) rfl)) rfl
  cases hb with
  | z0 k => exact c3 true
  | z1 k => exact c3 false
  | o0 k => exact c3 false
  | o1 k => exact c3 true
  | t0 k => exact c3 false
  | t1 k => exact c3 true
  | w1 => omega
  | w0 k => exact c3 false
  | w2 k => exact c3 true
  | p n => exact c4
  | q n => exact c4

/-- **A cascade leaves its stream clean up to where it stopped, and meets `1011` only at offsets `p` with
`b ≤ p + 2` when the stream was clean up to `b`.** -/
theorem Casc.clean {n f : Nat} {s s' : Tape} {E : List Nat} (h : Casc n s s' f E) :
    ∀ b, Clean b s → (∀ p ∈ E, b ≤ p + 2) ∧ Clean f s' := by
  induction h with
  | fin _ => exact fun _ _ => ⟨by simp, clean_zero _⟩
  | @fwd n m f w w' t t' E hb _ ih =>
    intro b hc
    obtain ⟨h1, h2⟩ := ih (b - w.length) (clean_app hc)
    refine ⟨?_, hb.out (by omega) h2⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have := h1 q hq
    omega
  | e1 => exact fun b hc => ⟨by have := dirty2 hc; simp; omega, clean_zero _⟩
  | e _ ih =>
    intro b hc
    have hb2 := dirty2 hc
    obtain ⟨_, h2⟩ := ih 0 (clean_zero _)
    refine ⟨?_, h2⟩
    intro p hp
    omega
  | d1 => exact fun _ _ => ⟨by simp, clean_zero _⟩
  | d _ ih =>
    intro b hc
    have hb2 := dirty2 hc
    obtain ⟨_, h2⟩ := ih 0 (clean_zero _)
    exact ⟨fun p _ => by omega, h2⟩
  | u1 => exact fun _ _ => ⟨by simp, clean_zero _⟩

/-- **A cascade on a stream clean up to `b` can halt only at offsets `p` with `b ≤ p + 2`.** -/
theorem CascH.clean {n p : Nat} {s : Tape} (h : CascH n s p) : ∀ b, Clean b s → b ≤ p + 2 := by
  induction h with
  | h111 => intro b hc; have := dirty0 hc; omega
  | h011 => intro b hc; have := dirty1 hc; omega
  | @fwd n m p w w' t hb _ ih =>
    intro b hc
    have := ih (b - w.length) (clean_app hc)
    omega
  | e _ _ => intro b hc; have := dirty2 hc; omega
  | d _ _ => intro b hc; have := dirty2 hc; omega

/-! ## Every cascade has an outcome -/

/-- `s` is blank from cell `N` on. -/
def BlankFrom (N : Nat) (s : Tape) : Prop := ∀ i, N ≤ i → s i = false

/-- The `n` visits to `s` either finish as a cascade or halt. -/
def Outcome (n : Nat) (s : Tape) : Prop := (∃ s' f E, Casc n s s' f E) ∨ (∃ p, CascH n s p)

theorem lift {n m : Nat} {w w' : List Bool} {t : Tape} (hb : Blk n w w' m)
    (ho : ∀ m', m = m' + 1 → Outcome (m' + 1) t) : Outcome n (app w t) := by
  cases m with
  | zero => exact Or.inl ⟨_, _, _, Casc.fin hb⟩
  | succ m' =>
    rcases ho m' rfl with ⟨s', f, E, hc⟩ | ⟨p, hc⟩
    · exact Or.inl ⟨_, _, _, Casc.fwd hb hc⟩
    · exact Or.inr ⟨_, CascH.fwd hb hc⟩

theorem split3 (s : Tape) : s = app [s 0, s 1, s 2] (fun i => s (i + 3)) := by
  funext i; rcases i with _ | _ | _ | i <;> rfl

theorem split4 (s : Tape) : s = app [s 0, s 1, s 2, s 3] (fun i => s (i + 4)) := by
  funext i; rcases i with _ | _ | _ | _ | i <;> rfl

theorem parity {n : Nat} (h : 0 < n) : ∃ k, n = 2 * k + 1 ∨ n = 2 * k + 2 :=
  ⟨(n - 1) / 2, by omega⟩

theorem total_blank : ∀ (K n : Nat), n ≤ K → 0 < n → ∀ s, BlankFrom 0 s → Outcome n s
  | 0, n, hK, hn, _, _ => by omega
  | K + 1, n, hK, hn, s, hs => by
    have e : s = app [false, false, false] (fun i => s (i + 3)) := by
      conv => lhs; rw [split3 s]
      rw [hs 0 (by omega), hs 1 (by omega), hs 2 (by omega)]
    have ht : BlankFrom 0 (fun i => s (i + 3)) := fun i _ => hs (i + 3) (by omega)
    rw [e]
    obtain ⟨k, rfl | rfl⟩ := parity hn
    · exact lift (Blk.z0 k) (fun m' hm => total_blank K (m' + 1) (by omega) (by omega) _ ht)
    · exact lift (Blk.z1 k) (fun m' hm => total_blank K (m' + 1) (by omega) (by omega) _ ht)

/-- Visits to `1011`: the first leaves `1000`, which is the block `100` followed by `0 t`. -/
theorem out1011 {t : Tape} (h : ∀ n, 0 < n → Outcome n (cons false t)) :
    ∀ n, 0 < n → Outcome n (app [true, false, true, true] t) := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => exact Or.inl ⟨_, _, _, Casc.e1⟩
    | succ n =>
      have ho : Outcome (n + 1) (app [true, false, false] (cons false t)) := by
        obtain ⟨k, hk | hk⟩ := parity (Nat.succ_pos n)
        · rw [show n + 1 = 2 * k + 1 from hk]; exact lift (Blk.o0 k) (fun m' hm => by rw [hm] at *; exact h _ (by omega))
        · rw [show n + 1 = 2 * k + 2 from hk]; exact lift (Blk.o1 k) (fun m' hm => by rw [hm] at *; exact h _ (by omega))
      rcases ho with ⟨s', f, E, hc⟩ | ⟨p, hc⟩
      · exact Or.inl ⟨_, _, _, Casc.e hc⟩
      · exact Or.inr ⟨_, CascH.e hc⟩

/-- **Every number of visits to an eventually blank stream either finishes as a cascade or halts.** -/
theorem total : ∀ (K N : Nat), N ≤ K → ∀ s, BlankFrom N s → ∀ n, 0 < n → Outcome n s
  | K, 0, _, s, hs, n, hn => total_blank n n (Nat.le_refl _) hn s hs
  | 0, N + 1, hK, _, _, _, _ => by omega
  | K + 1, N + 1, hK, s, hs, n, hn => by
    have ih3 : ∀ m, 0 < m → Outcome m (fun i => s (i + 3)) :=
      total K (N - 2) (by omega) _ (fun i hi => hs (i + 3) (by omega))
    have ih4 : ∀ m, 0 < m → Outcome m (fun i => s (i + 4)) :=
      total K (N - 3) (by omega) _ (fun i hi => hs (i + 4) (by omega))
    have ih4c : ∀ m, 0 < m → Outcome m (cons false (fun i => s (i + 4))) := by
      refine total K (N - 2) (by omega) _ ?_
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact hs (i + 4) (by omega)
    have l3 : ∀ {w w' : List Bool} {m : Nat}, Blk n w w' m → w.length = 3 →
        s = app w (fun i => s (i + 3)) → Outcome n s := by
      intro w w' m hb _ e
      rw [e]; exact lift hb (fun m' _ => ih3 _ (by omega))
    have l4 : ∀ {w w' : List Bool} {m : Nat}, Blk n w w' m →
        s = app w (fun i => s (i + 4)) → Outcome n s := by
      intro w w' m hb e
      rw [e]; exact lift hb (fun m' _ => ih4 _ (by omega))
    have e3 := split3 s
    have e4 := split4 s
    obtain ⟨k, hk⟩ := parity hn
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> rw [h0, h1, h2] at e3 e4
    · -- 000
      rcases hk with rfl | rfl
      · exact l3 (Blk.z0 k) rfl e3
      · exact l3 (Blk.z1 k) rfl e3
    · -- 001x
      cases h3 : s 3 <;> rw [h3] at e4
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        exact l4 (Blk.q n') e4
      · -- 0011
        rw [e4]
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        cases n' with
        | zero => exact Or.inl ⟨_, _, _, Casc.d1⟩
        | succ n' =>
          rcases out1011 ih4c (n' + 1) (by omega) with ⟨s', f, E, hc⟩ | ⟨p, hc⟩
          · exact Or.inl ⟨_, _, _, Casc.d hc⟩
          · exact Or.inr ⟨_, CascH.d hc⟩
    · -- 010
      rcases hk with rfl | rfl
      · cases k with
        | zero => exact l3 Blk.w1 rfl e3
        | succ k =>
          have e : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
          rw [e]; exact l3 (Blk.w2 k) rfl e3
      · exact l3 (Blk.w0 k) rfl e3
    · -- 011
      rw [e3]
      rcases hk with rfl | rfl
      · cases k with
        | zero => exact Or.inl ⟨_, _, _, Casc.u1⟩
        | succ k =>
          have e : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
          rw [e]; exact Or.inr ⟨_, CascH.h011⟩
      · exact Or.inr ⟨_, CascH.h011⟩
    · -- 100
      rcases hk with rfl | rfl
      · exact l3 (Blk.o0 k) rfl e3
      · exact l3 (Blk.o1 k) rfl e3
    · -- 101x
      cases h3 : s 3 <;> rw [h3] at e4
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        exact l4 (Blk.p n') e4
      · rw [e4]; exact out1011 ih4c n hn
    · -- 110
      rcases hk with rfl | rfl
      · exact l3 (Blk.t0 k) rfl e3
      · exact l3 (Blk.t1 k) rfl e3
    · -- 111
      rw [e3]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact Or.inr ⟨_, CascH.h111⟩

/-- A cascade that stops at `f` changes no cell from `f + 4` on. -/
theorem Casc.frame {n f : Nat} {s s' : Tape} {E : List Nat} (h : Casc n s s' f E) :
    ∀ i, f + 4 ≤ i → s' i = s i := by
  induction h with
  | @fin n w w' t hb =>
    intro i hi
    have hl := hb.len_le
    rw [app_ge w' t (by rw [hb.len]; omega), app_ge w t (by omega), hb.len]
  | @fwd n m f w w' t t' E hb _ ih =>
    intro i hi
    have hl := hb.len_le
    rw [app_ge w' t' (by rw [hb.len]; omega), app_ge w t (by omega), hb.len]
    exact ih _ (by omega)
  | @e1 t =>
    intro i hi
    rw [app_ge _ t (by simp; omega), app_ge _ t (by simp; omega)]; rfl
  | @e n f t s' E _ ih =>
    intro i hi
    rw [ih i hi, app_ge _ t (by simp; omega), app_ge _ t (by simp; omega)]; rfl
  | @d1 t =>
    intro i hi
    rw [app_ge _ t (by simp; omega), app_ge _ t (by simp; omega)]; rfl
  | @d n f t s' E _ ih =>
    intro i hi
    rw [ih i hi, app_ge _ t (by simp; omega), app_ge _ t (by simp; omega)]; rfl
  | @u1 t =>
    intro i hi
    rw [app_ge _ t (by simp; omega), app_ge _ t (by simp; omega)]; rfl

/-! ## The run, round by round -/

/-- The run in this model: after `r` rounds the machine is at `0^∞ A> 1 0 S`, and the cascade of round `r`
stopped at offset `F` of the stream `1 0 S` (0 before the first round). -/
inductive Reach : Nat → Tape → Nat → Prop
  | start : Reach 0 (app [true] blank) 0
  | next {r F f : Nat} {S S' : Tape} {E : List Nat} : Reach r S F →
      Casc 1 (cons true (cons false S)) S' f E → Reach (r + 1) S' (f + 2)

theorem round_pos {s s' : Tape} (h : Vis (cons true (cons false s)) s') :
    ∃ n, 0 < n ∧ steps n (LE s) = some (LE s') := by
  obtain ⟨n1, e1⟩ := h true blank
  have a0 : steps 4 ⟨cons false (cons false blank), cons true (cons false s), .A⟩ =
      some ⟨cons false (cons true blank), cons true (cons false s), .C⟩ := rfl
  rw [blank_eq] at a0
  exact ⟨4 + n1, by omega, steps_seq trans a0 e1⟩

/-- After `r` rounds of the model the machine is at `0^∞ A> 1 0 S`, after at least `r` steps. -/
theorem reach_steps {r F : Nat} {S : Tape} (h : Reach r S F) : ∃ n, r ≤ n ∧ steps n init = some (LE S) := by
  induction h with
  | start => exact ⟨4, by omega, start⟩
  | next _ hc ih =>
    obtain ⟨n, hn, e⟩ := ih
    obtain ⟨k, hk, e'⟩ := round_pos (visN_one_inv hc.vis)
    exact ⟨n + k, by omega, steps_seq trans e e'⟩

theorem reach_blank {r F : Nat} {S : Tape} (h : Reach r S F) : ∃ N, BlankFrom N (cons true (cons false S)) := by
  induction h with
  | start => exact ⟨3, fun i hi => by rcases i with _ | _ | _ | i; all_goals first | omega | rfl⟩
  | @next r F f S S' E _ hc ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N + f + 6, fun i hi => ?_⟩
    rcases i with _ | _ | i
    · omega
    · omega
    · show S' i = false
      rw [hc.frame i (by omega)]
      exact hN i (by omega)

/-- **Clean up to the previous stop.** Before every round, `1 0 S` has no two adjacent 1s left of offset `F`,
where the previous round's cascade stopped. -/
theorem reach_clean {r F : Nat} {S : Tape} (h : Reach r S F) : Clean F (cons true (cons false S)) := by
  induction h with
  | start => exact clean_zero _
  | next _ hc ih =>
    have := (hc.clean _ ih).2
    exact clean_cons_true (clean_cons_false this) rfl

/-- **1011 only at the right end.** In round `r + 1`, a visit meets `1011` only at offsets `p` with
`F ≤ p + 2`, where `F` is where round `r`'s cascade stopped. -/
theorem right_end_1011 {r F f : Nat} {S S' : Tape} {E : List Nat} (h : Reach r S F)
    (hc : Casc 1 (cons true (cons false S)) S' f E) : ∀ p ∈ E, F ≤ p + 2 :=
  (hc.clean F (reach_clean h)).1

/-- **111 only at the right end.** A round whose cascade halts halts at an offset `p` with `F ≤ p + 2`. -/
theorem right_end_halt {r F p : Nat} {S : Tape} (h : Reach r S F)
    (hc : CascH 1 (cons true (cons false S)) p) : F ≤ p + 2 :=
  hc.clean F (reach_clean h)

/-- Every round of the model either is a cascade or halts. -/
theorem reach_outcome {r F : Nat} {S : Tape} (h : Reach r S F) : Outcome 1 (cons true (cons false S)) := by
  obtain ⟨N, hN⟩ := reach_blank h
  exact total N N (Nat.le_refl _) _ hN 1 (by omega)

theorem halts_of_cascH {r F p : Nat} {S : Tape} (h : Reach r S F) (hc : CascH 1 (cons true (cons false S)) p) :
    HaltsFromBlank := by
  obtain ⟨n, _, e⟩ := reach_steps h
  obtain ⟨j, u, hj, h1, h2⟩ := hc.vis
  have hj0 : j = 0 := by omega
  subst hj0
  cases h1
  obtain ⟨m, c, e', hc'⟩ := round_halts h2
  exact ⟨n + m, c, steps_seq trans e e', hc'⟩

theorem not_halts (hno : ∀ r F p S, Reach r S F → ¬ CascH 1 (cons true (cons false S)) p) :
    ¬ HaltsFromBlank := by
  have hr : ∀ r, ∃ S F, Reach r S F := by
    intro r
    induction r with
    | zero => exact ⟨_, _, Reach.start⟩
    | succ r ih =>
      obtain ⟨S, F, h⟩ := ih
      rcases reach_outcome h with ⟨S', f, E, hc⟩ | ⟨p, hc⟩
      · exact ⟨_, _, Reach.next h hc⟩
      · exact absurd hc (hno r F p S h)
  apply not_halts_of_forall trans
  apply forall_of_unbounded trans (fun m => ∃ c', steps m init = some c')
  · intro n
    obtain ⟨S, F, h⟩ := hr n
    obtain ⟨m, hm, e⟩ := reach_steps h
    exact ⟨m, hm, _, e⟩
  · exact fun _ h => h

/-- **Halting is a question about the rounds' cascades.** The machine halts from blank tape if and only if the
cascade of some round of the model halts. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ r F p S, Reach r S F ∧ CascH 1 (cons true (cons false S)) p := by
  constructor
  · intro hh
    refine Classical.byContradiction (fun hne => ?_)
    exact not_halts (fun r F p S h hc => hne ⟨r, F, p, S, h, hc⟩) hh
  · rintro ⟨r, F, p, S, h, hc⟩
    exact halts_of_cascH h hc

/-- **Halting is a right-end question.** The machine halts from blank tape if and only if some round's cascade
halts, and it can do so only at an offset `p ≥ F - 2`, where `F` is where the previous round's cascade stopped. -/
theorem halts_iff_right_end : HaltsFromBlank ↔
    ∃ r F p S, Reach r S F ∧ CascH 1 (cons true (cons false S)) p ∧ F ≤ p + 2 := by
  rw [halts_iff]
  constructor
  · rintro ⟨r, F, p, S, h, hc⟩
    exact ⟨r, F, p, S, h, hc, right_end_halt h hc⟩
  · rintro ⟨r, F, p, S, h, hc, -⟩
    exact ⟨r, F, p, S, h, hc⟩

end H173741
