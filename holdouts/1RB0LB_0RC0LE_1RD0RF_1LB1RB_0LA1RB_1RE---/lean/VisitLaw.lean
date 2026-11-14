import TM

/-!
# The visit law as an abstract rewriting system, and a checker for it

A *visit* rewrites a stream (a right half-tape).  The law has four rewriting rules and one halting pattern:

    0 s     → 1 s
    1 0 0 r → 0 0 0 v(r)
    1 1 0 r → 0 0 0 v(r)
    1010 r  → 1010 v(v(r))        (only used when `r` does not start with 1 1)
    1011 r  : the visit halts

`AV s s'` is "one visit rewrites `s` to `s'`" and `AH s` is "a visit to `s` halts", both as inductive relations, so
nothing here depends on a Turing machine.  `Law` says what a machine has to satisfy for the abstract system to
describe it, in two forms of visit `V` and `W`: `W` is the form used for the first of the two nested visits of
the `1010` rule, and it is only ever needed on streams that do not start with 1 1.

`scan` carries a *count* of visits through a finite word in one pass (the count `2^e - c` is kept as the pair
`e`, `c`, so astronomically many visits cost one step per cell), and `check` runs whole rounds with it.
-/

namespace VisitLaw

open TM

theorem cons_one (a : Bool) (s : Tape) : cons a s 1 = s 0 := rfl

/-- `1 0 1 0 r` -/
def L4 (r : Tape) : Tape := cons true (cons false (cons true (cons false r)))
/-- `b 0 0 r` -/
def D3 (b : Bool) (r : Tape) : Tape := cons b (cons false (cons false r))
/-- `1 1 0 r` -/
def G3 (r : Tape) : Tape := cons true (cons true (cons false r))
/-- `1 0 1 1 r` -/
def X4 (r : Tape) : Tape := cons true (cons false (cons true (cons true r)))

/-- The stream does not start with `1 1`. -/
def Guard (r : Tape) : Prop := ¬ (r 0 = true ∧ r 1 = true)

/-- One visit of the abstract system. -/
inductive AV : Tape → Tape → Prop
  | z (s : Tape) : AV (cons false s) (cons true s)
  | h {r r' : Tape} : AV r r' → AV (D3 true r) (D3 false r')
  | g {r r' : Tape} : AV r r' → AV (G3 r) (D3 false r')
  | l {r r1 r2 : Tape} : Guard r → AV r r1 → AV r1 r2 → AV (L4 r) (L4 r2)

/-- A visit of the abstract system that halts. -/
inductive AH : Tape → Prop
  | x (r : Tape) : AH (X4 r)
  | h {r : Tape} : AH r → AH (D3 true r)
  | g {r : Tape} : AH r → AH (G3 r)
  | l1 {r : Tape} : Guard r → AH r → AH (L4 r)
  | l2 {r r1 : Tape} : Guard r → AV r r1 → AH r1 → AH (L4 r)

/-- What a machine's two forms of visit (`V`, `W`) and of halting visit (`VH`, `WH`) have to satisfy. -/
structure Law (V W : Tape → Tape → Prop) (VH WH : Tape → Prop) : Prop where
  v0 : ∀ s, V (cons false s) (cons true s)
  vh : ∀ {r r'}, V r r' → V (D3 true r) (D3 false r')
  vg : ∀ {r r'}, V r r' → V (G3 r) (D3 false r')
  vl : ∀ {r r1 r2}, W r r1 → V r1 r2 → V (L4 r) (L4 r2)
  w0 : ∀ s, W (cons false s) (cons true s)
  wh : ∀ {r r'}, V r r' → W (D3 true r) (D3 false r')
  wl : ∀ {r r1 r2}, W r r1 → V r1 r2 → W (L4 r) (L4 r2)
  vx : ∀ r, VH (X4 r)
  vhh : ∀ {r}, VH r → VH (D3 true r)
  vgh : ∀ {r}, VH r → VH (G3 r)
  vl1 : ∀ {r}, WH r → VH (L4 r)
  vl2 : ∀ {r r1}, W r r1 → VH r1 → VH (L4 r)
  wx : ∀ r, WH (X4 r)
  whh : ∀ {r}, VH r → WH (D3 true r)
  wl1 : ∀ {r}, WH r → WH (L4 r)
  wl2 : ∀ {r r1}, W r r1 → VH r1 → WH (L4 r)

theorem guard_G3 (r : Tape) : ¬ Guard (G3 r) := fun h => h ⟨rfl, rfl⟩

theorem Law.av {V W : Tape → Tape → Prop} {VH WH : Tape → Prop} (law : Law V W VH WH) {s s' : Tape}
    (h : AV s s') : V s s' ∧ (Guard s → W s s') := by
  induction h with
  | z s => exact ⟨law.v0 s, fun _ => law.w0 s⟩
  | h _ ih => exact ⟨law.vh ih.1, fun _ => law.wh ih.1⟩
  | g _ ih => exact ⟨law.vg ih.1, fun hg => absurd hg (guard_G3 _)⟩
  | l hg _ _ ih1 ih2 => exact ⟨law.vl (ih1.2 hg) ih2.1, fun _ => law.wl (ih1.2 hg) ih2.1⟩

theorem Law.ah {V W : Tape → Tape → Prop} {VH WH : Tape → Prop} (law : Law V W VH WH) {s : Tape}
    (h : AH s) : VH s ∧ (Guard s → WH s) := by
  induction h with
  | x r => exact ⟨law.vx r, fun _ => law.wx r⟩
  | h _ ih => exact ⟨law.vhh ih.1, fun _ => law.whh ih.1⟩
  | g _ ih => exact ⟨law.vgh ih.1, fun hg => absurd hg (guard_G3 _)⟩
  | l1 hg _ ih => exact ⟨law.vl1 (ih.2 hg), fun _ => law.wl1 (ih.2 hg)⟩
  | l2 hg hv _ ih => exact ⟨law.vl2 ((law.av hv).2 hg) ih.1, fun _ => law.wl2 ((law.av hv).2 hg) ih.1⟩

/-! ## Heads -/

theorem av_head {x y : Tape} (h : AV x y) :
    (x 0 = false ∧ y 0 = true ∧ y 1 = x 1) ∨ (x 0 = true ∧ y 1 = false) := by
  cases h with
  | z s => exact Or.inl ⟨rfl, rfl, rfl⟩
  | h _ => exact Or.inr ⟨rfl, rfl⟩
  | g _ => exact Or.inr ⟨rfl, rfl⟩
  | l _ _ _ => exact Or.inr ⟨rfl, rfl⟩

/-- After two visits the second cell of a stream is 0, so the stream does not start with `1 1`. -/
theorem av2_guard {r r1 r2 : Tape} (h1 : AV r r1) (h2 : AV r1 r2) : Guard r2 := by
  have : r2 1 = false := by
    rcases av_head h1 with ⟨_, a, _⟩ | ⟨_, b⟩
    · rcases av_head h2 with ⟨c, _, _⟩ | ⟨_, d⟩
      · rw [a] at c; cases c
      · exact d
    · rcases av_head h2 with ⟨_, _, c⟩ | ⟨_, d⟩
      · rw [c]; exact b
      · exact d
  intro hh; rw [this] at hh; cases hh.2

/-! ## Many visits -/

/-- `n` visits in a row. -/
inductive VS : Nat → Tape → Tape → Prop
  | zero (s : Tape) : VS 0 s s
  | succ {n : Nat} {s s1 s2 : Tape} : AV s s1 → VS n s1 s2 → VS (n + 1) s s2

theorem VS.one {s s' : Tape} (h : AV s s') : VS 1 s s' := .succ h (.zero _)

theorem VS.add {a b : Nat} {s s1 s2 : Tape} (h1 : VS a s s1) (h2 : VS b s1 s2) : VS (b + a) s s2 := by
  induction h1 with
  | zero s => exact h2
  | succ hv _ ih => exact .succ hv (ih h2)

theorem VS.snoc {n : Nat} {s s1 s2 : Tape} (h1 : VS n s s1) (h2 : AV s1 s2) : VS (n + 1) s s2 := by
  have := VS.add h1 (VS.one h2)
  rwa [Nat.add_comm] at this

theorem VS.unsnoc {n : Nat} {s s2 : Tape} (h : VS (n + 1) s s2) : ∃ s1, VS n s s1 ∧ AV s1 s2 := by
  induction n generalizing s with
  | zero => cases h with | succ hv hr => cases hr; exact ⟨_, .zero _, hv⟩
  | succ n ih =>
    cases h with
    | succ hv hr =>
      obtain ⟨s1, a, b⟩ := ih hr
      exact ⟨s1, .succ hv a, b⟩

theorem VS.cast {a b : Nat} {s s' : Tape} (h : VS a s s') (e : a = b) : VS b s s' := e ▸ h

theorem VS.one_inv {s s' : Tape} (h : VS 1 s s') : AV s s' := by
  cases h with | succ hv hr => cases hr; exact hv

/-- After at least two visits the stream does not start with `1 1`. -/
theorem VS.guard {n : Nat} {s s' : Tape} (h : VS (n + 2) s s') : Guard s' := by
  obtain ⟨s1, h1, a⟩ := VS.unsnoc h
  obtain ⟨s0, _, b⟩ := VS.unsnoc h1
  exact av2_guard b a

theorem vs_L {n : Nat} {r r' : Tape} (hg : Guard r) (h : VS (2 * n) r r') : VS n (L4 r) (L4 r') := by
  induction n generalizing r with
  | zero => cases h; exact .zero _
  | succ n ih =>
    have h' : VS (2 * n + 1 + 1) r r' := h.cast (by omega)
    cases h' with
    | succ hv hr => cases hr with
      | succ hv2 hr2 => exact .succ (.l hg hv hv2) (ih (av2_guard hv hv2) hr2)

theorem vs_ZZ {n : Nat} {r r' : Tape} (h : VS n r r') : VS (2 * n) (D3 false r) (D3 false r') := by
  induction h with
  | zero s => exact .zero _
  | succ hv _ ih => exact (VS.succ (.z _) (.succ (.h hv) ih)).cast (by omega)

theorem vs_HH {n : Nat} {r r' : Tape} (h : VS n r r') : VS (2 * n) (D3 true r) (D3 true r') := by
  induction h with
  | zero s => exact .zero _
  | succ hv _ ih => exact (VS.succ (.h hv) (.succ (.z _) ih)).cast (by omega)

/-- `0 0 0 r` under `n` visits: a binary digit. -/
theorem law_Z {n : Nat} {r r' : Tape} (h : VS (n / 2) r r') : VS n (D3 false r) (D3 (n % 2 == 1) r') := by
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · have : (n % 2 == 1) = false := by rw [e]; rfl
    rw [this]; exact (vs_ZZ h).cast (by omega)
  · have : (n % 2 == 1) = true := by rw [e]; rfl
    rw [this]; exact ((vs_ZZ h).snoc (.z _)).cast (by omega)

/-- `1 0 0 r` under `n` visits. -/
theorem law_H {n : Nat} {r r' : Tape} (h : VS ((n + 1) / 2) r r') : VS n (D3 true r) (D3 (n % 2 == 0) r') := by
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · have : (n % 2 == 0) = true := by rw [e]; rfl
    rw [this]; exact (vs_HH h).cast (by omega)
  · have : (n % 2 == 0) = false := by rw [e]; rfl
    rw [this]
    obtain ⟨s1, a, b⟩ := VS.unsnoc (h.cast (by omega : (n + 1) / 2 = n / 2 + 1))
    exact ((vs_HH a).snoc (.h b)).cast (by omega)

/-- `1 1 0 r` under `n ≥ 1` visits. -/
theorem law_G {n : Nat} {r r' : Tape} (hn : 1 ≤ n) (h : VS ((n + 1) / 2) r r') :
    VS n (G3 r) (D3 (n % 2 == 0) r') := by
  have h' : VS ((n - 1) / 2 + 1) r r' := h.cast (by omega)
  cases h' with
  | succ hv hr =>
    have := VS.succ (.g hv) (law_Z (n := n - 1) hr)
    have e : ((n - 1) % 2 == 1) = (n % 2 == 0) := by
      rcases Nat.mod_two_eq_zero_or_one n with e | e
      · have : (n - 1) % 2 = 1 := by omega
        rw [e, this]; rfl
      · have : (n - 1) % 2 = 0 := by omega
        rw [e, this]; rfl
    rw [e] at this
    exact this.cast (by omega)

/-- `0 s` under `n ≥ 1` visits: the first visit writes the 1. -/
theorem law_0 {n : Nat} {s s' : Tape} (hn : 1 ≤ n) (h : VS (n - 1) (cons true s) s') : VS n (cons false s) s' :=
  (VS.succ (.z s) h).cast (by omega)

/-! ## Halting within `n` visits -/

/-- One of the first `n` visits halts. -/
def HVS (n : Nat) (s : Tape) : Prop := ∃ m s1, m < n ∧ VS m s s1 ∧ AH s1

theorem hvs_one {s : Tape} (h : HVS 1 s) : AH s := by
  obtain ⟨m, s1, hm, hv, ha⟩ := h
  have : m = 0 := by omega
  subst this; cases hv; exact ha

theorem hvs_X {n : Nat} (hn : 1 ≤ n) (r : Tape) : HVS n (X4 r) := ⟨0, _, hn, .zero _, .x r⟩

theorem hvs_Z {n : Nat} {r : Tape} (h : HVS (n / 2) r) : HVS n (D3 false r) := by
  obtain ⟨m, s1, hm, hv, ha⟩ := h
  exact ⟨2 * m + 1, _, by omega, (vs_ZZ hv).snoc (.z _), .h ha⟩

theorem hvs_H {n : Nat} {r : Tape} (h : HVS ((n + 1) / 2) r) : HVS n (D3 true r) := by
  obtain ⟨m, s1, hm, hv, ha⟩ := h
  exact ⟨2 * m, _, by omega, vs_HH hv, .h ha⟩

theorem hvs_G {n : Nat} {r : Tape} (h : HVS ((n + 1) / 2) r) : HVS n (G3 r) := by
  obtain ⟨m, s1, hm, hv, ha⟩ := h
  cases hv with
  | zero s => exact ⟨0, _, by omega, .zero _, .g ha⟩
  | succ hv1 hr =>
    rename_i k s0
    exact ⟨2 * k + 1 + 1, _, by omega, .succ (.g hv1) ((vs_ZZ hr).snoc (.z _)), .h ha⟩

theorem hvs_L {n : Nat} {r : Tape} (hg : Guard r) (h : HVS (2 * n) r) : HVS n (L4 r) := by
  obtain ⟨m, s1, hm, hv, ha⟩ := h
  rcases Nat.mod_two_eq_zero_or_one m with e | e
  · have hv' : VS (2 * (m / 2)) r s1 := hv.cast (by omega)
    have g1 : Guard s1 := by
      rcases Nat.eq_zero_or_pos (m / 2) with z | p
      · have : m = 0 := by omega
        subst this; cases hv; exact hg
      · exact VS.guard (n := m - 2) (hv.cast (by omega))
    exact ⟨m / 2, _, by omega, vs_L hg hv', .l1 g1 ha⟩
  · obtain ⟨s0, a, b⟩ := VS.unsnoc (hv.cast (by omega : m = 2 * (m / 2) + 1))
    have g0 : Guard s0 := by
      rcases Nat.eq_zero_or_pos (m / 2) with z | p
      · rw [z] at a; cases a; exact hg
      · exact VS.guard (n := 2 * (m / 2) - 2) (a.cast (by omega))
    exact ⟨m / 2, _, by omega, vs_L hg a, .l2 g0 b ha⟩

theorem hvs_0 {n : Nat} {s : Tape} (h : HVS (n - 1) (cons true s)) : HVS n (cons false s) := by
  obtain ⟨m, s1, hm, hv, ha⟩ := h
  exact ⟨m + 1, _, by omega, .succ (.z s) hv, ha⟩

end VisitLaw
