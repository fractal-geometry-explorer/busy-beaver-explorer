import Step

/-!
# 1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA: the resets, the phase map and `halts_iff`

`Ph x c t` is the phase configuration S_t(x, c) = `0^inf A> 1^x (01)^2 1^6 (01)^c 1^t 0 1 1 0^inf` (`t = 3` or `6`,
written as a Bool `six`).  For c ≥ 2 a step takes it to `Ph (⌊3x/2⌋+7) (c-2) t` (`step_rule`).  For c = 0 or 1 the
last step ends on the tail instead (`tend*`): the middle block becomes `1^B` behind `1^4 0` or `1^5 0` (`K`), and a
conversion (`k4*`, `k5*`), maybe with a restart (`a2*`, `a3*`, `b3*`, `q4*`, `q5*`), either halts or gives a new
phase configuration.  For c = 1, t = 6 the conversion gives a short phase with a marker `1^3` and three copies of
`01`, which ends at `Ph y 1 3`.  `next` is the resulting map on (x, c, t) (`next_spec`); blank tape reaches
S_3(4, 4) (`start`), so the machine halts iff the orbit of (4, 4, 3) under `next` reaches `none` (`halts_iff`).
(The README's reset from c = 2 is one step to c = 0 followed by the reset here.)  `orbit_585` evaluates the first
585 terms (phases 0 to 2, `native_decide`): no `none`, and term 585 is S_3(6, c) with c odd and above 10^101.
-/

namespace H130861

open TM

def T2 : Tape := cons false (rep 2 [true] blank)
/-- `1^t 0 1 1 0^inf`. -/
def tl : Bool → Nat
  | true => 6
  | false => 3
def Tl (six : Bool) : Tape := rep (tl six) [true] T2
def T13 : Tape := cons false (rep 4 [true] T2)
def T16 : Tape := cons false (rep 7 [true] T2)
/-- S_t(x, c). -/
def Ph (x c : Nat) (six : Bool) : Config := S x c (Tl six)
/-- `0^inf A> 1^p 0 1^B R`. -/
def K (p B : Nat) (R : Tape) : Config := ⟨blank, rep p [true] (cons false (rep B [true] R)), .A⟩
/-- `0^inf A> 1^p (01)^m R`. -/
def Am (p m : Nat) (R : Tape) : Config := ⟨blank, rep p [true] (rep m [false, true] R), .A⟩
/-- `0^inf A> 1^p 0 1^4 (01)^k R`. -/
def Qc (p k : Nat) (R : Tape) : Config := ⟨blank, rep p [true] (cons false (rep 4 [true] (rep k [false, true] R))), .A⟩

theorem rep_succ' (n : Nat) (w : List Bool) (s : Tape) : rep (n + 1) w s = rep n w (app w s) := by
  rw [show n + 1 = n + 1 from rfl, rep_add n 1]; rfl

/-- `(01)^(b+4) s = (01)^3 (01)^b 0 1 s`, to match the conversions that leave the last `01` behind. -/
theorem am_tail (p b : Nat) (s : Tape) :
    rep p [true] (rep (b + 4) [false, true] s) = rep p [true] (rep 3 [false, true] (rep b [false, true] (cons false (cons true s)))) := by
  rw [show b + 4 = 3 + (b + 1) by omega, rep_add, rep_succ' b]; rfl

theorem r10 (n : Nat) (s : Tape) : rep n [true, false] (cons true s) = cons true (rep n [false, true] s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep_succ, app_cons, app_nil, ih]

/-- Unfold the definitions, turn `(11)^k` into `1^(2k)` and `(10)^k 1` into `1 (01)^k`, then compare by `rfl`. -/
macro "tq" : tactic => `(tactic| (simp only [W, S, Ph, K, Am, Qc, Tl, tl, T2, T13, T16, n_tt, r10]; try rfl))

/-- `c` reaches `c'` in some number of steps (maybe none). -/
def Reaches0 (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches0.then {a b c : Config} (h₁ : Reaches0 a b) (h₂ : Reaches1 b c) : Reaches1 a c := by
  obtain ⟨n, h⟩ := h₁
  obtain ⟨m, hm, h'⟩ := h₂
  exact ⟨n + m, by omega, steps_seq H130861.trans h h'⟩

theorem Reaches1.r0 {a b : Config} (h : Reaches1 a b) : Reaches0 a b := by
  obtain ⟨n, _, h⟩ := h; exact ⟨n, h⟩

theorem Reaches1.halts {a b : Config} (h₁ : Reaches1 a b) (h₂ : TM.Halts H130861.trans b) :
    TM.Halts H130861.trans a := by
  obtain ⟨n, _, h⟩ := h₁
  obtain ⟨m, c, h', hc⟩ := h₂
  exact ⟨n + m, c, steps_seq H130861.trans h h', hc⟩

/-! ## The rounds down to x = 2 or 1 -/

theorem wrun_even (r b : Nat) (R : Tape) : Reaches0 (W (2 * r + 2) (b + 1) R) (W 2 (b + 3 * r + 1) R) := by
  cases r with
  | zero => exact ⟨0, rfl⟩
  | succ r =>
    have h := rounds r 1 b R
    rw [show 1 + 1 + 2 * (r + 1) = 2 * (r + 1) + 2 by omega] at h
    exact h.r0

theorem wrun_odd (r b : Nat) (R : Tape) : Reaches0 (W (2 * r + 1) (b + 1) R) (W 1 (b + 3 * r + 1) R) := by
  cases r with
  | zero => exact ⟨0, rfl⟩
  | succ r =>
    have h := rounds r 0 b R
    rw [show 0 + 1 + 2 * (r + 1) = 2 * (r + 1) + 1 by omega] at h
    exact h.r0

/-! ## The end of the last step on a tail -/

theorem tend2_2 (b : Nat) : Reaches1 (W 2 b T2) (K 4 (b + 4) T2) := by
  rcases parity b with ⟨k, rfl | rfl⟩
  · exact of_rule (by omega) (tend2_e_T2 k) (by tq) (by tq)
  · exact of_rule (by omega) (tend2_o_T2 k) (by tq) (by tq)
theorem tend1_2 (b : Nat) : Reaches1 (W 1 b T2) (K 5 (b + 1) T2) := by
  rcases parity b with ⟨k, rfl | rfl⟩
  · exact of_rule (by omega) (tend1_e_T2 k) (by tq) (by tq)
  · exact of_rule (by omega) (tend1_o_T2 k) (by tq) (by tq)
theorem tend2_13 (b : Nat) : Reaches1 (W 2 b T13) (K 4 (b + 4) T13) := by
  rcases parity b with ⟨k, rfl | rfl⟩
  · exact of_rule (by omega) (tend2_e_T13 k) (by tq) (by tq)
  · exact of_rule (by omega) (tend2_o_T13 k) (by tq) (by tq)
theorem tend1_13 (b : Nat) : Reaches1 (W 1 b T13) (K 5 (b + 1) T13) := by
  rcases parity b with ⟨k, rfl | rfl⟩
  · exact of_rule (by omega) (tend1_e_T13 k) (by tq) (by tq)
  · exact of_rule (by omega) (tend1_o_T13 k) (by tq) (by tq)
theorem tend2_16 (b : Nat) : Reaches1 (W 2 b T16) (K 4 (b + 4) T16) := by
  rcases parity b with ⟨k, rfl | rfl⟩
  · exact of_rule (by omega) (tend2_e_T16 k) (by tq) (by tq)
  · exact of_rule (by omega) (tend2_o_T16 k) (by tq) (by tq)
theorem tend1_16 (b : Nat) : Reaches1 (W 1 b T16) (K 5 (b + 1) T16) := by
  rcases parity b with ⟨k, rfl | rfl⟩
  · exact of_rule (by omega) (tend1_e_T16 k) (by tq) (by tq)
  · exact of_rule (by omega) (tend1_o_T16 k) (by tq) (by tq)

/-! ## Restarts -/

theorem restart4 (k : Nat) (six : Bool) : Reaches1 (Am 2 (k + 4) (Tl six)) (Ph 4 k six) := by
  cases six
  · have h1 : Reaches1 (Am 2 (k + 2 + 2) (Tl false)) (Qc 4 (k + 2) (Tl false)) :=
      of_rule (by omega) (a2_T3 (k + 2)) (by tq) (by tq)
    have h2 : Reaches1 (Qc 4 (k + 2) (Tl false)) (Ph 4 k false) := of_rule (by omega) (q4_T3 k) (by tq) (by tq)
    exact h1.trans h2
  · have h1 : Reaches1 (Am 2 (k + 2 + 2) (Tl true)) (Qc 4 (k + 2) (Tl true)) :=
      of_rule (by omega) (a2_T6 (k + 2)) (by tq) (by tq)
    have h2 : Reaches1 (Qc 4 (k + 2) (Tl true)) (Ph 4 k true) := of_rule (by omega) (q4_T6 k) (by tq) (by tq)
    exact h1.trans h2

theorem restart5 (k : Nat) (six : Bool) : Reaches1 (Am 3 (k + 4) (Tl six)) (Ph 5 k six) := by
  cases six
  · have h1 : Reaches1 (Am 3 (k + 2 + 2) (Tl false)) (W 1 3 (rep (k + 2) [false, true] (Tl false))) :=
      of_rule (by omega) (a3_T3 (k + 2)) (by tq) (by tq)
    have h2 : Reaches1 (W 1 3 (rep (k + 2) [false, true] (Tl false))) (Qc 5 (k + 2) (Tl false)) :=
      of_rule (by omega) (b3_T3 (k + 2)) (by tq) (by tq)
    have h3 : Reaches1 (Qc 5 (k + 2) (Tl false)) (Ph 5 k false) := of_rule (by omega) (q5_T3 k) (by tq) (by tq)
    exact (h1.trans h2).trans h3
  · have h1 : Reaches1 (Am 3 (k + 2 + 2) (Tl true)) (W 1 3 (rep (k + 2) [false, true] (Tl true))) :=
      of_rule (by omega) (a3_T6 (k + 2)) (by tq) (by tq)
    have h2 : Reaches1 (W 1 3 (rep (k + 2) [false, true] (Tl true))) (Qc 5 (k + 2) (Tl true)) :=
      of_rule (by omega) (b3_T6 (k + 2)) (by tq) (by tq)
    have h3 : Reaches1 (Qc 5 (k + 2) (Tl true)) (Ph 5 k true) := of_rule (by omega) (q5_T6 k) (by tq) (by tq)
    exact (h1.trans h2).trans h3

/-! ## Conversions -/

/-- What a configuration leads to: `none`, it halts; `some (x, c, six)`, it reaches `Ph x c six`. -/
def Leads (a : Config) : Option (Nat × Nat × Bool) → Prop
  | none => TM.Halts H130861.trans a
  | some (x, c, six) => Reaches1 a (Ph x c six)

theorem Reaches0.halts {a b : Config} (h₁ : Reaches0 a b) (h₂ : TM.Halts H130861.trans b) :
    TM.Halts H130861.trans a := by
  obtain ⟨n, h⟩ := h₁
  obtain ⟨m, c, h', hc⟩ := h₂
  exact ⟨n + m, c, steps_seq H130861.trans h h', hc⟩

theorem Leads.pre {a b : Config} {o : Option (Nat × Nat × Bool)} (h : Reaches0 a b) (h' : Leads b o) : Leads a o := by
  match o, h' with
  | none, h' => exact h.halts h'
  | some (x, c, six), h' => exact h.then h'

theorem halts_of {c c' d : Config} {n : Nat} (h : steps n c = some c') (hc : TM.step H130861.trans c' = none)
    (e : d = c) : TM.Halts H130861.trans d := ⟨n, c', by rw [e]; exact h, hc⟩

/-! ## Conversions -/

theorem ite_t {α : Type} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a := by simp [h]
theorem ite_f {α : Type} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b := by simp [h]

def k4T2 (B : Nat) : Option (Nat × Nat × Bool) := if B % 2 = 0 then none else some (4, (B - 5) / 2, false)
def k5T2 (B : Nat) : Option (Nat × Nat × Bool) :=
  if B % 2 = 0 then some (6, (B - 8) / 2, false) else some (5, (B - 5) / 2, false)
def k4T13 (B : Nat) : Option (Nat × Nat × Bool) := if B % 2 = 0 then none else some (4, (B - 3) / 2, true)
def k5T13 (B : Nat) : Option (Nat × Nat × Bool) :=
  if B % 2 = 0 then some (6, (B - 6) / 2, true) else some (5, (B - 3) / 2, true)
def kT16 (y : Nat) : Option (Nat × Nat × Bool) := some (3 * y / 2 + 4, 1, false)

theorem conv4_2 (B : Nat) (hB : 5 ≤ B) : Leads (K 4 B T2) (k4T2 B) := by
  rcases parity B with ⟨b, rfl | rfl⟩
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    rw [k4T2, ite_t (by omega)]
    exact halts_of (k4_e_T2 b) rfl (by tq)
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    rw [k4T2, ite_f (by omega), show (2 * (b + 2) + 1 - 5) / 2 = b by omega]
    have h : Reaches1 (K 4 (2 * (b + 2) + 1) T2) (Am 2 (b + 4) (Tl false)) :=
      of_rule (by omega) (k4_o_T2 (b + 1)) (by tq) (by tq)
    exact h.trans (restart4 b false)

theorem conv5_2 (B : Nat) (hB : 8 ≤ B) : Leads (K 5 B T2) (k5T2 B) := by
  rcases parity B with ⟨b, rfl | rfl⟩
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 4 := ⟨b - 4, by omega⟩
    rw [k5T2, ite_t (by omega), show (2 * (b + 4) - 8) / 2 = b by omega]
    exact of_rule (by omega) (k5_e_T2 b) (by tq) (by tq)
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    rw [k5T2, ite_f (by omega), show (2 * (b + 2) + 1 - 5) / 2 = b by omega]
    have h : Reaches1 (K 5 (2 * (b + 2) + 1) T2) (Am 3 (b + 4) (Tl false)) :=
      of_rule (by omega) (k5_o_T2 (b + 1)) (by tq) (by tq)
    exact h.trans (restart5 b false)

theorem conv4_13 (B : Nat) (hB : 3 ≤ B) : Leads (K 4 B T13) (k4T13 B) := by
  rcases parity B with ⟨b, rfl | rfl⟩
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [k4T13, ite_t (by omega)]
    exact halts_of (k4_e_T13 b) rfl (by tq)
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [k4T13, ite_f (by omega), show (2 * (b + 1) + 1 - 3) / 2 = b by omega]
    have h : Reaches1 (K 4 (2 * (b + 1) + 1) T13) (Am 2 (b + 4) (Tl true)) :=
      of_rule (by omega) (k4_o_T13 b) (by tq) (by simp only [Am, am_tail]; tq)
    exact h.trans (restart4 b true)

theorem conv5_13 (B : Nat) (hB : 6 ≤ B) : Leads (K 5 B T13) (k5T13 B) := by
  rcases parity B with ⟨b, rfl | rfl⟩
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 3 := ⟨b - 3, by omega⟩
    rw [k5T13, ite_t (by omega), show (2 * (b + 3) - 6) / 2 = b by omega]
    exact of_rule (by omega) (k5_e_T13 b) (by tq) (by tq)
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [k5T13, ite_f (by omega), show (2 * (b + 1) + 1 - 3) / 2 = b by omega]
    have h : Reaches1 (K 5 (2 * (b + 1) + 1) T13) (Am 3 (b + 4) (Tl true)) :=
      of_rule (by omega) (k5_o_T13 b) (by tq) (by simp only [Am, am_tail]; tq)
    exact h.trans (restart5 b true)

/-! ## The short phase after c = 1, t = 6 -/

def R3 : Tape := rep 3 [false, true] (Tl false)

theorem short (y : Nat) (hy : 6 ≤ y) : Reaches1 (W y 3 R3) (Ph (3 * y / 2 + 4) 1 false) := by
  rcases parity y with ⟨r, rfl | rfl⟩
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
    have h1 := wrun_even (s + 1) 2 R3
    have h2 := end2 (3 * s) 1 (Tl false)
    rw [show 2 + 3 * (s + 1) + 1 = 3 * s + 6 by omega, show 2 * (s + 1) + 2 = 2 * (s + 2) by omega] at h1
    rw [show 3 * s + 10 = 3 * (2 * (s + 2)) / 2 + 4 by omega] at h2
    exact h1.then h2
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have h1 := wrun_odd (s + 1) 2 R3
    have h2 := end1 (3 * s) 1 (Tl false)
    rw [show 2 + 3 * (s + 1) + 1 = 3 * s + 6 by omega] at h1
    rw [show 3 * s + 8 = 3 * (2 * (s + 1) + 1) / 2 + 4 by omega] at h2
    exact h1.then h2

theorem conv4_16 (B : Nat) (hB : 6 ≤ B) : Leads (K 4 B T16) (kT16 B) := by
  rcases parity B with ⟨b, rfl | rfl⟩
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 3 := ⟨b - 3, by omega⟩
    have h : Reaches1 (K 4 (2 * (b + 3)) T16) (W (2 * (b + 3)) 3 R3) :=
      of_rule (by omega) (k4_e_T16 b) (by tq) (by tq)
    exact h.trans (short _ (by omega))
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 3 := ⟨b - 3, by omega⟩
    have h : Reaches1 (K 4 (2 * (b + 3) + 1) T16) (W (2 * (b + 3) + 1) 3 R3) :=
      of_rule (by omega) (k4_o_T16 b) (by tq) (by tq)
    exact h.trans (short _ (by omega))

theorem conv5_16 (B : Nat) (hB : 6 ≤ B) : Leads (K 5 B T16) (kT16 (B + 1)) := by
  rcases parity B with ⟨b, rfl | rfl⟩
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 3 := ⟨b - 3, by omega⟩
    have h : Reaches1 (K 5 (2 * (b + 3)) T16) (W (2 * (b + 3) + 1) 3 R3) :=
      of_rule (by omega) (k5_e_T16 b) (by tq) (by tq)
    exact h.trans (short _ (by omega))
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 3 := ⟨b - 3, by omega⟩
    have h : Reaches1 (K 5 (2 * (b + 3) + 1) T16) (W (2 * (b + 3) + 1 + 1) 3 R3) :=
      of_rule (by omega) (k5_o_T16 b) (by tq) (by tq)
    exact h.trans (short _ (by omega))

/-! ## The map on phase configurations -/

/-- The phase configuration reached from `Ph x c six`, or `none` for a halt. -/
def next (x c : Nat) (six : Bool) : Option (Nat × Nat × Bool) :=
  match c, six with
  | c + 2, six => some (3 * x / 2 + 7, c, six)
  | 0, six => if x % 2 = 0 then k4T2 (3 * (x / 2) + 7 + tl six) else k5T2 (3 * (x / 2) + 7 + tl six)
  | 1, false => if x % 2 = 0 then k4T13 (3 * (x / 2) + 7) else k5T13 (3 * (x / 2) + 7)
  | 1, true => if x % 2 = 0 then kT16 (3 * (x / 2) + 7) else kT16 (3 * (x / 2) + 8)

theorem ph0 (x : Nat) (six : Bool) : Ph x 0 six = W x (5 + tl six + 1) T2 := by cases six <;> rfl
theorem ph1f (x : Nat) : Ph x 1 false = W x (5 + 1) T13 := rfl
theorem ph1t (x : Nat) : Ph x 1 true = W x (5 + 1) T16 := rfl

/-- **The reset table and the step together: `Ph x c six` leads to `next x c six`, for every x ≥ 1.** -/
theorem next_spec (x c : Nat) (six : Bool) (hx : 1 ≤ x) : Leads (Ph x c six) (next x c six) := by
  match c, six with
  | c + 2, six =>
    obtain ⟨x, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    exact step_rule x c (Tl six)
  | 0, six =>
    rcases parity x with ⟨r, rfl | rfl⟩
    · obtain ⟨r, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      simp only [next]
      rw [ite_t (by omega), show 3 * (2 * (r + 1) / 2) + 7 + tl six = 5 + tl six + 3 * r + 1 + 4 by omega, ph0]
      have h := (wrun_even r (5 + tl six) T2).then (tend2_2 _)
      exact Leads.pre h.r0 (conv4_2 _ (by omega))
    · simp only [next]
      rw [ite_f (by omega), show 3 * ((2 * r + 1) / 2) + 7 + tl six = 5 + tl six + 3 * r + 1 + 1 by omega, ph0]
      have h := (wrun_odd r (5 + tl six) T2).then (tend1_2 _)
      exact Leads.pre h.r0 (conv5_2 _ (by cases six <;> simp [tl] <;> omega))
  | 1, false =>
    rcases parity x with ⟨r, rfl | rfl⟩
    · obtain ⟨r, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      simp only [next]
      rw [ite_t (by omega), show 3 * (2 * (r + 1) / 2) + 7 = 5 + 3 * r + 1 + 4 by omega, ph1f]
      have h := (wrun_even r 5 T13).then (tend2_13 _)
      exact Leads.pre h.r0 (conv4_13 _ (by omega))
    · simp only [next]
      rw [ite_f (by omega), show 3 * ((2 * r + 1) / 2) + 7 = 5 + 3 * r + 1 + 1 by omega, ph1f]
      have h := (wrun_odd r 5 T13).then (tend1_13 _)
      exact Leads.pre h.r0 (conv5_13 _ (by omega))
  | 1, true =>
    rcases parity x with ⟨r, rfl | rfl⟩
    · obtain ⟨r, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      simp only [next]
      rw [ite_t (by omega), show 3 * (2 * (r + 1) / 2) + 7 = 5 + 3 * r + 1 + 4 by omega, ph1t]
      have h := (wrun_even r 5 T16).then (tend2_16 _)
      exact Leads.pre h.r0 (conv4_16 _ (by omega))
    · simp only [next]
      rw [ite_f (by omega), show 3 * ((2 * r + 1) / 2) + 8 = 5 + 3 * r + 1 + 1 + 1 by omega, ph1t]
      have h := (wrun_odd r 5 T16).then (tend1_16 _)
      exact Leads.pre h.r0 (conv5_16 _ (by omega))

theorem next_pos (x c : Nat) (six : Bool) (y c' : Nat) (six' : Bool) (h : next x c six = some (y, c', six')) :
    1 ≤ y := by
  match c, six with
  | c + 2, six => simp only [next, Option.some.injEq, Prod.mk.injEq] at h; omega
  | 0, six =>
    simp only [next, k4T2, k5T2] at h
    split at h <;> split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;> omega
  | 1, false =>
    simp only [next, k4T13, k5T13] at h
    split at h <;> split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;> omega
  | 1, true =>
    simp only [next, kT16] at h
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> omega

/-! ## The run from blank tape -/

set_option maxRecDepth 100000 in
/-- Blank tape reaches S_3(4, 4) at step 388. -/
theorem start : steps 388 init = some (Ph 4 4 false) := rfl

/-- The orbit of (4, 4, t = 3) under `next`. -/
def orbit : Nat → Option (Nat × Nat × Bool)
  | 0 => some (4, 4, false)
  | i + 1 => match orbit i with
    | none => none
    | some (x, c, six) => next x c six

theorem orbit_pos (i : Nat) : ∀ x c six, orbit i = some (x, c, six) → 1 ≤ x := by
  cases i with
  | zero => intro x c six h; simp only [orbit, Option.some.injEq, Prod.mk.injEq] at h; omega
  | succ i =>
    intro x c six h
    simp only [orbit] at h
    split at h
    · cases h
    · exact next_pos _ _ _ _ _ _ h

theorem orbit_run (i : Nat) : ∀ x c six, orbit i = some (x, c, six) →
    ∃ s, i ≤ s ∧ steps s init = some (Ph x c six) := by
  induction i with
  | zero =>
    intro x c six h
    simp only [orbit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨388, by omega, start⟩
  | succ i ih =>
    intro x c six h
    simp only [orbit] at h
    cases ho : orbit i with
    | none => rw [ho] at h; cases h
    | some p =>
      obtain ⟨x0, c0, s0⟩ := p
      simp only [ho] at h
      obtain ⟨s, hs, hr⟩ := ih x0 c0 s0 ho
      have hl := next_spec x0 c0 s0 (orbit_pos i x0 c0 s0 ho)
      rw [h] at hl
      obtain ⟨m, hm, hr'⟩ := hl
      exact ⟨s + m, by omega, steps_seq H130861.trans hr hr'⟩

/-- **The machine halts from blank tape exactly when the orbit of (4, 4, 3) under `next` reaches `none`.** -/
theorem halts_iff : HaltsFromBlank ↔ ∃ i, orbit i = none := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    have hall : ∀ i, ∃ p, orbit i = some p := by
      intro i
      cases h : orbit i with
      | none => exact absurd ⟨i, h⟩ hno
      | some p => exact ⟨p, rfl⟩
    apply not_halts_of_forall H130861.trans _ hh
    apply forall_of_unbounded H130861.trans (fun n => ∃ c, steps n init = some c)
    · intro n
      obtain ⟨⟨x, c, six⟩, h⟩ := hall n
      obtain ⟨m, hm, hr⟩ := orbit_run n x c six h
      exact ⟨m, hm, _, hr⟩
    · intro m hm; exact hm
  · intro ⟨i, hi⟩
    induction i with
    | zero => simp [orbit] at hi
    | succ i ih =>
      simp only [orbit] at hi
      cases ho : orbit i with
      | none => exact ih ho
      | some p =>
        obtain ⟨x, c, six⟩ := p
        simp only [ho] at hi
        obtain ⟨s, -, hr⟩ := orbit_run i x c six ho
        have hl := next_spec x c six (orbit_pos i x c six ho)
        rw [hi] at hl
        obtain ⟨m, c', h₁, h₂⟩ := hl
        exact ⟨s + m, c', steps_seq H130861.trans hr h₁, h₂⟩

theorem orbit_none_succ (i : Nat) (h : orbit i = none) : orbit (i + 1) = none := by
  simp [orbit, h]

theorem orbit_some_of_le {i k : Nat} (hik : i ≤ k) (h : (orbit k).isSome = true) : (orbit i).isSome = true := by
  induction hik with
  | refl => exact h
  | step _ ih =>
    apply ih
    cases ho : orbit _ with
    | none => rw [orbit_none_succ _ ho] at h; cases h
    | some _ => rfl

/-- Phases 0, 1 and 2 and their resets: the orbit has no `none` in its first 585 terms, and term 585 is
S_3(6, c) with c > 10^101 (evaluated by compiled code: `native_decide`). -/
def phase3 : Option (Nat × Nat × Bool) → Bool
  | some (x, c, six) => x == 6 && six == false && decide (10 ^ 101 < c) && c % 2 == 1
  | none => false

theorem orbit_585 : (orbit 585).isSome = true ∧ phase3 (orbit 585) = true := by
  native_decide

/-- So the run from blank tape does not halt in phases 0 to 2. -/
theorem no_halt_585 (i : Nat) (hi : i ≤ 585) : orbit i ≠ none := by
  have h := orbit_some_of_le hi orbit_585.1
  intro hn; rw [hn] at h; cases h

end H130861
