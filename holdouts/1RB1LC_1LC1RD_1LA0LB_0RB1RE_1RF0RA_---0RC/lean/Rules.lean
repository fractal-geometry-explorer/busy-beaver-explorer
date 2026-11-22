import Phases

/-!
# 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC: the rules on A(a, b)

A visit is the tape `A(a, b) := 0^∞ 1^a 0 C> 1^b 0^∞` (a ≥ 1).  In frames of `Phases.lean` it is `vis a b`:
`Ph.b (a - 2) 1 (b - 1)` (three steps before the visit) for a ≥ 2, `Ph.d 0 2 (b - 1)` (five steps before) for a = 1.

`op` is the map of the bbchallenge wiki page (analysis by Racheline) on the visits:

    A(a, 3)                    -> HALT                 a >= 2
    A(a, 2)                    -> A(a - 3, 7)          a >= 4
    A(a, b),   a >= b >= 4     -> A(a - b + 1, 2b + 3)
    A(a, a + 1)                -> A(4, 2a + 4)         a >= 3
    A(a, a + 2)                -> A(1, 2a + 7)         a >= 2
    A(a, b),   a even, b >= a + 3 -> A(2a + 4, b - a - 1)
    A(a, a + 3), a odd         -> A(2a + 1, 9)
    A(a, b),   a odd, b >= a + 4  -> A(2a + 3, b - a)

Each rule is proved here for all sizes as a run of the frame map `next` (`op_step`: `Reach` means at least one
frame), from two loop lemmas (`loop_ba`, `loop_cd`) and single cases of `next`, all checked by the kernel.
`dom` (a ≥ 1, b ≥ 2, and not A(1, 2), A(1, 3), A(2, 2), A(3, 2)) holds at A(2, 9) and is kept by every rule.

**`halts_iff_rules`: the machine halts from blank tape if and only if the orbit of (2, 9) under `op` reaches a
pair with b = 3.**  `no_b3`: by `native_decide`, not in the first 10^8 visits (about 6.8·10^23 machine steps by the
rules' step counts of `py/rules.py`; `c/abrun.c` follows the same orbit much further).

`op_sum`: every rule adds at least 2 to a + b (3 or 4 for all but the rare restarts and short rule), so
`orbit_sum`: after k visits a + b ≥ 2k + 11.  With s = a + b as a clock, the rules are a doubling map on a / s:
the swap (a ≥ b) is a ↦ 2a - s + 1, the growing rules a ↦ 2a + 4 or 2a + 3.
-/

namespace H8084
open TM

/-! ## Runs of the frame map -/

theorem iter_add : ∀ m n p, iter (m + n) p = (iter m p).bind (iter n)
  | 0, n, p => by simp [iter]
  | m + 1, n, p => by
    rw [Nat.add_right_comm]
    simp only [iter]
    cases next p with
    | none => rfl
    | some q => simp only [Option.bind_some]; exact iter_add m n q

/-- `q` is reached from `p` after some number of frames (possibly none). -/
def R0 (p q : Ph) : Prop := ∃ k, iter k p = some q

/-- `q` is reached from `p` after at least one frame. -/
def Reach (p q : Ph) : Prop := ∃ k, 0 < k ∧ iter k p = some q

theorem R0.refl (p : Ph) : R0 p p := ⟨0, rfl⟩

theorem R0.tr {p q r : Ph} : R0 p q → R0 q r → R0 p r
  | ⟨m, h1⟩, ⟨n, h2⟩ => ⟨m + n, by rw [iter_add, h1, Option.bind_some, h2]⟩

theorem Reach.tr {p q r : Ph} : Reach p q → Reach q r → Reach p r
  | ⟨m, hm, h1⟩, ⟨n, _, h2⟩ => ⟨m + n, by omega, by rw [iter_add, h1, Option.bind_some, h2]⟩

theorem Reach.tr0 {p q r : Ph} : Reach p q → R0 q r → Reach p r
  | ⟨m, hm, h1⟩, ⟨n, h2⟩ => ⟨m + n, by omega, by rw [iter_add, h1, Option.bind_some, h2]⟩

theorem R0.trR {p q r : Ph} : R0 p q → Reach q r → Reach p r
  | ⟨m, h1⟩, ⟨n, hn, h2⟩ => ⟨m + n, by omega, by rw [iter_add, h1, Option.bind_some, h2]⟩

theorem Reach.r0 {p q : Ph} : Reach p q → R0 p q
  | ⟨k, _, h⟩ => ⟨k, h⟩

/-- One frame. -/
theorem nx {p q : Ph} (h : next p = some q) : Reach p q := ⟨1, by omega, by simp [iter, h]⟩

theorem Reach.eq {p q q' : Ph} (h : Reach p q) (e : q = q') : Reach p q' := e ▸ h

theorem R0.eq {p q q' : Ph} (h : R0 p q) (e : q = q') : R0 p q' := e ▸ h

/-- `1^(L+k) B 10 10^j 1^(r+k)` runs to `1^L B 10 10^(j+k) 1^r`, k pairs `b → a → b`, while the right block
stays at least 4. -/
theorem loop_ba : ∀ k l j r, 3 ≤ r → R0 (.b (l + k) j (r + k)) (.b l (j + k) r)
  | 0, l, j, r, _ => R0.refl _
  | k + 1, l, j, r, hr => by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
    have e1 : Ph.b (l + (k + 1)) j (s + 3 + (k + 1)) = Ph.b ((l + k) + 1) j ((s + k) + 4) := by
      congr 1 <;> omega
    rw [e1]
    refine ((nx (q := .a (l + k + 1) (j + 1) (s + k + 1)) rfl).tr
      (nx (q := .b (l + k) (j + 1) (s + k + 3)) rfl)).r0.tr ?_
    have h := loop_ba k l (j + 1) (s + 3) (by omega)
    rw [show s + 3 + k = s + k + 3 by omega, show j + 1 + k = j + (k + 1) by omega] at h
    exact h

/-- `1^l 0 C 0 10^(j+2k+1) 1^(r+1)` runs to `1^(l+4k) 0 C 0 10^(j+1) 1^(r+1)`, k pairs `c → d → c`. -/
theorem loop_cd : ∀ k l j r, R0 (.c l (j + 2 * k + 1) (r + 1)) (.c (l + 4 * k) (j + 1) (r + 1))
  | 0, l, j, r => R0.refl _
  | k + 1, l, j, r => by
    have e1 : Ph.c l (j + 2 * (k + 1) + 1) (r + 1) = Ph.c l ((j + 2 * k + 2) + 1) (r + 1) := by
      congr 1
    rw [e1]
    refine ((nx (q := .d l (j + 2 * k + 3) (r + 1)) rfl).tr
      (nx (q := .c (l + 4) (j + 2 * k + 1) (r + 1)) rfl)).r0.tr ?_
    exact (loop_cd k (l + 4) j r).eq (by congr 1; omega)

/-! ## The visits and the rules -/

/-- The frame of the visit `A(a, b)`. -/
def vis : Nat → Nat → Ph
  | a + 2, b => .b a 1 (b - 1)
  | _, b => .d 0 2 (b - 1)

/-- The wiki's map; `none` at b = 3 (the halt). -/
def op : Nat × Nat → Option (Nat × Nat)
  | (a, b) =>
    if b = 3 then none
    else if b = 2 then some (a - 3, 7)
    else if b ≤ a then some (a - b + 1, 2 * b + 3)
    else if b = a + 1 then some (4, 2 * a + 4)
    else if b = a + 2 then some (1, 2 * a + 7)
    else if a % 2 = 0 then some (2 * a + 4, b - a - 1)
    else if b = a + 3 then some (2 * a + 1, 9)
    else some (2 * a + 3, b - a)

/-- Where the rules apply. -/
def dom (a b : Nat) : Prop := 1 ≤ a ∧ 2 ≤ b ∧ (b ≠ 2 ∨ 4 ≤ a) ∧ (b ≠ 3 ∨ 2 ≤ a)

theorem ss {a b c d : Nat} (h1 : a = c) (h2 : b = d) : some (a, b) = some (c, d) := by subst h1; subst h2; rfl

/-- `A(n + 4, 2) → A(n + 1, 7)`. -/
theorem r_b2 (n : Nat) : Reach (vis (n + 4) 2) (vis (n + 1) 7) := by
  show Reach (.b (n + 2) 1 1) _
  refine ((nx (q := .e (n + 2) 3) rfl).tr (nx (q := .b n 0 7) rfl)).tr ((nx (q := .a n 1 4) rfl).tr ?_)
  cases n with
  | zero => exact nx rfl
  | succ n => exact nx rfl

/-- `A(c + 4 + d, c + 4) → A(d + 1, 2c + 11)`: a ≥ b ≥ 4. -/
theorem r_ge (c d : Nat) : Reach (vis (d + c + 4) (c + 4)) (vis (d + 1) (2 * c + 11)) := by
  show Reach (.b (d + c + 2) 1 (c + 3)) _
  have h := loop_ba c (d + 2) 1 3 (by omega)
  rw [show d + 2 + c = d + c + 2 by omega, show 3 + c = c + 3 by omega, show 1 + c = c + 1 by omega] at h
  refine h.trR ?_
  refine ((nx (q := .f (d + 2) (c + 1 + 1)) rfl).tr (nx (q := .e (d + 2) (c + 5)) rfl)).tr ?_
  refine (nx (q := .b d 0 (2 * c + 11)) ?_).tr ((nx (q := .a d 1 (2 * c + 8)) rfl).tr ?_)
  · show some (Ph.b d 0 (2 * (c + 4) + 3)) = _; congr 2 <;> omega
  cases d with
  | zero => exact nx rfl
  | succ d => exact nx rfl

/-- `A(n + 3, n + 4) → A(4, 2n + 10)`. -/
theorem r_p1 (n : Nat) : Reach (vis (n + 3) (n + 4)) (vis 4 (2 * n + 10)) := by
  show Reach (.b (n + 1) 1 (n + 3)) _
  have h := loop_ba n 1 1 3 (by omega)
  rw [show 1 + n = n + 1 by omega, show 3 + n = n + 3 by omega] at h
  refine h.trR ?_
  refine ((nx (q := .f 1 (n + 1 + 1)) rfl).tr (nx (q := .e 1 (n + 5)) rfl)).tr ?_
  refine (nx (q := .d 0 1 (2 * n + 11)) ?_).tr (nx (q := .b 2 1 (2 * n + 9)) rfl)
  show some (Ph.d 0 1 (2 * (n + 4) + 3)) = _; congr 2 <;> omega

/-- `A(n + 2, n + 4) → A(1, 2n + 11)`. -/
theorem r_p2 (n : Nat) : Reach (vis (n + 2) (n + 4)) (vis 1 (2 * n + 11)) := by
  show Reach (.b n 1 (n + 3)) _
  have h := loop_ba n 0 1 3 (by omega)
  rw [show 0 + n = n by omega, show 3 + n = n + 3 by omega, show 1 + n = n + 1 by omega] at h
  refine h.trR ?_
  refine ((nx (q := .f 0 (n + 1 + 1)) rfl).tr (nx (q := .e 0 (n + 5)) rfl)).tr ?_
  refine (nx (q := .d 0 0 (2 * n + 11)) ?_).tr ?_
  · show some (Ph.d 0 0 (2 * (n + 4) + 3)) = _; congr 2 <;> omega
  refine ((nx (q := .a 1 0 (2 * n + 9)) rfl).tr (nx (q := .b 0 0 (2 * n + 11)) rfl)).tr ?_
  exact (nx (q := .a 0 1 (2 * n + 8)) rfl).tr (nx rfl)

/-- `A(2m + 2, s + 2m + 5) → A(4m + 8, s + 2)`: a even, b ≥ a + 3. -/
theorem r_de (m s : Nat) : Reach (vis (2 * m + 2) (s + 2 * m + 5)) (vis (4 * m + 8) (s + 2)) := by
  show Reach (.b (2 * m) 1 (s + 2 * m + 4)) (.b (4 * m + 6) 1 (s + 1))
  have h := loop_ba (2 * m) 0 1 (s + 4) (by omega)
  rw [show 0 + 2 * m = 2 * m by omega, show s + 4 + 2 * m = s + 2 * m + 4 by omega] at h
  refine h.trR ?_
  refine ((nx (q := .a 0 (1 + 2 * m + 1) (s + 1)) rfl).tr (nx (q := .d 0 (2 * m + 3) (s + 3)) ?_)).tr ?_
  · show some (Ph.d 0 (1 + 2 * m + 1 + 1) (s + 3)) = _; congr 2 <;> omega
  refine (nx (q := .c 4 (2 * m + 1) (s + 3)) rfl).tr0 ?_
  have hc := loop_cd m 4 0 (s + 2)
  rw [Nat.zero_add] at hc
  refine hc.tr ?_
  refine ((nx (q := .d (4 + 4 * m) 1 (s + 3)) rfl).tr (nx (q := .b (4 * m + 6) 1 (s + 1)) ?_)).r0
  show some (Ph.b (4 + 4 * m + 2) 1 (s + 1)) = _; congr 2 <;> omega

/-- `A(2m + 3, s + 2m + 7) → A(4m + 9, s + 4)`: a ≥ 3 odd, b ≥ a + 4. -/
theorem r_do (m s : Nat) : Reach (vis (2 * m + 3) (s + 2 * m + 7)) (vis (4 * m + 9) (s + 4)) := by
  show Reach (.b (2 * m + 1) 1 (s + 2 * m + 6)) (.b (4 * m + 7) 1 (s + 3))
  have h := loop_ba (2 * m + 1) 0 1 (s + 5) (by omega)
  rw [show 0 + (2 * m + 1) = 2 * m + 1 by omega, show s + 5 + (2 * m + 1) = s + 2 * m + 6 by omega] at h
  refine h.trR ?_
  refine ((nx (q := .a 0 (1 + (2 * m + 1) + 1) (s + 2)) rfl).tr (nx (q := .d 0 (2 * m + 4) (s + 4)) ?_)).tr ?_
  · show some (Ph.d 0 (1 + (2 * m + 1) + 1 + 1) (s + 4)) = _; congr 2 <;> omega
  refine (nx (q := .c 4 (1 + 2 * m + 1) (s + 3 + 1)) ?_).tr ?_
  · show some (Ph.c 4 (2 * m + 1 + 1) (s + 3 + 1)) = _; congr 2 <;> omega
  refine (loop_cd m 4 1 (s + 3)).trR ?_
  refine ((nx (q := .d (4 + 4 * m) 2 (s + 4)) rfl).tr (nx (q := .c (4 * m + 8) 0 (s + 4)) ?_)).tr ?_
  · show some (Ph.c (4 + 4 * m + 4) 0 (s + 4)) = _; congr 2 <;> omega
  refine ((nx (q := .d (4 * m + 8) 0 (s + 4)) rfl).tr (nx (q := .a (4 * m + 9) 0 (s + 2)) rfl)).tr ?_
  refine ((nx (q := .b (4 * m + 8) 0 (s + 4)) rfl).tr (nx (q := .a (4 * m + 8) 1 (s + 1)) rfl)).tr ?_
  exact nx rfl

/-- `A(1, s + 5) → A(5, s + 4)`. -/
theorem r_do1 (s : Nat) : Reach (vis 1 (s + 5)) (vis 5 (s + 4)) := by
  show Reach (.d 0 2 (s + 4)) (.b 3 1 (s + 3))
  refine ((nx (q := .c 4 0 (s + 4)) rfl).tr (nx (q := .d 4 0 (s + 4)) rfl)).tr ?_
  refine ((nx (q := .a 5 0 (s + 2)) rfl).tr (nx (q := .b 4 0 (s + 4)) rfl)).tr ?_
  exact (nx (q := .a 4 1 (s + 1)) rfl).tr (nx rfl)

/-- `A(2m + 3, 2m + 6) → A(4m + 7, 9)`: a ≥ 3 odd, b = a + 3. -/
theorem r_p3 (m : Nat) : Reach (vis (2 * m + 3) (2 * m + 6)) (vis (4 * m + 7) 9) := by
  show Reach (.b (2 * m + 1) 1 (2 * m + 5)) (.b (4 * m + 5) 1 8)
  have h := loop_ba (2 * m + 1) 0 1 4 (by omega)
  rw [show 0 + (2 * m + 1) = 2 * m + 1 by omega, show 4 + (2 * m + 1) = 2 * m + 5 by omega] at h
  refine h.trR ?_
  refine ((nx (q := .a 0 (1 + (2 * m + 1) + 1) 1) rfl).tr (nx (q := .d 0 (2 * m + 4) 3) ?_)).tr ?_
  · show some (Ph.d 0 (1 + (2 * m + 1) + 1 + 1) 3) = _; congr 2 <;> omega
  refine (nx (q := .c 4 (1 + 2 * m + 1) (2 + 1)) ?_).tr ?_
  · show some (Ph.c 4 (2 * m + 1 + 1) (2 + 1)) = _; congr 2 <;> omega
  refine (loop_cd m 4 1 2).trR ?_
  refine ((nx (q := .d (4 + 4 * m) 2 3) rfl).tr (nx (q := .c (4 * m + 8) 0 3) ?_)).tr ?_
  · show some (Ph.c (4 + 4 * m + 4) 0 3) = _; congr 2 <;> omega
  refine ((nx (q := .d (4 * m + 8) 0 3) rfl).tr (nx (q := .a (4 * m + 9) 0 1) rfl)).tr ?_
  refine ((nx (q := .b (4 * m + 8) 0 3) rfl).tr (nx (q := .f (4 * m + 8) 1) rfl)).tr ?_
  refine ((nx (q := .e (4 * m + 8) 4) rfl).tr (nx (q := .b (4 * m + 6) 0 9) rfl)).tr ?_
  exact (nx (q := .a (4 * m + 6) 1 6) rfl).tr (nx rfl)

/-- `A(1, 4) → A(3, 9)`. -/
theorem r_p3_1 : Reach (vis 1 4) (vis 3 9) := ⟨9, by omega, rfl⟩

/-- The run from blank tape reaches `A(2, 9)`. -/
theorem start : R0 (.e 1 0) (vis 2 9) := ⟨10, rfl⟩

/-- `A(n + 2, 3)` halts. -/
theorem vis_halt (n : Nat) : next (vis (n + 2) 3) = none := rfl

/-- Every rule: from a visit in the domain with b ≠ 3, `op` gives the next visit, again in the domain. -/
theorem op_step (a b : Nat) (hd : dom a b) (h3 : b ≠ 3) :
    ∃ a' b', op (a, b) = some (a', b') ∧ dom a' b' ∧ Reach (vis a b) (vis a' b') := by
  obtain ⟨ha, hb, h2, -⟩ := hd
  simp only [op, if_neg h3]
  by_cases e2 : b = 2
  · subst e2
    obtain ⟨n, rfl⟩ : ∃ n, a = n + 4 := ⟨a - 4, by omega⟩
    refine ⟨n + 1, 7, ss (by omega) rfl, by simp only [dom]; omega, r_b2 n⟩
  rw [if_neg e2]
  by_cases e3 : b ≤ a
  · rw [if_pos e3]
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 4 := ⟨b - 4, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, a = d + c + 4 := ⟨a - c - 4, by omega⟩
    refine ⟨d + 1, 2 * c + 11, ss (by omega) (by omega), by simp only [dom]; omega,
      r_ge c d⟩
  rw [if_neg e3]
  by_cases e4 : b = a + 1
  · rw [if_pos e4]; subst e4
    obtain ⟨n, rfl⟩ : ∃ n, a = n + 3 := ⟨a - 3, by omega⟩
    exact ⟨4, 2 * n + 10, ss (by omega) (by omega), by simp only [dom]; omega,
      r_p1 n⟩
  rw [if_neg e4]
  by_cases e5 : b = a + 2
  · rw [if_pos e5]; subst e5
    obtain ⟨n, rfl⟩ : ∃ n, a = n + 2 := ⟨a - 2, by omega⟩
    exact ⟨1, 2 * n + 11, ss (by omega) (by omega), by simp only [dom]; omega,
      r_p2 n⟩
  rw [if_neg e5]
  by_cases e6 : a % 2 = 0
  · rw [if_pos e6]
    obtain ⟨m, rfl⟩ : ∃ m, a = 2 * m + 2 := ⟨a / 2 - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, b = s + 2 * m + 5 := ⟨b - 2 * m - 5, by omega⟩
    exact ⟨4 * m + 8, s + 2, ss (by omega) (by omega), by simp only [dom]; omega,
      r_de m s⟩
  rw [if_neg e6]
  by_cases e7 : b = a + 3
  · rw [if_pos e7]; subst e7
    by_cases a1 : a = 1
    · subst a1; exact ⟨3, 9, rfl, by simp only [dom]; omega, r_p3_1⟩
    obtain ⟨m, rfl⟩ : ∃ m, a = 2 * m + 3 := ⟨(a - 3) / 2, by omega⟩
    exact ⟨4 * m + 7, 9, ss (by omega) (by omega), by simp only [dom]; omega,
      r_p3 m⟩
  rw [if_neg e7]
  by_cases a1 : a = 1
  · subst a1
    obtain ⟨s, rfl⟩ : ∃ s, b = s + 5 := ⟨b - 5, by omega⟩
    exact ⟨5, s + 4, ss (by omega) (by omega), by simp only [dom]; omega, r_do1 s⟩
  obtain ⟨m, rfl⟩ : ∃ m, a = 2 * m + 3 := ⟨(a - 3) / 2, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, b = s + 2 * m + 7 := ⟨b - 2 * m - 7, by omega⟩
  exact ⟨4 * m + 9, s + 4, ss (by omega) (by omega), by simp only [dom]; omega,
    r_do m s⟩

/-! ## Halting -/

/-- `k` steps of `op`. -/
def opIter : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, x => some x
  | k + 1, x => (op x).bind (opIter k)

theorem opIter_succ : ∀ k x y, opIter k x = some y → opIter (k + 1) x = op y
  | 0, x, y, h => by simp only [opIter, Option.some.injEq] at h; subst h; simp [opIter]
  | k + 1, x, y, h => by
    simp only [opIter] at h ⊢
    cases hx : op x with
    | none => simp [hx] at h
    | some z => simp only [hx, Option.bind_some] at h ⊢; exact opIter_succ k z y h

theorem opIter_none : ∀ k x, opIter k x = none → opIter (k + 1) x = none
  | 0, _, h => by simp [opIter] at h
  | k + 1, x, h => by
    show (op x).bind (opIter (k + 1)) = none
    change (op x).bind (opIter k) = none at h
    cases hx : op x with
    | none => rfl
    | some z => rw [hx] at h; exact opIter_none k z h

/-- Along the orbit of (2, 9), as long as b ≠ 3: the pair is in the domain and its frame is reached from `e 1 0`
after at least `k` frames. -/
theorem orbit (k : Nat) (a b : Nat) (h : opIter k (2, 9) = some (a, b)) :
    dom a b ∧ ∃ n, k ≤ n ∧ iter n (.e 1 0) = some (vis a b) := by
  induction k generalizing a b with
  | zero =>
    simp only [opIter, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨n, hn⟩ := start
    exact ⟨by simp only [dom]; omega, n, Nat.zero_le _, hn⟩
  | succ k ih =>
    cases hk : opIter k (2, 9) with
    | none =>
      have : opIter (k + 1) (2, 9) = none := opIter_none k _ hk
      rw [this] at h; exact absurd h (by simp)
    | some y =>
      obtain ⟨a0, b0⟩ := y
      obtain ⟨hd, n, hn, hi⟩ := ih a0 b0 hk
      rw [opIter_succ k _ _ hk] at h
      by_cases h3 : b0 = 3
      · subst h3; simp [op] at h
      obtain ⟨a', b', ho, hd', m, hm, hr⟩ := op_step a0 b0 hd h3
      rw [ho, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hd', n + m, by omega, by rw [iter_add, hi, Option.bind_some, hr]⟩


/-! ## The sum a + b is a clock -/

/-- Every rule adds at least 2 to a + b (3 for the growing rules, 4 for the swap, 6 or 7 for the restarts, 2 for the
short rule), so a + b counts the visits: the orbit is a doubling map on a / (a + b) with a slowly growing modulus. -/
theorem op_sum (a b a' b' : Nat) (hd : dom a b) (h : op (a, b) = some (a', b')) : a + b + 2 ≤ a' + b' := by
  obtain ⟨ha, hb, h2, h3⟩ := hd
  simp only [op] at h
  repeat' split at h
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); omega)
    | exact absurd h (by simp)

theorem orbit_sum (k a b : Nat) (h : opIter k (2, 9) = some (a, b)) : 11 + 2 * k ≤ a + b := by
  induction k generalizing a b with
  | zero => simp only [opIter, Option.some.injEq, Prod.mk.injEq] at h; omega
  | succ k ih =>
    cases hk : opIter k (2, 9) with
    | none => rw [opIter_none k _ hk] at h; exact absurd h (by simp)
    | some y =>
      obtain ⟨a0, b0⟩ := y
      rw [opIter_succ k _ _ hk] at h
      have := op_sum a0 b0 a b (orbit k a0 b0 hk).1 h
      have := ih a0 b0 hk
      omega


theorem iter_none_after (p q : Ph) (k : Nat) (h : iter k p = some q) (hn : next q = none) :
    ∀ j, iter (k + 1 + j) p = none := by
  intro j
  rw [iter_add, iter_succ k p q h, hn]; rfl

/-- **The machine halts from blank tape if and only if the orbit of (2, 9) under the wiki's map `op` reaches a
pair (a, 3).** -/
theorem halts_iff_rules : HaltsFromBlank ↔ ∃ k a, opIter k (2, 9) = some (a, 3) := by
  rw [halts_iff]
  constructor
  · rintro ⟨k, p, hk, hn⟩
    apply Classical.byContradiction
    intro hno
    have hall : ∀ i, ∃ y, opIter i (2, 9) = some y := by
      intro i
      induction i with
      | zero => exact ⟨_, rfl⟩
      | succ i ih =>
        obtain ⟨⟨a, b⟩, hy⟩ := ih
        rw [opIter_succ i _ _ hy]
        have hb : b ≠ 3 := fun e => hno ⟨i, a, e ▸ hy⟩
        obtain ⟨a', b', ho, -⟩ := op_step a b (orbit i a b hy).1 hb
        exact ⟨_, ho⟩
    obtain ⟨⟨a, b⟩, hy⟩ := hall (k + 1)
    obtain ⟨-, n, hn', hi⟩ := orbit (k + 1) a b hy
    have := iter_none_after _ _ k hk hn (n - (k + 1))
    rw [show k + 1 + (n - (k + 1)) = n by omega, hi] at this
    exact absurd this (by simp)
  · rintro ⟨k, a, h⟩
    obtain ⟨hd, n, -, hi⟩ := orbit k a 3 h
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by have := hd.2.2.2; omega⟩
    exact ⟨n, _, hi, vis_halt c⟩

/-! ## The first 10^8 visits -/

/-- The first `k` iterates of `op` from `x` have b ≠ 3 (and are defined). -/
def okOp : Nat → Nat × Nat → Bool
  | 0, _ => true
  | k + 1, x => match op x with
    | none => false
    | some y => okOp k y

theorem okOp_sound : ∀ k x, okOp k x = true → ∀ j, j < k → ∀ y, opIter j x = some y → y.2 ≠ 3
  | 0, _, _, j, hj, _, _ => absurd hj (Nat.not_lt_zero j)
  | k + 1, x, h, j, hj, y, hi => by
    simp only [okOp] at h
    cases hx : op x with
    | none => simp [hx] at h
    | some z =>
      simp only [hx] at h
      cases j with
      | zero =>
        simp only [opIter, Option.some.injEq] at hi; subst hi
        intro e
        obtain ⟨a, b⟩ := x
        simp only at e; subst e
        simp [op] at hx
      | succ j =>
        simp only [opIter, hx, Option.bind_some] at hi
        exact okOp_sound k z h j (by omega) y hi

/-- No b = 3 among the first 10^8 visits of the run from blank tape. -/
theorem no_b3 : ∀ j, j < 100000000 → ∀ y, opIter j (2, 9) = some y → y.2 ≠ 3 :=
  okOp_sound _ _ (by native_decide)

end H8084
