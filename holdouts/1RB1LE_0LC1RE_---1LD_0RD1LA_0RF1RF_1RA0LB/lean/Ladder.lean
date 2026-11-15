import Hits

/-!
# 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB: the ladder of levels as an odometer

Hand-written.  From the hits on one level (`Hits.lean`, for every block count):

* `level_run`: `y` hits in a row on a level, by induction on `y`, with naive counting functions (`advN`, `passN`,
  `costN`), and their closed forms (`advF`, `passF`, `costF`: whole turns of 16 hits are done by arithmetic);
* `stack_run`: the same for a list of levels (`Stack`), by induction on the list: every level passes on its share
  of the hits, the tape below the last level gets what is left (the levels are transparent);
* `front_run`: the front and the two visits per hit;
* `crun`, `hrun`: a simulator for a call on a finite tape, proved for every tape to the right of the call;
* `S`, `opAdv`, `opPeel`, `opUnpeel`, `opFinal`, `loop`: the accelerated run as a function, and `loop_sound`:
  if it returns `N` from a configuration reached from blank tape, the machine halts after `N` steps
  (`N + 1` in the bbchallenge count).
-/

namespace H23376

open TM

/-! ## Facts about the table -/

theorem forall_lt16 (P : Nat → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6)
    (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13) (h14 : P 14)
    (h15 : P 15) : ∀ p, p < 16 → P p := by
  intro p hp
  match p, hp with
  | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3 | 4, _ => exact h4
  | 5, _ => exact h5 | 6, _ => exact h6 | 7, _ => exact h7 | 8, _ => exact h8 | 9, _ => exact h9
  | 10, _ => exact h10 | 11, _ => exact h11 | 12, _ => exact h12 | 13, _ => exact h13 | 14, _ => exact h14
  | 15, _ => exact h15
  | n + 16, h => omega

/-- The kind of the next hit that a level at position `p` passes on. -/
def firstPass : Nat → Kind
  | 0 | 1 | 2 | 5 | 6 | 7 | 11 | 12 => .H
  | _ => .V

/-- What `level_run` needs of the tables, as one check. -/
def tabOK (p : Nat) : Bool :=
  decide (nxt p < 16) && (kindOf (nxt p) == (kindOf p).other) &&
    match passOf p with
    | none => firstPass (nxt p) == firstPass p
    | some k => (firstPass p == k) && (firstPass (nxt p) == k.other)

theorem tabOK_all : ∀ p, p < 16 → tabOK p = true := by decide

theorem nxt_lt {p : Nat} (hp : p < 16) : nxt p < 16 := by
  have := tabOK_all p hp
  simp only [tabOK, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1

theorem kind_nxt {p : Nat} (hp : p < 16) : kindOf (nxt p) = (kindOf p).other := by
  have := tabOK_all p hp
  simp only [tabOK, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.2

theorem fp_none {p : Nat} (hp : p < 16) (h : passOf p = none) : firstPass (nxt p) = firstPass p := by
  have := tabOK_all p hp
  simp only [tabOK, h, Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

theorem fp_some {p : Nat} (hp : p < 16) {k : Kind} (h : passOf p = some k) :
    firstPass p = k ∧ firstPass (nxt p) = k.other := by
  have := tabOK_all p hp
  simp only [tabOK, h, Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

/-! ## Many hits on one level -/

/-- Position and block count after `y` hits. -/
def advN : Nat → Nat → Nat → Nat × Nat
  | p, j, 0 => (p, j)
  | p, j, y + 1 => advN (nxt p) (j + inc p) y

/-- The number of hits passed on among the next `y`. -/
def passN : Nat → Nat → Nat
  | _, 0 => 0
  | p, y + 1 => passN (nxt p) y + (if (passOf p).isSome then 1 else 0)

/-- Steps inside the level during the next `y` hits. -/
def costN : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | p, j, y + 1 => la p * (j + 1) + lb p + costN (nxt p) (j + inc p) y

theorem level_run : ∀ (y p j : Nat) (Y Y' : Tape) (m : Nat), p < 16 → Run (firstPass p) (passN p y) Y Y' m →
    Run (kindOf p) y (W p j Y) (W (advN p j y).1 (advN p j y).2 Y') (costN p j y + m)
  | 0, p, j, Y, Y', m, _, h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | y + 1, p, j, Y, Y', m, hp, h => by
    have hl := level_hit p j hp
    cases hpass : passOf p with
    | none =>
      have h' : Run (firstPass (nxt p)) (passN (nxt p) y) Y Y' m := by
        rw [fp_none hp hpass]
        simpa [passN, hpass] using h
      have ih := level_run y (nxt p) (j + inc p) Y Y' m (nxt_lt hp) h'
      rw [kind_nxt hp] at ih
      exact ⟨_, _, _, hl.1 hpass Y, ih, by simp only [costN]; omega⟩
    | some k =>
      have h1 : Run (firstPass p) (passN (nxt p) y + 1) Y Y' m := by
        simpa [passN, hpass] using h
      rw [(fp_some hp hpass).1] at h1
      obtain ⟨Y1, n1, n2, hh, hr, rfl⟩ := h1
      rw [← (fp_some hp hpass).2] at hr
      have ih := level_run y (nxt p) (j + inc p) Y1 Y' n2 (nxt_lt hp) hr
      rw [kind_nxt hp] at ih
      exact ⟨_, _, _, hl.2 k hpass Y Y1 n1 hh, ih, by simp only [costN]; omega⟩

/-! ## Closed forms: 16 hits are one turn -/

theorem advN_add : ∀ (a b p j : Nat), advN p j (a + b) = advN (advN p j a).1 (advN p j a).2 b
  | 0, b, p, j => by rw [Nat.zero_add]; rfl
  | a + 1, b, p, j => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [advN]
    exact advN_add a b _ _

theorem passN_add : ∀ (a b p j : Nat), passN p (a + b) = passN p a + passN (advN p j a).1 b
  | 0, b, p, j => by rw [Nat.zero_add]; simp [passN, advN]
  | a + 1, b, p, j => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [passN, advN]
    rw [passN_add a b (nxt p) (j + inc p)]
    omega

theorem costN_add : ∀ (a b p j : Nat),
    costN p j (a + b) = costN p j a + costN (advN p j a).1 (advN p j a).2 b
  | 0, b, p, j => by rw [Nat.zero_add]; simp [costN, advN]
  | a + 1, b, p, j => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [costN, advN]
    rw [costN_add a b (nxt p) (j + inc p)]
    omega

theorem adv16 : ∀ p, p < 16 → ∀ j, advN p j 16 = (p, j + 4) := by
  refine forall_lt16 (fun p => ∀ j, advN p j 16 = (p, j + 4)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    intro j <;> rfl

theorem pass16 : ∀ p, p < 16 → passN p 16 = 6 := by decide

/-- The sum of the step coefficients over the next `y` hits. -/
def sumLa : Nat → Nat → Nat
  | _, 0 => 0
  | p, y + 1 => la p + sumLa (nxt p) y

theorem costN_shift : ∀ (y p j : Nat), costN p (j + 1) y = costN p j y + sumLa p y
  | 0, _, _ => rfl
  | y + 1, p, j => by
    simp only [costN, sumLa]
    rw [show j + 1 + inc p = (j + inc p) + 1 by omega, costN_shift y (nxt p) (j + inc p), Nat.mul_succ (la p) (j + 1)]
    omega

theorem sumLa16 : ∀ p, p < 16 → sumLa p 16 = 1344 := by decide

theorem cost16 {p : Nat} (hp : p < 16) : ∀ j, costN p j 16 = 1344 * j + costN p 0 16
  | 0 => by omega
  | j + 1 => by
    rw [costN_shift, cost16 hp j, sumLa16 p hp]
    omega

theorem adv16q {p : Nat} (hp : p < 16) (j : Nat) : ∀ q, advN p j (16 * q) = (p, j + 4 * q)
  | 0 => rfl
  | q + 1 => by
    rw [show 16 * (q + 1) = 16 * q + 16 by omega, advN_add, adv16q hp j q]
    show advN p (j + 4 * q) 16 = _
    rw [adv16 p hp, show j + 4 * q + 4 = j + 4 * (q + 1) by omega]

theorem pass16q {p : Nat} (hp : p < 16) : ∀ q, passN p (16 * q) = 6 * q
  | 0 => rfl
  | q + 1 => by
    rw [show 16 * (q + 1) = 16 * q + 16 by omega, passN_add _ _ _ 0, adv16q hp 0 q, pass16q hp q]
    show _ + passN p 16 = _
    rw [pass16 p hp]
    omega

theorem tri (q : Nat) : (q + 1) * (q + 1 - 1) = q * (q - 1) + 2 * q := by
  cases q with
  | zero => rfl
  | succ k =>
    have e1 : (k + 1 + 1) * (k + 1) = (k + 1) * (k + 1) + (k + 1) := Nat.succ_mul (k + 1) (k + 1)
    have e2 : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := Nat.mul_succ (k + 1) k
    show (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1)
    omega

theorem cost16q {p : Nat} (hp : p < 16) (j : Nat) :
    ∀ q, costN p j (16 * q) = q * (1344 * j + costN p 0 16) + 2688 * (q * (q - 1))
  | 0 => by simp [costN]
  | q + 1 => by
    rw [show 16 * (q + 1) = 16 * q + 16 by omega, costN_add, adv16q hp j q, cost16q hp j q]
    show _ + costN p (j + 4 * q) 16 = _
    rw [cost16 hp (j + 4 * q)]
    have e1 : (q + 1) * (1344 * j + costN p 0 16) = q * (1344 * j + costN p 0 16) + (1344 * j + costN p 0 16) :=
      Nat.succ_mul _ _
    have e2 := tri q
    omega

def advF (p j y : Nat) : Nat × Nat := advN p (j + 4 * (y / 16)) (y % 16)

def passF (p y : Nat) : Nat := 6 * (y / 16) + passN p (y % 16)

def costF (p j y : Nat) : Nat :=
  (y / 16) * (1344 * j + costN p 0 16) + 2688 * ((y / 16) * (y / 16 - 1)) + costN p (j + 4 * (y / 16)) (y % 16)

theorem advF_eq {p : Nat} (hp : p < 16) (j y : Nat) : advN p j y = advF p j y := by
  have e : y = 16 * (y / 16) + y % 16 := (Nat.div_add_mod y 16).symm
  rw [e, advN_add, adv16q hp]
  unfold advF
  rw [← e]

theorem passF_eq {p : Nat} (hp : p < 16) (y : Nat) : passN p y = passF p y := by
  have e : y = 16 * (y / 16) + y % 16 := (Nat.div_add_mod y 16).symm
  rw [e, passN_add _ _ _ 0, adv16q hp, pass16q hp]
  unfold passF
  rw [← e]

theorem costF_eq {p : Nat} (hp : p < 16) (j y : Nat) : costN p j y = costF p j y := by
  have e : y = 16 * (y / 16) + y % 16 := (Nat.div_add_mod y 16).symm
  rw [e, costN_add, adv16q hp, cost16q hp]
  unfold costF
  rw [← e]

/-! ## A list of levels -/

/-- The levels `ls` (outermost first) in front of the tape `Y`. -/
def Stack : List (Nat × Nat) → Tape → Tape
  | [], Y => Y
  | (p, j) :: ls, Y => W p j (Stack ls Y)

/-- The levels after `y` hits, the number of hits that reach the tape below them, the steps inside the levels. -/
def advS : List (Nat × Nat) → Nat → List (Nat × Nat) × Nat × Nat
  | [], y => ([], y, 0)
  | (p, j) :: ls, y =>
    let r := advS ls (passF p y)
    (advF p j y :: r.1, r.2.1, costF p j y + r.2.2)

/-- The kind of the next hit that reaches the tape below the levels, when the next hit from above is of kind `t`. -/
def tailKind : Kind → List (Nat × Nat) → Kind
  | t, [] => t
  | _, (p, _) :: ls => tailKind (firstPass p) ls

/-- Every level is at a position of the table and expects the kind of hit the level above passes on. -/
def chainOK : Kind → List (Nat × Nat) → Bool
  | _, [] => true
  | t, (p, _) :: ls => decide (p < 16) && (kindOf p == t) && chainOK (firstPass p) ls

theorem stack_run : ∀ (ls : List (Nat × Nat)) (t : Kind) (y : Nat) (Y Y' : Tape) (m : Nat), chainOK t ls = true →
    Run (tailKind t ls) (advS ls y).2.1 Y Y' m → Run t y (Stack ls Y) (Stack (advS ls y).1 Y') ((advS ls y).2.2 + m)
  | [], t, y, Y, Y', m, _, h => by
    show Run t y Y Y' (0 + m)
    rw [Nat.zero_add]
    exact h
  | (p, j) :: ls, t, y, Y, Y', m, hc, h => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨hp, hk⟩, hc'⟩ := hc
    have ih := stack_run ls (firstPass p) (passF p y) Y Y' m hc' h
    have ih' : Run (firstPass p) (passN p y) (Stack ls Y) (Stack (advS ls (passF p y)).1 Y')
        ((advS ls (passF p y)).2.2 + m) := by
      rw [passF_eq hp]; exact ih
    have lr := level_run y p j _ _ _ hp ih'
    rw [hk, advF_eq hp, costF_eq hp] at lr
    show Run t y (W p j (Stack ls Y)) (W (advF p j y).1 (advF p j y).2 (Stack (advS ls (passF p y)).1 Y'))
      (costF p j y + (advS ls (passF p y)).2.2 + m)
    rw [Nat.add_assoc]
    exact lr

/-! ## The front -/

def fOf : Kind → List Bool
  | .H => fH
  | .V => fV

/-- Steps of the front per hit, the bounce visit included. -/
def fc : Kind → Nat
  | .H => 107
  | .V => 83

theorem front_hit : ∀ (t : Kind) {Y Y' : Tape} {n : Nat}, Hit t Y Y' n →
    steps (n + fc t) ⟨app (fOf t) Y, blank, .A⟩ = some ⟨app (fOf t.other) Y', blank, .A⟩
  | .H, _, _, _, h => frontH h
  | .V, _, _, _, h => frontV h

def fcN : Kind → Nat → Nat
  | _, 0 => 0
  | t, y + 1 => fc t + fcN t.other y

def flipN : Kind → Nat → Kind
  | t, 0 => t
  | t, y + 1 => flipN t.other y

theorem front_run : ∀ (y : Nat) (t : Kind) (Y Y' : Tape) (n : Nat), Run t y Y Y' n →
    steps (n + fcN t y) ⟨app (fOf t) Y, blank, .A⟩ = some ⟨app (fOf (flipN t y)) Y', blank, .A⟩
  | 0, t, Y, Y', n, h => by
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | y + 1, t, Y, Y', n, h => by
    obtain ⟨Y1, n1, n2, hh, hr, rfl⟩ := h
    exact steps_congr trans (by simp only [fcN]; omega)
      (steps_seq trans (front_hit t hh) (front_run y t.other Y1 Y' n2 hr))

def fcF (t : Kind) (y : Nat) : Nat :=
  fc t * ((y + 1) / 2) + fc t.other * (y / 2)

def flipF (t : Kind) (y : Nat) : Kind := if y % 2 = 0 then t else t.other

theorem other_other (t : Kind) : t.other.other = t := by cases t <;> rfl

theorem fcF_eq : ∀ (y : Nat) (t : Kind), fcN t y = fcF t y
  | 0, t => by simp [fcN, fcF]
  | y + 1, t => by
    simp only [fcN, fcF_eq y t.other, fcF, other_other]
    have e1 : (y + 1 + 1) / 2 = y / 2 + 1 := by omega
    have e2 : (y + 1) / 2 + (y + 1) / 2 = y + 1 - (y + 1) % 2 := by omega
    rw [e1, Nat.mul_succ]
    omega

theorem flipF_eq : ∀ (y : Nat) (t : Kind), flipN t y = flipF t y
  | 0, t => rfl
  | y + 1, t => by
    simp only [flipN, flipF_eq y t.other, flipF]
    by_cases h : y % 2 = 0
    · have h2 : (y + 1) % 2 ≠ 0 := by omega
      simp [h, h2]
    · have h2 : (y + 1) % 2 = 0 := by omega
      simp [h, h2, other_other]

/-! ## Calls on a finite tape, by evaluation -/

theorem step_R {q s : St} {x w : Bool} (hδ : trans q x = some (w, .R, s)) (L Rr : Tape) :
    step ⟨L, cons x Rr, q⟩ = some ⟨cons w L, Rr, s⟩ := by
  simp [step, TM.step, hδ]

theorem step_L {q s : St} {x w : Bool} (hδ : trans q x = some (w, .L, s)) (L Rr : Tape) :
    step ⟨L, cons x Rr, q⟩ = some ⟨tail L, cons (L 0) (cons w Rr), s⟩ := by
  simp [step, TM.step, hδ]

theorem step_N {q : St} {x : Bool} (hδ : trans q x = none) (L Rr : Tape) : step ⟨L, cons x Rr, q⟩ = none := by
  simp [step, TM.step, hδ]

/-- Run on the cells `l` (left, blank beyond) and `rs` (from the head on) until the head leaves `rs` to the right:
the left cells, the state and the step count then.  `none`: a halt, or the fuel `f` is used up. -/
def crun : Nat → List Bool → List Bool → St → Nat → Option (List Bool × St × Nat)
  | 0, _, _, _, _ => none
  | _ + 1, l, [], q, n => some (l, q, n)
  | f + 1, l, x :: rs, q, n =>
    match trans q x with
    | none => none
    | some (w, .R, s) => crun f (w :: l) rs s (n + 1)
    | some (w, .L, s) => crun f l.tail (l.headD false :: w :: rs) s (n + 1)

/-- The same run when it ends in a halt before the head leaves `rs`: the number of steps before the halt. -/
def hrun : Nat → List Bool → List Bool → St → Nat → Option Nat
  | 0, _, _, _, _ => none
  | _ + 1, _, [], _, _ => none
  | f + 1, l, x :: rs, q, n =>
    match trans q x with
    | none => some n
    | some (w, .R, s) => hrun f (w :: l) rs s (n + 1)
    | some (w, .L, s) => hrun f l.tail (l.headD false :: w :: rs) s (n + 1)

theorem crun_sound : ∀ (f : Nat) (l rs : List Bool) (q : St) (n0 : Nat) (l' : List Bool) (q' : St) (n : Nat),
    crun f l rs q n0 = some (l', q', n) →
    ∃ k, n = n0 + k ∧ ∀ R : Tape, steps k ⟨app l blank, app rs R, q⟩ = some ⟨app l' blank, R, q'⟩
  | 0, _, _, _, _, _, _, _, h => by simp [crun] at h
  | f + 1, l, [], q, n0, l', q', n, h => by
    simp only [crun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨0, rfl, fun R => rfl⟩
  | f + 1, l, x :: rs, q, n0, l', q', n, h => by
    simp only [crun] at h
    cases hδ : trans q x with
    | none => simp [hδ] at h
    | some tr =>
      obtain ⟨w, d, s⟩ := tr
      cases d with
      | R =>
        simp only [hδ] at h
        obtain ⟨k, rfl, hk⟩ := crun_sound f _ _ _ _ _ _ _ h
        refine ⟨k + 1, by omega, fun R => ?_⟩
        show steps (k + 1) ⟨app l blank, cons x (app rs R), q⟩ = _
        exact (steps_succ_of_step trans k (step_R hδ _ _)).trans (hk R)
      | L =>
        simp only [hδ] at h
        obtain ⟨k, rfl, hk⟩ := crun_sound f _ _ _ _ _ _ _ h
        refine ⟨k + 1, by omega, fun R => ?_⟩
        show steps (k + 1) ⟨app l blank, cons x (app rs R), q⟩ = _
        have e := steps_succ_of_step trans k (step_L hδ (app l blank) (app rs R))
        rw [app_tail, app_head] at e
        exact e.trans (hk R)

theorem hrun_sound : ∀ (f : Nat) (l rs : List Bool) (q : St) (n0 n : Nat), hrun f l rs q n0 = some n →
    ∃ k, n = n0 + k ∧ ∀ R : Tape, HaltsIn k ⟨app l blank, app rs R, q⟩
  | 0, _, _, _, _, _, h => by simp [hrun] at h
  | f + 1, l, [], q, n0, n, h => by simp [hrun] at h
  | f + 1, l, x :: rs, q, n0, n, h => by
    simp only [hrun] at h
    cases hδ : trans q x with
    | none =>
      simp only [hδ, Option.some.injEq] at h
      exact ⟨0, by omega, fun R => ⟨_, rfl, step_N hδ _ _⟩⟩
    | some tr =>
      obtain ⟨w, d, s⟩ := tr
      cases d with
      | R =>
        simp only [hδ] at h
        obtain ⟨k, rfl, hk⟩ := hrun_sound f _ _ _ _ _ h
        refine ⟨k + 1, by omega, fun R => ?_⟩
        obtain ⟨c, hc, hn⟩ := hk R
        refine ⟨c, ?_, hn⟩
        show steps (k + 1) ⟨app l blank, cons x (app rs R), q⟩ = _
        exact (steps_succ_of_step trans k (step_R hδ _ _)).trans hc
      | L =>
        simp only [hδ] at h
        obtain ⟨k, rfl, hk⟩ := hrun_sound f _ _ _ _ _ h
        refine ⟨k + 1, by omega, fun R => ?_⟩
        obtain ⟨c, hc, hn⟩ := hk R
        refine ⟨c, ?_, hn⟩
        show steps (k + 1) ⟨app l blank, cons x (app rs R), q⟩ = _
        have e := steps_succ_of_step trans k (step_L hδ (app l blank) (app rs R))
        rw [app_tail, app_head] at e
        exact e.trans hc

/-- The fuel of one call (no call of the run is nearly as long). -/
def callFuel : Nat := 10000000

/-- A call in `q` on the cells `l` that returns in `q'`: the new cells and the steps. -/
def call1 (q q' : St) (l : List Bool) : Option (List Bool × Nat) :=
  match crun callFuel l [true] q 0 with
  | some (true :: l', q'', n) => if q'' = q' then some (l', n) else none
  | _ => none

theorem call1_sound {q q' : St} {l l' : List Bool} {n : Nat} (h : call1 q q' l = some (l', n)) :
    Call q q' (app l blank) (app l' blank) n := by
  unfold call1 at h
  split at h
  · rename_i l1 q1 n1 hc
    split at h
    · rename_i hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hq
      obtain ⟨k, e, hk⟩ := crun_sound _ _ _ _ _ _ _ _ hc
      rw [Nat.zero_add] at e
      subst e
      exact fun R => hk R
    · cases h
  · cases h

/-- A call in `q` on the cells `l` that halts: the steps before the halt. -/
def halt1 (q : St) (l : List Bool) : Option Nat := hrun callFuel l [true] q 0

theorem halt1_sound {q : St} {l : List Bool} {n : Nat} (h : halt1 q l = some n) : HaltCall q (app l blank) n := by
  obtain ⟨k, e, hk⟩ := hrun_sound _ _ _ _ _ _ h
  rw [Nat.zero_add] at e
  subst e
  exact fun R => hk R

def tailHitH (l0 : List Bool) : Option (List Bool × Nat) :=
  match call1 .C .E l0 with
  | none => none
  | some (l1, n1) =>
    match call1 .E .F l1 with
    | none => none
    | some (l2, n2) =>
      match call1 .B .E l2 with
      | none => none
      | some (l3, n3) =>
        match call1 .C .A l3 with
        | none => none
        | some (l4, n4) =>
          match call1 .D .E l4 with
          | none => none
          | some (l5, n5) => some (true :: true :: true :: l5, n1 + n2 + n3 + n4 + n5)

def tailHitV (l0 : List Bool) : Option (List Bool × Nat) :=
  match call1 .C .E l0 with
  | none => none
  | some (l1, n1) => some (true :: true :: true :: true :: true :: true :: true :: l1, n1)

/-- A hit of kind `k` on the cells `tl` (blank beyond): the cells after it and the steps. -/
def tailHit : Kind → List Bool → Option (List Bool × Nat)
  | .H, true :: l0 => tailHitH l0
  | .V, true :: l0 => tailHitV l0
  | _, _ => none

theorem tailHitH_sound {l0 tl' : List Bool} {m : Nat} (h : tailHitH l0 = some (tl', m)) :
    HitH (app (true :: l0) blank) (app tl' blank) m := by
  unfold tailHitH at h
  cases h1 : call1 .C .E l0 with
  | none => simp [h1] at h
  | some r1 =>
    obtain ⟨l1, n1⟩ := r1
    simp only [h1] at h
    cases h2 : call1 .E .F l1 with
    | none => simp [h2] at h
    | some r2 =>
      obtain ⟨l2, n2⟩ := r2
      simp only [h2] at h
      cases h3 : call1 .B .E l2 with
      | none => simp [h3] at h
      | some r3 =>
        obtain ⟨l3, n3⟩ := r3
        simp only [h3] at h
        cases h4 : call1 .C .A l3 with
        | none => simp [h4] at h
        | some r4 =>
          obtain ⟨l4, n4⟩ := r4
          simp only [h4] at h
          cases h5 : call1 .D .E l4 with
          | none => simp [h5] at h
          | some r5 =>
            obtain ⟨l5, n5⟩ := r5
            simp only [h5, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, call1_sound h1, call1_sound h2, call1_sound h3,
              call1_sound h4, call1_sound h5, rfl, rfl⟩

theorem tailHitV_sound {l0 tl' : List Bool} {m : Nat} (h : tailHitV l0 = some (tl', m)) :
    HitV (app (true :: l0) blank) (app tl' blank) m := by
  unfold tailHitV at h
  cases h1 : call1 .C .E l0 with
  | none => simp [h1] at h
  | some r1 =>
    obtain ⟨l1, n1⟩ := r1
    simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, rfl, call1_sound h1, rfl⟩

theorem tailHit_sound : ∀ {k : Kind} {tl tl' : List Bool} {m : Nat}, tailHit k tl = some (tl', m) →
    Hit k (app tl blank) (app tl' blank) m
  | .H, true :: _, _, _, h => tailHitH_sound h
  | .V, true :: _, _, _, h => tailHitV_sound h
  | .H, [], _, _, h => by cases h
  | .V, [], _, _, h => by cases h
  | .H, false :: _, _, _, h => by cases h
  | .V, false :: _, _, _, h => by cases h

/-- The fourth call of an H-hit on the cells `l0` halts: the steps before the halt. -/
def tailHaltH (l0 : List Bool) : Option Nat :=
  match call1 .C .E l0 with
  | none => none
  | some (l1, n1) =>
    match call1 .E .F l1 with
    | none => none
    | some (l2, n2) =>
      match call1 .B .E l2 with
      | none => none
      | some (l3, n3) =>
        match halt1 .C l3 with
        | none => none
        | some n4 => some (n1 + n2 + n3 + n4)

/-- A hit of kind `k` on the cells `tl` (blank beyond) that halts: how, and the steps before the halt. -/
def tailHalt : Kind → List Bool → Option (HK × Nat)
  | .H, true :: l0 =>
    match tailHaltH l0 with
    | none => none
    | some n => some (.H4, n)
  | .V, true :: l0 =>
    match halt1 .C l0 with
    | none => none
    | some n => some (.HC, n)
  | _, _ => none

theorem tailHaltH_sound {l0 : List Bool} {m : Nat} (h : tailHaltH l0 = some m) : H4 (app (true :: l0) blank) m := by
  unfold tailHaltH at h
  cases h1 : call1 .C .E l0 with
  | none => simp [h1] at h
  | some r1 =>
    obtain ⟨l1, n1⟩ := r1
    simp only [h1] at h
    cases h2 : call1 .E .F l1 with
    | none => simp [h2] at h
    | some r2 =>
      obtain ⟨l2, n2⟩ := r2
      simp only [h2] at h
      cases h3 : call1 .B .E l2 with
      | none => simp [h3] at h
      | some r3 =>
        obtain ⟨l3, n3⟩ := r3
        simp only [h3] at h
        cases h4 : halt1 .C l3 with
        | none => simp [h4] at h
        | some n4 =>
          simp only [h4, Option.some.injEq] at h
          subst h
          exact ⟨_, _, _, _, _, _, _, _, rfl, call1_sound h1, call1_sound h2, call1_sound h3, halt1_sound h4, rfl⟩

theorem tailHalt_sound : ∀ {k : Kind} {tl : List Bool} {hk : HK} {m : Nat}, tailHalt k tl = some (hk, m) →
    Dies hk (app tl blank) m
  | .H, true :: l0, hk, m, h => by
    unfold tailHalt at h
    cases h1 : tailHaltH l0 with
    | none => simp [h1] at h
    | some n =>
      simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact tailHaltH_sound h1
  | .V, true :: l0, hk, m, h => by
    unfold tailHalt at h
    cases h1 : halt1 .C l0 with
    | none => simp [h1] at h
    | some n =>
      simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, halt1_sound h1⟩
  | .H, [], _, _, h => by cases h
  | .V, [], _, _, h => by cases h
  | .H, false :: _, _, _, h => by cases h
  | .V, false :: _, _, _, h => by cases h

/-! ## A hit that halts, through the levels -/

/-- The way the hit on the levels `ls` halts when the hit below them halts as `hk`, and the steps inside the levels
before the halt. -/
def haltUp : List (Nat × Nat) → HK → Option (HK × Nat)
  | [], hk => some (hk, 0)
  | (p, j) :: ls, hk =>
    match haltUp ls hk with
    | none => none
    | some (hk1, c) =>
      match haltTab p hk1 with
      | none => none
      | some (hk2, a, b) => some (hk2, c + (a * j + b))

theorem haltUp_sound : ∀ (ls : List (Nat × Nat)) (hk hk' : HK) (c : Nat) (Y : Tape) (m : Nat),
    haltUp ls hk = some (hk', c) → Dies hk Y m → Dies hk' (Stack ls Y) (m + c)
  | [], hk, hk', c, Y, m, h, hd => by
    simp only [haltUp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hd
  | (p, j) :: ls, hk, hk', c, Y, m, h, hd => by
    simp only [haltUp] at h
    cases h1 : haltUp ls hk with
    | none => simp [h1] at h
    | some r1 =>
      obtain ⟨hk1, c1⟩ := r1
      simp only [h1] at h
      cases h2 : haltTab p hk1 with
      | none => simp [h2] at h
      | some r2 =>
        obtain ⟨hk2, a, b⟩ := r2
        simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have d1 := haltUp_sound ls hk hk1 c1 Y m h1 hd
        have d2 := level_halt p j hk1 hk2 a b h2 d1
        rw [Nat.add_assoc] at d2
        exact d2

/-- Steps of the front before the call that halts. -/
def frontHalt : Kind → HK → Option Nat
  | .H, .HC => some 23
  | .H, .H4 => some 70
  | .V, .HC => some 35
  | .V, .H4 => none

theorem frontHalt_sound : ∀ (t : Kind) (hk : HK) (f : Nat) (Y : Tape) (m : Nat), frontHalt t hk = some f →
    Dies hk Y m → HaltsIn (m + f) ⟨app (fOf t) Y, blank, .A⟩
  | .H, .HC, _, _, _, h, hd => by cases h; exact frontH_HC hd
  | .H, .H4, _, _, _, h, hd => by cases h; exact frontH_H4 hd
  | .V, .HC, _, _, _, h, hd => by cases h; exact frontV_HC hd
  | .V, .H4, _, _, _, h, _ => by cases h

/-! ## The accelerated run -/

/-- `w` repeated `n` times, as a list. -/
def repL : Nat → List Bool → List Bool
  | 0, _ => []
  | n + 1, w => w ++ repL n w

theorem rep_repL : ∀ (n : Nat) (w : List Bool) (s : Tape), rep n w s = app (repL n w) s
  | 0, _, _ => rfl
  | n + 1, w, s => by rw [rep_succ, rep_repL n w s, app_app]; rfl

/-- The cells of a level. -/
def wList (p j : Nat) : List Bool := repL (j + 1) blockW ++ sepL p

theorem W_list (p j : Nat) (l : List Bool) : W p j (app l blank) = app (wList p j ++ l) blank := by
  unfold W wList
  rw [rep_repL, app_app, app_app, List.append_assoc]

theorem Stack_snoc : ∀ (ls : List (Nat × Nat)) (p j : Nat) (Y : Tape), Stack (ls ++ [(p, j)]) Y = Stack ls (W p j Y)
  | [], _, _, _ => rfl
  | (p', j') :: ls, p, j, Y => by
    show W p' j' (Stack (ls ++ [(p, j)]) Y) = _
    rw [Stack_snoc ls]
    rfl

/-- `strip w l = some r` when `l = w ++ r`. -/
def strip : List Bool → List Bool → Option (List Bool)
  | [], l => some l
  | _ :: _, [] => none
  | a :: w, b :: l => if a = b then strip w l else none

theorem strip_sound : ∀ (w l r : List Bool), strip w l = some r → l = w ++ r
  | [], l, r, h => by simp only [strip, Option.some.injEq] at h; rw [h]; rfl
  | _ :: _, [], _, h => by simp [strip] at h
  | a :: w, b :: l, r, h => by
    simp only [strip] at h
    split at h
    · rename_i hab
      rw [hab, strip_sound w l r h]; rfl
    · cases h

/-- The state of the accelerated run at a visit that is followed by a hit: the kind of that hit (the front), the
levels `(position, blocks - 1)` outermost first, the cells of the tape left of them down to the blank end, and the
number of steps from blank tape. -/
structure S where
  t : Kind
  ls : List (Nat × Nat)
  tl : List Bool
  n : Nat

def S.cfg (s : S) : Config := ⟨app (fOf s.t) (Stack s.ls (app s.tl blank)), blank, .A⟩

/-- The run from blank tape is at the configuration of `s` after `s.n` steps. -/
def Reach (s : S) : Prop := steps s.n init = some s.cfg

/-- `y` hits, of which none or one reaches the cells `tl`. -/
def opAdv (s : S) (y : Nat) : Option S :=
  if chainOK s.t s.ls then
    match advS s.ls y with
    | (ls', 0, c) => some ⟨flipF s.t y, ls', s.tl, s.n + (c + fcF s.t y)⟩
    | (ls', 1, c) =>
      match tailHit (tailKind s.t s.ls) s.tl with
      | some (tl', m) => some ⟨flipF s.t y, ls', tl', s.n + (c + m + fcF s.t y)⟩
      | none => none
    | _ => none
  else none

theorem opAdv_sound {s s' : S} {y : Nat} (hr : Reach s) (h : opAdv s y = some s') : Reach s' := by
  unfold opAdv at h
  split at h
  · rename_i hc
    split at h
    · rename_i ls' c he
      simp only [Option.some.injEq] at h
      subst h
      have hrun : Run (tailKind s.t s.ls) (advS s.ls y).2.1 (app s.tl blank) (app s.tl blank) 0 := by
        rw [he]; exact ⟨rfl, rfl⟩
      have fr := front_run y s.t _ _ _ (stack_run s.ls s.t y _ _ _ hc hrun)
      rw [he, fcF_eq, flipF_eq] at fr
      exact steps_congr trans (by simp only; omega) (steps_seq trans hr fr)
    · rename_i ls' c he
      split at h
      · rename_i tl' m ht
        simp only [Option.some.injEq] at h
        subst h
        have hrun : Run (tailKind s.t s.ls) (advS s.ls y).2.1 (app s.tl blank) (app tl' blank) m := by
          rw [he]; exact ⟨_, _, _, tailHit_sound ht, ⟨rfl, rfl⟩, rfl⟩
        have fr := front_run y s.t _ _ _ (stack_run s.ls s.t y _ _ _ hc hrun)
        rw [he, fcF_eq, flipF_eq] at fr
        exact steps_congr trans rfl (steps_seq trans hr fr)
      · cases h
    · cases h
  · cases h

/-- Read the first cells of `tl` as a level. -/
def opPeel (s : S) (p j : Nat) : Option S :=
  match strip (wList p j) s.tl with
  | some rest => some ⟨s.t, s.ls ++ [(p, j)], rest, s.n⟩
  | none => none

theorem opPeel_sound {s s' : S} {p j : Nat} (hr : Reach s) (h : opPeel s p j = some s') : Reach s' := by
  unfold opPeel at h
  split at h
  · rename_i rest hs
    simp only [Option.some.injEq] at h
    subst h
    have e := strip_sound _ _ _ hs
    unfold Reach S.cfg
    simp only
    rw [Stack_snoc, W_list, ← e]
    exact hr
  · cases h

/-- Write the deepest level out as cells. -/
def opUnpeel (s : S) : Option S :=
  match s.ls.reverse with
  | [] => none
  | (p, j) :: r => some ⟨s.t, r.reverse, wList p j ++ s.tl, s.n⟩

theorem opUnpeel_sound {s s' : S} (hr : Reach s) (h : opUnpeel s = some s') : Reach s' := by
  unfold opUnpeel at h
  split at h
  · cases h
  · rename_i p j r hrev
    simp only [Option.some.injEq] at h
    subst h
    have e : s.ls = r.reverse ++ [(p, j)] := by
      have := congrArg List.reverse hrev
      rw [List.reverse_reverse, List.reverse_cons] at this
      exact this
    unfold Reach S.cfg at hr ⊢
    simp only
    rw [e, Stack_snoc, W_list] at hr
    exact hr

/-- The next hit halts: the number of steps from blank tape before the halt. -/
def opFinal (s : S) : Option Nat :=
  match tailHalt (tailKind s.t s.ls) s.tl with
  | none => none
  | some (hk, m) =>
    match haltUp s.ls hk with
    | none => none
    | some (hk', c) =>
      match frontHalt s.t hk' with
      | none => none
      | some f => some (s.n + (m + c + f))

theorem opFinal_sound {s : S} {N : Nat} (hr : Reach s) (h : opFinal s = some N) : HaltsIn N init := by
  unfold opFinal at h
  cases h1 : tailHalt (tailKind s.t s.ls) s.tl with
  | none => simp [h1] at h
  | some r1 =>
    obtain ⟨hk, m⟩ := r1
    simp only [h1] at h
    cases h2 : haltUp s.ls hk with
    | none => simp [h2] at h
    | some r2 =>
      obtain ⟨hk', c⟩ := r2
      simp only [h2] at h
      cases h3 : frontHalt s.t hk' with
      | none => simp [h3] at h
      | some f =>
        simp only [h3, Option.some.injEq] at h
        subst h
        exact HaltsIn.seq hr (frontHalt_sound _ _ _ _ _ h3 (haltUp_sound _ _ _ _ _ _ h2 (tailHalt_sound h1)))

/-! The parts of the run that need no proof: which levels to read, how many hits to jump. -/

def cntBlocks : Nat → List Bool → Nat → Nat × List Bool
  | 0, l, n => (n, l)
  | f + 1, l, n =>
    match strip blockW l with
    | some r => cntBlocks f r (n + 1)
    | none => (n, l)

def findSep (k : Kind) (l : List Bool) : Option Nat :=
  (List.range 16).find? (fun p => kindOf p == k && (strip (sepL p) l).isSome)

def parsePeel (k : Kind) (tl : List Bool) : Option (Nat × Nat) :=
  match cntBlocks tl.length tl 0 with
  | (0, _) => none
  | (n + 1, r) =>
    match findSep k r with
    | some p => some (p, n)
    | none => none

/-- Read as many levels as the cells show. -/
def peelAll : Nat → S → S
  | 0, s => s
  | f + 1, s =>
    match parsePeel (tailKind s.t s.ls) s.tl with
    | none => s
    | some (p, j) =>
      match opPeel s p j with
      | none => s
      | some s' => peelAll f s'

theorem peelAll_sound : ∀ (f : Nat) (s : S), Reach s → Reach (peelAll f s)
  | 0, _, hr => hr
  | f + 1, s, hr => by
    simp only [peelAll]
    split
    · exact hr
    · split
      · exact hr
      · rename_i h
        exact peelAll_sound f _ (opPeel_sound hr h)

def distPass : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, p => if (passOf p).isSome then 0 else 1 + distPass f (nxt p)

def walk : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, p, r => if r = 0 then 0 else 1 + walk f (nxt p) (if (passOf p).isSome then r - 1 else r)

/-- The hits a level at position `p` must get to pass on `x` of them. -/
def need (p x : Nat) : Nat := if x = 0 then 0 else 16 * ((x - 1) / 6) + walk 40 p ((x - 1) % 6 + 1)

/-- The hits until every level stands at a passing position. -/
def readyCount (ls : List (Nat × Nat)) : Nat :=
  ls.reverse.foldl (fun e pj => need pj.1 e + distPass 16 (advF pj.1 0 (need pj.1 e)).1) 0

/-- The run: with `true`, read the levels and jump to the next hit that reaches the cells; with `false`, make that
hit, or find that it halts, or (if the calls do not return as they should) write the deepest level out as cells
and try again.  The result is the number of steps from blank tape before the halt. -/
def loop : Nat → Bool → S → Option Nat
  | 0, _, _ => none
  | f + 1, true, s =>
    match opAdv (peelAll 100 s) (readyCount (peelAll 100 s).ls) with
    | none => none
    | some s2 => loop f false s2
  | f + 1, false, s =>
    match opAdv s 1 with
    | some s3 => loop f true s3
    | none =>
      match opFinal s with
      | some N => some N
      | none =>
        match opUnpeel s with
        | some s4 => loop f false s4
        | none => none

theorem loop_sound : ∀ (f : Nat) (b : Bool) (s : S) (N : Nat), Reach s → loop f b s = some N → HaltsIn N init
  | 0, _, _, _, _, h => by simp [loop] at h
  | f + 1, true, s, N, hr, h => by
    simp only [loop] at h
    split at h
    · cases h
    · rename_i s2 h2
      exact loop_sound f false s2 N (opAdv_sound (peelAll_sound _ _ hr) h2) h
  | f + 1, false, s, N, hr, h => by
    simp only [loop] at h
    split at h
    · rename_i s3 h3
      exact loop_sound f true s3 N (opAdv_sound hr h3) h
    · split at h
      · rename_i N' hN
        simp only [Option.some.injEq] at h
        subst h
        exact opFinal_sound hr hN
      · split at h
        · rename_i s4 h4
          exact loop_sound f false s4 N (opUnpeel_sound hr h4) h
        · cases h

end H23376
