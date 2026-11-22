import Machine
import Total

/-! # The four visit functions are the machine, and the round law

Machine: 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF. `Tokens.lean` took the four visit functions (`BV`) as a
definition, checked against the transition table only by `c/zvis.cpp`. This file closes that gap in the kernel:

* `link`: every computation of the four visit functions is a run of the real machine (`H36869.trans`, as generated
  from the text form). The half tape of a visit is the tape from the head leftwards (head cell first): a visit of
  `X` on `S` with result `S'` starts with the head on `S 0` in state `X`, ends with the head on the first cell to the
  right of the half tape in state B, and never reads or writes anything to the right of `S 0`. P is a visit of B
  entered with the cell under the head already 0.
* `round`: from `0 S` with blank tape to the right, in state A, the machine reaches `0 S'` with `S' = 1 0 A(S)`,
  again with blank tape to the right, in state A. From blank tape `S = []`.
* `nonhalt_of_clean`: if, in every round from blank tape, the visit of A leaves a tape without defect (the defect
  `1 0` put in front by the previous round has disappeared), the machine never halts.

So the whole question is now the one statement assumed in `nonhalt_of_clean`; everything else is in the kernel.
-/

namespace L36869

open Z36869 (BV BK T TV enc Clean Good)

abbrev St := H36869.St
abbrev steps := H36869.steps

theorem zc : @Z36869.cons = @TM.cons := by
  funext b s i; cases i <;> rfl

/-- A visit of `X` on the half tape `S`, ending in state B with half tape `S'`, for any tape `R` to the right. -/
def Vis (X : St) (S S' : TM.Tape) : Prop :=
  ∃ n, ∀ R : TM.Tape, steps n ⟨TM.tail S, TM.cons (S 0) R, X⟩ = some ⟨S', R, .B⟩

theorem seq {a b : Nat} {c0 c1 c2 : H36869.Config} (h1 : steps a c0 = some c1) (h2 : steps b c1 = some c2) :
    steps (a + b) c0 = some c2 := TM.steps_seq _ h1 h2

theorem seq3 {a b c : Nat} {c0 c1 c2 c3 : H36869.Config} (h1 : steps a c0 = some c1) (h2 : steps b c1 = some c2)
    (h3 : steps c c2 = some c3) : steps (a + b + c) c0 = some c3 := seq (seq h1 h2) h3

open TM (cons tail blank)

theorem v_a0 (s : TM.Tape) : Vis .A (cons false s) (cons true s) := ⟨1, fun _ => rfl⟩

theorem v_a1 {s e r} (he : Vis .E s e) (hp : Vis .B (cons false e) r) : Vis .A (cons true s) r := by
  obtain ⟨n, hn⟩ := he; obtain ⟨m, hm⟩ := hp
  exact ⟨1 + n + m, fun R => seq3 (c1 := ⟨tail s, cons (s 0) (cons false R), .E⟩) rfl (hn _) (hm _)⟩

theorem v_e00 {t a} (h : Vis .A t a) : Vis .E (cons false (cons false t)) (cons true (cons false a)) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨2 + n + 2, fun R => seq3 (c1 := ⟨tail t, cons (t 0) (cons true (cons false R)), .A⟩) rfl (hn _) rfl⟩

theorem v_e10 {t e} (h : Vis .E t e) : Vis .E (cons true (cons false t)) (cons true (cons false e)) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨4 + n + 2, fun R => seq3 (c1 := ⟨tail t, cons (t 0) (cons true (cons false R)), .E⟩) rfl (hn _) rfl⟩

theorem v_e01 {t f r} (hf : Vis .F (cons true t) f) (hp : Vis .B (cons false f) r) :
    Vis .E (cons false (cons true t)) r := by
  obtain ⟨n, hn⟩ := hf; obtain ⟨m, hm⟩ := hp
  exact ⟨1 + n + m, fun R => seq3 (c1 := ⟨t, cons true (cons false R), .F⟩) rfl (hn _) (hm _)⟩

theorem v_f10 {u a} (h : Vis .A u a) : Vis .F (cons true (cons false u)) (cons true (cons false a)) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨2 + n + 2, fun R => seq3 (c1 := ⟨tail u, cons (u 0) (cons true (cons false R)), .A⟩) rfl (hn _) rfl⟩

theorem v_f11 {u f r} (hf : Vis .F (cons true u) f) (hp : Vis .B (cons false f) r) :
    Vis .F (cons true (cons true u)) r := by
  obtain ⟨n, hn⟩ := hf; obtain ⟨m, hm⟩ := hp
  exact ⟨1 + n + m, fun R => seq3 (c1 := ⟨u, cons true (cons false R), .F⟩) rfl (hn _) (hm _)⟩

theorem v_p0 {v e} (h : Vis .E v e) : Vis .B (cons false (cons false v)) (cons true (cons false e)) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨2 + n + 2, fun R => seq3 (c1 := ⟨tail v, cons (v 0) (cons true (cons false R)), .E⟩) rfl (hn _) rfl⟩

theorem v_p1 (v : TM.Tape) : Vis .B (cons false (cons true v)) (cons false (cons false v)) := ⟨3, fun _ => rfl⟩

/-- What a computation of a visit function means for the machine. -/
def Real : BK → TM.Tape → TM.Tape → Prop
  | .A, s, r => Vis .A s r
  | .E, s, r => Vis .E s r
  | .F, s, r => Vis .F s r
  | .P, s, r => Vis .B (cons false (tail s)) r

/-- Every computation of the four visit functions is a run of the machine. -/
theorem link {k s r} (h : BV k s r) : Real k s r := by
  induction h <;> simp only [Real, zc, TM.tail_cons] at *
  · exact v_a0 _
  all_goals first
    | exact v_a1 ‹_› ‹_› | exact v_e00 ‹_› | exact v_e10 ‹_› | exact v_e01 ‹_› ‹_› | exact v_f10 ‹_›
    | exact v_f11 ‹_› ‹_› | exact v_p0 ‹_› | exact v_p1 _

/-- One round: `0 S` with blank tape to the right, in state A, becomes `0 1 0 A(S)`, the same way round. -/
theorem round {S a} (h : Vis .A S a) :
    ∃ n, 1 ≤ n ∧ steps n ⟨cons false S, blank, .A⟩ = some ⟨cons false (cons true (cons false a)), blank, .A⟩ := by
  obtain ⟨n, hn⟩ := v_e00 h
  refine ⟨6 + n + 1, by omega, ?_⟩
  have h3 : steps 1 ⟨cons true (cons false a), cons true (cons false blank), .B⟩ =
      some ⟨cons false (cons true (cons false a)), blank, .A⟩ := by
    conv => rhs; rw [← TM.cons_false_blank]
    rfl
  exact seq3 (c1 := ⟨cons false S, cons false (cons true (cons false blank)), .E⟩) rfl (hn _) h3

/-! ## Rounds from blank tape -/

/-- The token tapes at the start of the rounds from blank tape: `S₀ = []`, `S_{k+1} = x A(S_k)`. -/
inductive Reach : List T → Prop
  | nil : Reach []
  | next {w a} : Reach w → TV .A w a → Reach (.x :: a)

theorem good_of_reach (H : ∀ w a, Reach w → TV .A w a → Clean a) {w} (h : Reach w) : Good w := by
  cases h with
  | nil => exact Or.inl Z36869.clean_nil
  | next hw ha => exact Or.inr ⟨[], .x, _, Z36869.clean_nil, Or.inl rfl, H _ _ hw ha, rfl⟩

theorem step_of_good {w} (h : Good w) : ∃ a, TV .A w a := by
  obtain ⟨r, hr, _⟩ := Z36869.total h 1
  obtain ⟨a, ha, h0⟩ := hr.succ_inv
  exact ⟨a, ha⟩

theorem enc_x (a : List T) : enc (.x :: a) = cons true (cons false (enc a)) := by
  show Z36869.cons true (Z36869.cons false (enc a)) = _; rw [zc]

theorem runs (H : ∀ w a, Reach w → TV .A w a → Clean a) :
    ∀ k, ∃ w n, Reach w ∧ k ≤ n ∧ steps n H36869.init = some ⟨cons false (enc w), blank, .A⟩ := by
  intro k
  induction k with
  | zero =>
    refine ⟨[], 0, Reach.nil, Nat.le_refl _, ?_⟩
    show some H36869.init = some ⟨cons false blank, blank, .A⟩
    rw [TM.cons_false_blank]; rfl
  | succ k ih =>
    obtain ⟨w, n, hw, hk, hn⟩ := ih
    obtain ⟨a, ha⟩ := step_of_good (good_of_reach H hw)
    have hv : Vis .A (enc w) (enc a) := link (Z36869.sound ha)
    obtain ⟨m, hm1, hm⟩ := round hv
    refine ⟨.x :: a, n + m, Reach.next hw ha, by omega, ?_⟩
    rw [enc_x]; exact seq hn hm

/-- If every round's defect has disappeared by the end of the round (the visit of A on every round tape leaves a
tape without defect), the machine never halts from blank tape. -/
theorem nonhalt_of_clean (H : ∀ w a, Reach w → TV .A w a → Clean a) : ¬ H36869.HaltsFromBlank := by
  apply TM.not_halts_of_forall
  apply TM.forall_of_unbounded _ (fun m => ∃ w, steps m H36869.init = some ⟨cons false (enc w), blank, .A⟩)
  · intro n
    obtain ⟨w, m, _, hm, h⟩ := runs H n
    exact ⟨m, hm, w, h⟩
  · rintro m ⟨w, h⟩
    exact ⟨_, h⟩

end L36869
