import Machine
import Total
import Need

/-! # The twin's token rules are runs of this machine, and the round law

Machine: 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---. Its twin 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF has token
rules `TV` (words `L = 1010`, `O = 000`, `I = 100`, defects `x = 10`, `1`, `0`; the twin's `lean/Tokens.lean`) and
proves in `lean/Total.lean` there that on a tape with at most one defect they always apply (`Z36869.total`). This
file proves, in the kernel, that the same token rules are runs of **this** machine's transition table
(`H83189.trans`), so this machine never halts under exactly the same assumption as the twin (`nonhalt_of_need`).

A token tape `w` is the half tape `E w` to the right of the head. Each kind of token visit is a run from one of
five *entry forms* (state, and the two cells left of the head, nearest first) that ends three cells further left,
having rewritten those two cells, for any tape `L` further left (never read):

* `FA w w'`  (visit of A):  `B` after `1 0` on `E w`  ends in `E` on `L 0 · 0 0 · E w'`.
* `FH1 w w'` (`Eh`, E without its leading `1 0`): `C` after `1 0` on `E w` ends in `E` on `L 0 · 0 0 1 0 · E w'`.
* `FH2 w w'` (`Eh`): `C` after `1 1` on `E w` ends in `D` on `L 0 · 0 0 0 0 · E w'`.
* `FO1 w w'` (`E0`, E after a 0): `B` after `0 0` on `0 · E w` ends in `E` on `L 0 · 0 0 · E w'`.
* `FO2 w w'` (`E0`): `C` after `1 0` on `0 · E w` ends in `E` on `L 0 · 0 0 · E w'`.

* `sound`: every token rule `TV k w w'` holds in all forms of its kind (`Means`). Each of the 25 cases is a few
  stretches of 1 to 17 steps (checked by `rfl`) around calls of the rule's premises; the defect rule `x L` runs the same
  way as on the twin, through the visit of A on `x W` four cells further right. Written by `py/linkgen.py`, which
  finds each run by symbolic simulation.
* `round_run`: in `E` on `0 0 0 1 0 · E S` (anything to the left after two blank cells) the machine reaches `E`
  two cells further left on `0 0 0 1 0 · E (x :: A(S))`, where `FA S A(S)`; from blank tape it is there with
  `S = []` after 4 steps (`start`).
* `round9`: from blank tape this machine is at the start of round 9 (E on `0 0 0 1 0 · x a9`) at step 7,834.
* `nonhalt_of_need`: if every round from round 9 on has `nx W ≤ 1` on its tape `x W` (the twin's hypothesis in
  `F36869.nonhalt_of_need`, word for word, with `nx` and `R9` from the twin's `Need.lean`), this machine never halts
  from blank tape. An earlier version (`nonhalt_of_clean`, PR 416) assumed that every round's defect dies counted from
  round 0; that hypothesis is false (round 2's defect survives, `F36869.old_hyp_false`), so it was removed.
-/

namespace K83189

open TM (cons tail blank app)
open Z36869 (T TV Clean Good)

abbrev steps := H83189.steps

/-- A token tape as the half tape right of the head. -/
def E : List T → TM.Tape
  | [] => blank
  | t :: w => app (Z36869.bits t) (E w)

theorem sq {a b : Nat} {c0 c1 c2 : H83189.Config} (h1 : steps a c0 = some c1) (h2 : steps b c1 = some c2) :
    steps (a + b) c0 = some c2 := TM.steps_seq _ h1 h2

def FA (w w' : List T) : Prop := ∃ n, ∀ L : TM.Tape,
  steps n ⟨app [true, false] L, E w, .B⟩ = some ⟨tail L, cons (L 0) (app [false, false] (E w')), .E⟩
def FH1 (w w' : List T) : Prop := ∃ n, ∀ L : TM.Tape,
  steps n ⟨app [true, false] L, E w, .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false] (E w')), .E⟩
def FH2 (w w' : List T) : Prop := ∃ n, ∀ L : TM.Tape,
  steps n ⟨app [true, true] L, E w, .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false] (E w')), .D⟩
def FO1 (w w' : List T) : Prop := ∃ n, ∀ L : TM.Tape,
  steps n ⟨app [false, false] L, cons false (E w), .B⟩ = some ⟨tail L, cons (L 0) (app [false, false] (E w')), .E⟩
def FO2 (w w' : List T) : Prop := ∃ n, ∀ L : TM.Tape,
  steps n ⟨app [true, false] L, cons false (E w), .C⟩ = some ⟨tail L, cons (L 0) (app [false, false] (E w')), .E⟩

/-- What a token visit means for this machine: a run from each entry form of its kind. -/
def Means : Z36869.TK → List T → List T → Prop
  | .A, w, w' => FA w w'
  | .Eh, w, w' => FH1 w w' ∧ FH2 w w'
  | .E0, w, w' => FO1 w w' ∧ FO2 w w'

/-! ## Blank tails -/

theorem blank_pad : app (List.replicate 14 false) blank = blank := by
  simp only [List.replicate, TM.app_cons, TM.app_nil, TM.cons_false_blank]

theorem app_getD (u : List Bool) : app u blank = fun i => u.getD i false := by
  induction u with
  | nil => rfl
  | cons b u ih => funext i; cases i <;> simp [ih]

theorem getD_of_le (u : List Bool) (i : Nat) (h : u.length ≤ i) : u.getD i false = false := by
  induction u generalizing i with
  | nil => rfl
  | cons b u ih => cases i with
    | zero => simp at h
    | succ i => simp only [List.getD_cons_succ]; exact ih i (by simp at h; omega)

theorem app_blank_ext (u v : List Bool) (h : ∀ i < max u.length v.length, u.getD i false = v.getD i false) :
    app u blank = app v blank := by
  rw [app_getD, app_getD]; funext i
  by_cases hi : i < max u.length v.length
  · exact h i hi
  · rw [getD_of_le u i (by omega), getD_of_le v i (by omega)]

theorem E_x_nil : E [.x] = E [.I] := app_blank_ext [true, false] [true, false, false] (by decide)

/-! ## The token rules as runs (generated by `py/linkgen.py`) -/

theorem aL_FA {a b w : List T} (h0 : Means .A w a) (h1 : Means .A a b) : FA (.L :: w) (.L :: b) := by
  obtain ⟨n0, g0⟩ := h0
  obtain ⟨n1, g1⟩ := h1
  exact ⟨6 + n0 + 7 + n1 + 12, fun L => sq (sq (sq (sq (show steps 6 ⟨app [true, false] L, app [true, false, true, false] (E w), .B⟩ = some ⟨app [true, false, true, true, true, false] L, app [] (E w), .B⟩ from rfl) (g0 (app [true, true, true, false] L))) (show steps 7 ⟨app [true, true, false] L, app [true, false, false] (E a), .E⟩ = some ⟨app [true, false, true, false, true, false] L, app [] (E a), .B⟩ from rfl)) (g1 (app [true, false, true, false] L))) (show steps 12 ⟨app [false, true, false] L, app [true, false, false] (E b), .E⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, true, false] (E b)), .E⟩ from rfl)⟩

theorem aO_FA {w : List T}  : FA (.O :: w) (.I :: w) := by
  exact ⟨3, fun L => (show steps 3 ⟨app [true, false] L, app [false, false, false] (E w), .B⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, false] (E w)), .E⟩ from rfl)⟩

theorem aI_FA {a w : List T} (h0 : Means .A w a) : FA (.I :: w) (.O :: a) := by
  obtain ⟨n0, g0⟩ := h0
  exact ⟨3 + n0 + 3, fun L => sq (sq (show steps 3 ⟨app [true, false] L, app [true, false, false] (E w), .B⟩ = some ⟨app [true, false, true, true, false] L, app [] (E w), .B⟩ from rfl) (g0 (app [true, true, false] L))) (show steps 3 ⟨app [true, false] L, app [true, false, false] (E a), .E⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false, false] (E a)), .E⟩ from rfl)⟩

theorem aNil_FA  : FA [] [.I] := by
  refine ⟨3, fun L => ?_⟩
  have s := (show steps 3 ⟨app [true, false] L, app [] (app (List.replicate 14 false) blank), .B⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false] blank), .E⟩ from rfl)
  rw [blank_pad, app_blank_ext [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false] [false, false, true, false, false] (by decide)] at s
  exact s

theorem az_FA {w : List T}  : FA (.z :: w) (.one :: w) := by
  exact ⟨3, fun L => (show steps 3 ⟨app [true, false] L, app [false] (E w), .B⟩ = some ⟨tail L, cons (L 0) (app [false, false, true] (E w)), .E⟩ from rfl)⟩

theorem axO_FA {w : List T}  : FA (.x :: .O :: w) (.O :: .x :: w) := by
  exact ⟨9, fun L => (show steps 9 ⟨app [true, false] L, app [true, false, false, false, false] (E w), .B⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false, false, true, false] (E w)), .E⟩ from rfl)⟩

theorem axI_FA {e w : List T} (h0 : Means .Eh w e) : FA (.x :: .I :: w) (.L :: .O :: e) := by
  obtain ⟨⟨n0, g0FH1⟩, ⟨m0, g0FH2⟩⟩ := h0
  exact ⟨17 + m0 + 13, fun L => sq (sq (show steps 17 ⟨app [true, false] L, app [true, false, true, false, false] (E w), .B⟩ = some ⟨app [true, true, false, true, false, true, false] L, app [] (E w), .C⟩ from rfl) (g0FH2 (app [false, true, false, true, false] L))) (show steps 13 ⟨app [true, false, true, false] L, app [false, false, false, false, false] (E e), .D⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, true, false, false, false, false] (E e)), .E⟩ from rfl)⟩

theorem axL_FA {a b w : List T} (h0 : Means .A (.x :: w) a) (h1 : Means .A a b) : FA (.x :: .L :: w) (.L :: b) := by
  obtain ⟨n0, g0⟩ := h0
  obtain ⟨n1, g1⟩ := h1
  exact ⟨6 + n0 + 7 + n1 + 12, fun L => sq (sq (sq (sq (show steps 6 ⟨app [true, false] L, app [true, false, true, false, true, false] (E w), .B⟩ = some ⟨app [true, false, true, true, true, false] L, app [true, false] (E w), .B⟩ from rfl) (g0 (app [true, true, true, false] L))) (show steps 7 ⟨app [true, true, false] L, app [true, false, false] (E a), .E⟩ = some ⟨app [true, false, true, false, true, false] L, app [] (E a), .B⟩ from rfl)) (g1 (app [true, false, true, false] L))) (show steps 12 ⟨app [false, true, false] L, app [true, false, false] (E b), .E⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, true, false] (E b)), .E⟩ from rfl)⟩

theorem a1_FA {e w : List T} (h0 : Means .Eh w e) : FA (.one :: w) (.O :: e) := by
  obtain ⟨⟨n0, g0FH1⟩, ⟨m0, g0FH2⟩⟩ := h0
  exact ⟨1 + m0 + 1, fun L => sq (sq (show steps 1 ⟨app [true, false] L, app [true] (E w), .B⟩ = some ⟨app [true, true, false] L, app [] (E w), .C⟩ from rfl) (g0FH2 (app [false] L))) (show steps 1 ⟨app [] L, app [false, false, false, false, false] (E e), .D⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false, false] (E e)), .E⟩ from rfl)⟩

theorem hL_FH1 {e w : List T} (h0 : Means .Eh w e) : FH1 (.L :: w) (.L :: e) := by
  obtain ⟨⟨n0, g0FH1⟩, ⟨m0, g0FH2⟩⟩ := h0
  exact ⟨8 + n0 + 12, fun L => sq (sq (show steps 8 ⟨app [true, false] L, app [true, false, true, false] (E w), .C⟩ = some ⟨app [true, false, true, false, true, false] L, app [] (E w), .C⟩ from rfl) (g0FH1 (app [true, false, true, false] L))) (show steps 12 ⟨app [false, true, false] L, app [true, false, false, true, false] (E e), .E⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, true, false, true, false] (E e)), .E⟩ from rfl)⟩

theorem hL_FH2 {e w : List T} (h0 : Means .Eh w e) : FH2 (.L :: w) (.L :: e) := by
  obtain ⟨⟨n0, g0FH1⟩, ⟨m0, g0FH2⟩⟩ := h0
  exact ⟨8 + n0 + 8, fun L => sq (sq (show steps 8 ⟨app [true, true] L, app [true, false, true, false] (E w), .C⟩ = some ⟨app [true, false, true, false, true, true] L, app [] (E w), .C⟩ from rfl) (g0FH1 (app [true, false, true, true] L))) (show steps 8 ⟨app [false, true, true] L, app [true, false, false, true, false] (E e), .E⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false, true, false, true, false] (E e)), .D⟩ from rfl)⟩

theorem hO_FH1 {w : List T}  : FH1 (.O :: w) (.one :: w) := by
  exact ⟨11, fun L => (show steps 11 ⟨app [true, false] L, app [false, false, false] (E w), .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, true] (E w)), .E⟩ from rfl)⟩

theorem hO_FH2 {w : List T}  : FH2 (.O :: w) (.one :: w) := by
  exact ⟨7, fun L => (show steps 7 ⟨app [true, true] L, app [false, false, false] (E w), .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false, true] (E w)), .D⟩ from rfl)⟩

theorem hI_FH1 {e w : List T} (h0 : Means .E0 w e) : FH1 (.I :: w) e := by
  obtain ⟨⟨n0, g0FO1⟩, ⟨m0, g0FO2⟩⟩ := h0
  exact ⟨4 + m0 + 6, fun L => sq (sq (show steps 4 ⟨app [true, false] L, app [true, false, false] (E w), .C⟩ = some ⟨app [true, false, true, false] L, app [false] (E w), .C⟩ from rfl) (g0FO2 (app [true, false] L))) (show steps 6 ⟨app [false] L, app [true, false, false] (E e), .E⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false] (E e)), .E⟩ from rfl)⟩

theorem hI_FH2 {e w : List T} (h0 : Means .E0 w e) : FH2 (.I :: w) e := by
  obtain ⟨⟨n0, g0FO1⟩, ⟨m0, g0FO2⟩⟩ := h0
  exact ⟨4 + m0 + 2, fun L => sq (sq (show steps 4 ⟨app [true, true] L, app [true, false, false] (E w), .C⟩ = some ⟨app [true, false, true, true] L, app [false] (E w), .C⟩ from rfl) (g0FO2 (app [true, true] L))) (show steps 2 ⟨app [true] L, app [true, false, false] (E e), .E⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false] (E e)), .D⟩ from rfl)⟩

theorem hNil_FH1  : FH1 [] [.I] := by
  refine ⟨11, fun L => ?_⟩
  have s := (show steps 11 ⟨app [true, false] L, app [] (app (List.replicate 14 false) blank), .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false] blank), .E⟩ from rfl)
  rw [blank_pad, app_blank_ext [false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false] [false, false, true, false, true, false, false] (by decide)] at s
  exact s

theorem hNil_FH2  : FH2 [] [.I] := by
  refine ⟨7, fun L => ?_⟩
  have s := (show steps 7 ⟨app [true, true] L, app [] (app (List.replicate 14 false) blank), .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false] blank), .D⟩ from rfl)
  rw [blank_pad, app_blank_ext [false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false] [false, false, false, false, true, false, false] (by decide)] at s
  exact s

theorem oO_FO1 {w : List T}  : FO1 (.O :: w) (.L :: w) := by
  exact ⟨15, fun L => (show steps 15 ⟨app [false, false] L, app [false, false, false, false] (E w), .B⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, true, false] (E w)), .E⟩ from rfl)⟩

theorem oO_FO2 {w : List T}  : FO2 (.O :: w) (.L :: w) := by
  exact ⟨11, fun L => (show steps 11 ⟨app [true, false] L, app [false, false, false, false] (E w), .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, true, false] (E w)), .E⟩ from rfl)⟩

theorem oL_FO1 {a w : List T} (h0 : Means .A (.x :: w) a) : FO1 (.L :: w) (.O :: a) := by
  obtain ⟨n0, g0⟩ := h0
  exact ⟨9 + n0 + 3, fun L => sq (sq (show steps 9 ⟨app [false, false] L, app [false, true, false, true, false] (E w), .B⟩ = some ⟨app [true, false, true, true, false] L, app [true, false] (E w), .B⟩ from rfl) (g0 (app [true, true, false] L))) (show steps 3 ⟨app [true, false] L, app [true, false, false] (E a), .E⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false, false] (E a)), .E⟩ from rfl)⟩

theorem oL_FO2 {a w : List T} (h0 : Means .A (.x :: w) a) : FO2 (.L :: w) (.O :: a) := by
  obtain ⟨n0, g0⟩ := h0
  exact ⟨5 + n0 + 3, fun L => sq (sq (show steps 5 ⟨app [true, false] L, app [false, true, false, true, false] (E w), .C⟩ = some ⟨app [true, false, true, true, false] L, app [true, false] (E w), .B⟩ from rfl) (g0 (app [true, true, false] L))) (show steps 3 ⟨app [true, false] L, app [true, false, false] (E a), .E⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false, false] (E a)), .E⟩ from rfl)⟩

theorem oI_FO1 {w : List T}  : FO1 (.I :: w) (.O :: .one :: w) := by
  exact ⟨15, fun L => (show steps 15 ⟨app [false, false] L, app [false, true, false, false] (E w), .B⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false, false, true] (E w)), .E⟩ from rfl)⟩

theorem oI_FO2 {w : List T}  : FO2 (.I :: w) (.O :: .one :: w) := by
  exact ⟨11, fun L => (show steps 11 ⟨app [true, false] L, app [false, true, false, false] (E w), .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false, false, true] (E w)), .E⟩ from rfl)⟩

theorem oNil_FO1  : FO1 [] [.L] := by
  refine ⟨15, fun L => ?_⟩
  have s := (show steps 15 ⟨app [false, false] L, app [false] (app (List.replicate 14 false) blank), .B⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false] blank), .E⟩ from rfl)
  rw [blank_pad, app_blank_ext [false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false] [false, false, true, false, true, false] (by decide)] at s
  exact s

theorem oNil_FO2  : FO2 [] [.L] := by
  refine ⟨11, fun L => ?_⟩
  have s := (show steps 11 ⟨app [true, false] L, app [false] (app (List.replicate 14 false) blank), .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false] blank), .E⟩ from rfl)
  rw [blank_pad, app_blank_ext [false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false] [false, false, true, false, true, false] (by decide)] at s
  exact s

theorem round_run {S a : List T} (h0 : FA S a) :
    ∃ n, 1 ≤ n ∧ ∀ L, steps n ⟨app [false, false] L, app [false, false, false, true, false] (E S), .E⟩ =
      some ⟨L, app [false, false, false, true, false, true, false] (E a), .E⟩ := by
  obtain ⟨n0, g0⟩ := h0
  exact ⟨7 + n0 + 16, by omega, fun L => sq (sq (show steps 7 ⟨app [false, false] L, app [false, false, false, true, false] (E S), .E⟩ = some ⟨app [true, false, true, true, false, false, false] L, app [] (E S), .B⟩ from rfl) (g0 (app [true, true, false, false, false] L))) (show steps 16 ⟨app [true, false, false, false] L, app [true, false, false] (E a), .E⟩ = some ⟨app [] L, app [false, false, false, true, false, true, false] (E a), .E⟩ from rfl)⟩

/-- Every token rule of the twin is a run of this machine, from every entry form of its kind. -/
theorem sound {k w w'} (h : TV k w w') : Means k w w' := by
  induction h with
  | aL _ _ ih1 ih2 => exact aL_FA ih1 ih2
  | aO w => exact aO_FA
  | aI _ ih => exact aI_FA ih
  | aNil => exact aNil_FA
  | az w => exact az_FA
  | axO w => exact axO_FA
  | axI _ ih => exact axI_FA ih
  | axL _ _ ih1 ih2 => exact axL_FA ih1 ih2
  | a1 _ ih => exact a1_FA ih
  | axEnd _ ih => show FA [.x] _; unfold FA; rw [E_x_nil]; exact ih
  | hL _ ih => exact ⟨hL_FH1 ih, hL_FH2 ih⟩
  | hO w => exact ⟨hO_FH1, hO_FH2⟩
  | hI _ ih => exact ⟨hI_FH1 ih, hI_FH2 ih⟩
  | hNil => exact ⟨hNil_FH1, hNil_FH2⟩
  | oO w => exact ⟨oO_FO1, oO_FO2⟩
  | oL _ ih => exact ⟨oL_FO1 ih, oL_FO2 ih⟩
  | oI w => exact ⟨oI_FO1, oI_FO2⟩
  | oNil => exact ⟨oNil_FO1, oNil_FO2⟩

/-! ## Rounds from blank tape -/

/-- From blank tape, after 4 steps: `E` on `0 0 0 1 0 · E []` with blank tape to the left. -/
theorem start : steps 4 H83189.init = some ⟨blank, app [false, false, false, true, false] (E []), .E⟩ := by
  have h : steps 4 ⟨blank, blank, .A⟩ = some ⟨blank, app [false, false, false, true] blank, .E⟩ := rfl
  rw [show app [false, false, false, true, false] (E []) = app [false, false, false, true] blank from
    app_blank_ext _ _ (by decide)]
  exact h

theorem step_of_good {w} (h : Good w) : ∃ a, TV .A w a := by
  obtain ⟨r, hr, _⟩ := Z36869.total h 1
  obtain ⟨a, ha, h0⟩ := hr.succ_inv
  exact ⟨a, ha⟩

/-! ## From round 9 on

The rounds from blank tape do not all have one defect: round 2's defect survives (`F36869.old_hyp_false` in the
twin's `Fuel.lean`), so a reduction "every round's defect dies, from round 0" would be vacuous. As on the twin, the
reduction starts at round 9, whose tape `x a9` is clean behind the defect, and asks that every round's defect needs
at most one visit (`F36869.nx`, `F36869.R9` from the twin's `Need.lean`). -/

/-- The bits of a word list, head first. -/
def flatK : List T → List Bool
  | [] => []
  | t :: w => Z36869.bits t ++ flatK w

theorem E_flat (w : List T) : E w = app (flatK w) blank := by
  induction w with
  | nil => rfl
  | cons t w ih => show app (Z36869.bits t) (E w) = _; rw [ih, flatK, TM.app_app]

/-- The right half tape at the start of round 9, as the list simulator leaves it (no trailing blanks). -/
def r9 : List Bool := ([false, false, false, true, false] ++ flatK (.x :: F36869.a9)).dropLast.dropLast

theorem r9_eq : [false, false, false, true, false] ++ flatK (.x :: F36869.a9) = r9 ++ [false, false] := by decide

theorem round9_f : H83189.fsteps 7834 (TM.FCfg.blank .A) = some ⟨[], r9, .E⟩ := by decide +kernel

/-- From blank tape this machine reaches the start of round 9, E on `0 0 0 1 0 · x a9` with blank tape to the left,
at step 7,834 (kernel evaluation; the twin gets there at step 5,848). -/
theorem round9 : steps 7834 H83189.init =
    some ⟨blank, app [false, false, false, true, false] (E (.x :: F36869.a9)), .E⟩ := by
  have h := TM.blank_reaches H83189.trans round9_f
  show TM.steps H83189.trans 7834 (TM.blankCfg .A) = _
  rw [h]
  have e1 : app r9 blank = app [false, false, false, true, false] (E (.x :: F36869.a9)) := by
    rw [E_flat, TM.app_app, r9_eq, ← TM.app_app]
    show app r9 blank = app r9 (cons false (cons false blank))
    rw [TM.cons_false_blank, TM.cons_false_blank]
  show some (⟨app [] blank, app r9 blank, .E⟩ : H83189.Config) = _
  rw [e1]; rfl

theorem runs9 (H : ∀ W, F36869.R9 W → F36869.nx W ≤ 1) :
    ∀ k, ∃ W n, F36869.R9 W ∧ k ≤ n ∧
      steps n H83189.init = some ⟨blank, app [false, false, false, true, false] (E (.x :: W)), .E⟩ := by
  intro k
  induction k with
  | zero => exact ⟨F36869.a9, 7834, F36869.R9.base, by omega, round9⟩
  | succ k ih =>
    obtain ⟨W, n, hW, hk, hn⟩ := ih
    have hg : Good (.x :: W) := Or.inr ⟨[], .x, W, Z36869.clean_nil, Or.inl rfl, F36869.r9_clean H hW, rfl⟩
    obtain ⟨a, ha⟩ := step_of_good hg
    obtain ⟨m, hm1, hm⟩ := round_run (sound ha)
    refine ⟨a, n + m, F36869.R9.next hW ha, by omega, ?_⟩
    have h := hm blank
    rw [show app [false, false] blank = blank by simp only [TM.app_cons, TM.app_nil, TM.cons_false_blank]] at h
    exact sq hn h

/-- **The reduction.** If in every round from round 9 on the defect in front needs at most one visit (the twin's
hypothesis in `F36869.nonhalt_of_need`, word for word), this machine never halts from blank tape. -/
theorem nonhalt_of_need (H : ∀ W, F36869.R9 W → F36869.nx W ≤ 1) : ¬ H83189.HaltsFromBlank := by
  apply TM.not_halts_of_forall
  apply TM.forall_of_unbounded _ (fun m => ∃ W, steps m H83189.init =
    some ⟨blank, app [false, false, false, true, false] (E (.x :: W)), .E⟩)
  · intro n
    obtain ⟨W, m, _, hm, h⟩ := runs9 H n
    exact ⟨m, hm, W, h⟩
  · rintro m ⟨W, h⟩
    exact ⟨_, h⟩

end K83189
