import Wall

/-! # Rounds on a list of blocks: the induction

Before the copy loop of a wall trip the head works on the blocks next to the level, and how it handles a block
depends on what it carries from the block before; a round may sweep part of the list, or all of it, more than once.
`py/rework.py` describes a round as the machine walks:

* the tape left of the head is a list of blocks `(s, b)` (a separator cell `s`, then `b` pairs `10`), nearest
  first, ending on blank tape: `itp L blank`;
* a *left mode* `m` (state `lq m`, cells `llc m` between the list and the head, the head on the cell `lu m`)
  crosses the nearest block: it turns back inside it (`refl`: the block becomes the blocks `news`, the head goes
  right in a *right mode* `r`, with cells `rc r` between the list and the head), or comes out on its far side in a
  new left mode, the block turned into a piece of tape `gT g t` right of the head (`cont`);
* a right mode crosses such a piece back, over the nearest block `(s, E)` of the list (`pass`: that block becomes
  the blocks `news`), or turns left again at the list (`bounce`: a left mode, the rest of the piece to its right).

`go n T` computes a sweep (`sw`) or a crossing (`rx`) by these cases, with `n` a bound on the depth of the
recursion.  Given the cases as functions (`Sys`) and a proof of each (`Sys.Ok`: one symbolic run each, generated in
`Rework.lean`), `go_ok` proves by induction on `n` that the machine does what `go` says.  Hand-written; kernel only. -/

namespace BB6e
open TM

/-- A block: its separator and its number of pairs. -/
abbrev Item := Bool × Nat

/-- The blocks of `l` (nearest first) in front of the tape `X`. -/
def itp : List Item → Tape → Tape
  | [], X => X
  | (s, b) :: l, X => rep b P (cons s (itp l X))

theorem itp_append (l1 l2 : List Item) (X : Tape) : itp (l1 ++ l2) X = itp l1 (itp l2 X) := by
  induction l1 with
  | nil => rfl
  | cons a l ih => obtain ⟨s, b⟩ := a; simp only [List.cons_append, itp, ih]

theorem nat_eo (b : Nat) : ∃ u, b = 2 * u ∨ b = 2 * u + 1 := ⟨b / 2, by omega⟩

/-- What a left mode does at a block. -/
inductive LRes (LM RM GF : Type) where
  | refl (r : RM) (news : List Item)
  | cont (m : LM) (g : GF) (t : Nat)
  | stuck

/-- What a right mode does at a piece. -/
inductive XRes (LM RM GF : Type) where
  | pass (r : RM) (news : List Item)
  | bounce (m : LM) (news : List Item) (g : GF) (t : Nat)
  | stuck

/-- The cases: modes, pieces and what each mode does at each block or piece. -/
structure Sys where
  LM : Type
  RM : Type
  GF : Type
  lq : LM → St
  llc : LM → List Bool
  lu : LM → Bool
  rq : RM → St
  rc : RM → List Bool
  /-- The piece `g` with parameter `t` in front of `Y`. -/
  gT : GF → Nat → Tape → Tape
  /-- The tape right of the head when a crossing of `g` ends (`Y` for a block's piece). -/
  gF : GF → Tape → Tape
  /-- A block `(s, b)` with more blocks to its left. -/
  leftC : LM → Bool → Nat → LRes LM RM GF
  /-- The last block `(false, b)`, on blank tape. -/
  lastC : LM → Nat → LRes LM RM GF
  /-- A piece `g` with parameter `t` over the nearest block `(s, E)`. -/
  rxC : RM → Bool → GF → Nat → Nat → XRes LM RM GF

namespace Sys
variable (S : Sys)

/-- Each case is a run of the machine. -/
structure Ok : Prop where
  left : ∀ m s b X Y, match S.leftC m s b with
    | .refl r news => ∃ k, steps k ⟨app (S.llc m) (rep b P (cons s X)), cons (S.lu m) Y, S.lq m⟩
        = some ⟨app (S.rc r) (itp news X), Y, S.rq r⟩
    | .cont m' g t => (∀ Y, S.gF g Y = Y) ∧ ∃ k, steps k ⟨app (S.llc m) (rep b P (cons s X)), cons (S.lu m) Y, S.lq m⟩
        = some ⟨app (S.llc m') X, cons (S.lu m') (S.gT g t Y), S.lq m'⟩
    | .stuck => True
  last : ∀ m b Y, match S.lastC m b with
    | .refl r news => ∃ k, steps k ⟨app (S.llc m) (rep b P blank), cons (S.lu m) Y, S.lq m⟩
        = some ⟨app (S.rc r) (itp news blank), Y, S.rq r⟩
    | _ => True
  rx : ∀ r s g t E Z Y, match S.rxC r s g t E with
    | .pass r' news => ∃ k, steps k ⟨app (S.rc r) (rep E P (cons s Z)), S.gT g t Y, S.rq r⟩
        = some ⟨app (S.rc r') (itp news Z), S.gF g Y, S.rq r'⟩
    | .bounce m news g' t' => (∀ Y, S.gF g' Y = S.gF g Y) ∧ ∃ k, steps k ⟨app (S.rc r) (rep E P (cons s Z)), S.gT g t Y, S.rq r⟩
        = some ⟨app (S.llc m) (itp news Z), cons (S.lu m) (S.gT g' t' Y), S.lq m⟩
    | .stuck => True

/-- A sweep from a left mode, or a crossing of a piece from a right mode. -/
inductive Task where
  | sw (m : S.LM) (L : List Item)
  | rx (r : S.RM) (g : S.GF) (t : Nat) (L : List Item)

/-- The rounds' function, `n` bounding the depth. -/
def go : Nat → S.Task → Option (S.RM × List Item)
  | 0, _ => none
  | _ + 1, .sw _ [] => none
  | _ + 1, .sw m [(s, b)] =>
    match s, S.lastC m b with
    | false, .refl r news => some (r, news)
    | _, _ => none
  | n + 1, .sw m ((s, b) :: x :: L) =>
    match S.leftC m s b with
    | .refl r news => some (r, news ++ x :: L)
    | .cont m' g t =>
      match go n (.sw m' (x :: L)) with
      | some (r, L') => go n (.rx r g t L')
      | none => none
    | .stuck => none
  | _ + 1, .rx _ _ _ [] => none
  | n + 1, .rx r g t ((s, E) :: Z) =>
    match S.rxC r s g t E with
    | .pass r' news => some (r', news ++ Z)
    | .bounce m news g' t' =>
      match go n (.sw m (news ++ Z)) with
      | some (r2, L3) => go n (.rx r2 g' t' L3)
      | none => none
    | .stuck => none

def Task.start : S.Task → Tape → Cfg St
  | .sw m L, Y => ⟨app (S.llc m) (itp L blank), cons (S.lu m) Y, S.lq m⟩
  | .rx r g t L, Y => ⟨app (S.rc r) (itp L blank), S.gT g t Y, S.rq r⟩

def Task.fin : S.Task → Tape → Tape
  | .sw _ _, Y => Y
  | .rx _ g _ _, Y => S.gF g Y

theorem go_ok (h : S.Ok) : ∀ n (T : S.Task) r L', S.go n T = some (r, L') →
    ∀ Y, ∃ k, steps k (T.start S Y) = some ⟨app (S.rc r) (itp L' blank), T.fin S Y, S.rq r⟩ := by
  intro n
  induction n with
  | zero => intro T r L' hg; simp [go] at hg
  | succ n ih =>
    intro T r L' hg Y
    cases T with
    | sw m L =>
      match L, hg with
      | [], hg => simp [go] at hg
      | [(s, b)], hg =>
        have hc := h.last m b Y
        cases s with
        | true => simp [go] at hg
        | false =>
          simp only [go] at hg
          cases hl : S.lastC m b with
          | refl r0 news =>
            simp only [hl] at hg hc
            simp only [Option.some.injEq, Prod.mk.injEq] at hg
            obtain ⟨rfl, rfl⟩ := hg
            simp only [Task.start, Task.fin, itp, cons_false_blank]
            exact hc
          | cont _ _ _ => simp [hl] at hg
          | stuck => simp [hl] at hg
      | (s, b) :: x :: L, hg =>
        have hc := h.left m s b (itp (x :: L) blank) Y
        simp only [go] at hg
        cases hl : S.leftC m s b with
        | refl r0 news =>
          simp only [hl] at hg hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          simp only [Task.start, Task.fin, itp_append]
          exact hc
        | cont m' g t =>
          simp only [hl] at hg hc
          obtain ⟨hF, k1, h1⟩ := hc
          cases hgo : S.go n (.sw m' (x :: L)) with
          | none => simp [hgo] at hg
          | some p =>
            obtain ⟨r1, L1⟩ := p
            simp only [hgo] at hg
            obtain ⟨k2, h2⟩ := ih (.sw m' (x :: L)) r1 L1 hgo (S.gT g t Y)
            obtain ⟨k3, h3⟩ := ih (.rx r1 g t L1) r L' hg Y
            simp only [Task.start, Task.fin] at h2 h3
            rw [hF] at h3
            exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩
        | stuck => simp [hl] at hg
    | rx r0 g t L =>
      match L, hg with
      | [], hg => simp [go] at hg
      | (s, E) :: Z, hg =>
        have hc := h.rx r0 s g t E (itp Z blank) Y
        simp only [go] at hg
        cases hl : S.rxC r0 s g t E with
        | pass r1 news =>
          simp only [hl] at hg hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          simp only [Task.start, Task.fin, itp_append, itp]
          exact hc
        | bounce m news g' t' =>
          simp only [hl] at hg hc
          obtain ⟨hF, k1, h1⟩ := hc
          cases hgo : S.go n (.sw m (news ++ Z)) with
          | none => simp [hgo] at hg
          | some p =>
            obtain ⟨r1, L1⟩ := p
            simp only [hgo] at hg
            obtain ⟨k2, h2⟩ := ih (.sw m (news ++ Z)) r1 L1 hgo (S.gT g' t' Y)
            obtain ⟨k3, h3⟩ := ih (.rx r1 g' t' L1) r L' hg Y
            simp only [Task.start, Task.fin, itp_append] at h2 h3
            rw [hF] at h3
            exact ⟨k1 + (k2 + k3), steps_seq trans h1 (steps_seq trans h2 h3)⟩
        | stuck => simp [hl] at hg

end Sys

end BB6e
