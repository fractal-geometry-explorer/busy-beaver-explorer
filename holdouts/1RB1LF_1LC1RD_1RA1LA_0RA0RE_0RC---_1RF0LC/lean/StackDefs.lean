import Reduction

/-!
# The wall as a stack of counters: definitions

Words are written left to right; `b = 110`.  A wall is `1 X_n ... X_1` (bottom to top) with items

* `It.o k`: the open counter `K(k) = b^k 1^3 b 1`,
* `It.c k`: the closed counter `K'(k) = b^k 1^6`,

kept in a list with the TOP item first, so that the tape left of the head (nearest cell first) is built by
structural recursion: `wt (x :: ws) = itT x (wt ws)`, `wt [] = 1 0^inf`.

The part of the tape right of the wall is a *context* `Cx`: at the top of the stack the block is followed by
`1 0^inf`; an item that passes a signal down makes a new block for the item below, followed by the marker
`1 0 1 0` and what is left of its own block (`deep m c`: `1 0 1 0 b^m` and then the context `c` of the item above).

The three configurations where a signal arrives or an answer is given (`W` a wall tape):

* `CALL W x y c`: `W b^x 111 F> b^(y+1) rhs(c)`; with `x = 0` it is the signal *odd* (N odd) arriving at `W`;
  the junction of the transfer loop is `CALL W x y .top` (`J` of `Sweeps.lean`);
* `QQ L n c`: `L F> 1 b^n rhs(c)` where `W = L 1`: the head on the last cell of the wall: the signal *even*;
* `START W M c`: `W A> 0 b^M rhs(c)`: the answer; `START W N .top` is the step start `S W N` of `Reduction.lean`.

`Seg`, `ev`, `normA`: a small normaliser for tapes made of words and repeats, used to prove that two ways of
writing a tape are equal (`tape_eq`, by evaluation of `normA` in the kernel).
-/

namespace H3292

open TM

/-! ## Normalising tapes -/

/-- A piece of tape: a word, or a word repeated `n` times. -/
inductive Seg where
  | l (w : List Bool)
  | r (n : Nat) (w : List Bool)

/-- The tape of a list of pieces in front of `T`. -/
def ev : List Seg → Tape → Tape
  | [], T => T
  | .l w :: s, T => app w (ev s T)
  | .r n w :: s, T => rep n w (ev s T)

/-- Push the word before a repeat into it, cell by cell, while its last cell is the last cell of the repeated
word (`x (y x)^n = (x y)^n x`).  Arguments reversed: `ra` the word before, `rw` the repeated word; `mv` the cells
moved behind the repeat. -/
def pushR : Nat → List Bool → List Bool → List Bool → List Bool × List Bool × List Bool
  | f + 1, a :: ra, b :: rw, mv => if a = b then pushR f ra (rw ++ [b]) (a :: mv) else (a :: ra, b :: rw, mv)
  | _, ra, rw, mv => (ra, rw, mv)

theorem pushR_ok (n : Nat) (T : Tape) : ∀ f ra rw mv,
    app ra.reverse (rep n rw.reverse (app mv T)) =
      app (pushR f ra rw mv).1.reverse (rep n (pushR f ra rw mv).2.1.reverse (app (pushR f ra rw mv).2.2 T))
  | 0, _, _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | _ + 1, _ :: _, [], _ => rfl
  | f + 1, a :: ra, b :: rw, mv => by
    simp only [pushR]
    split
    · next h =>
      subst h
      rw [← pushR_ok n T f ra (rw ++ [a]) (a :: mv)]
      simp only [List.reverse_cons, List.reverse_append, List.reverse_nil, List.nil_append, List.cons_append]
      rw [← app_app, rep_rotate n [a] (rw.reverse ++ [a]) (a :: rw.reverse) (by simp)]
      rfl
    · rfl

/-- Normal form: words pushed right through repeats as far as they go. -/
def normA : List Bool → List Seg → List Seg
  | acc, [] => [.l acc]
  | acc, .l w :: s => normA (acc ++ w) s
  | acc, .r n w :: s =>
    match pushR acc.length acc.reverse w.reverse [] with
    | (ra, rw, mv) => .l ra.reverse :: .r n rw.reverse :: normA mv s

theorem normA_ok (T : Tape) : ∀ s acc, ev (normA acc s) T = app acc (ev s T)
  | [], _ => rfl
  | .l w :: s, acc => by simp only [normA, ev, normA_ok T s, app_app]
  | .r n w :: s, acc => by
    have h := pushR_ok n (ev s T) acc.length acc.reverse w.reverse []
    simp only [List.reverse_reverse, app_nil] at h
    simp only [normA, ev, normA_ok T s, h]

theorem tape_eq (s1 s2 : List Seg) (T : Tape) (h : normA [] s1 = normA [] s2) : ev s1 T = ev s2 T := by
  rw [← app_nil (ev s1 T), ← normA_ok, h, normA_ok, app_nil]

/-- Drop the zeros at the end of the last word (for tapes ending in blank). -/
def trimSeg : List Seg → List Seg
  | [] => []
  | [.l w] => [.l (trim w)]
  | x :: s => x :: trimSeg s

theorem trimSeg_ok : ∀ s, ev (trimSeg s) blank = ev s blank
  | [] => rfl
  | [.l w] => trim_spec w
  | [.r _ _] => rfl
  | .l w :: x :: s => by
    show app w (ev (trimSeg (x :: s)) blank) = _
    rw [trimSeg_ok (x :: s)]; rfl
  | .r n w :: x :: s => by
    show rep n w (ev (trimSeg (x :: s)) blank) = _
    rw [trimSeg_ok (x :: s)]; rfl

theorem tape_eqB (s1 s2 : List Seg) (h : trimSeg (normA [] s1) = trimSeg (normA [] s2)) :
    ev s1 blank = ev s2 blank := by
  rw [← app_nil (ev s1 blank), ← normA_ok, ← trimSeg_ok, h, trimSeg_ok, normA_ok, app_nil]

theorem cfg_eq {l1 l2 r1 r2 : Tape} {q : St} (hl : l1 = l2) (hr : r1 = r2) :
    (⟨l1, r1, q⟩ : Config) = ⟨l2, r2, q⟩ := by subst hl; subst hr; rfl

/-! ## Walls, contexts, interfaces -/

/-- An item of the wall: an open counter `K(k) = b^k 1^3 b 1` or a closed counter `K'(k) = b^k 1^6`. -/
inductive It where
  | o (k : Nat)
  | c (k : Nat)
  deriving DecidableEq, Repr

/-- An item in front of the tape below it (cells nearest the head first). -/
def itT : It → Tape → Tape
  | .o k, L => app [true, false, true, true, true, true, true] (rep k [false, true, true] L)
  | .c k, L => app [true, true, true, true, true, true] (rep k [false, true, true] L)

/-- The wall `1 X_n ... X_1` as the tape left of the head; the list has the top item `X_1` first. -/
def wt : List It → Tape
  | [] => cons true blank
  | x :: ws => itT x (wt ws)

/-- The wall without its last cell (which is always 1). -/
def wtl : List It → Tape
  | [] => blank
  | .o k :: ws => app [false, true, true, true, true, true] (rep k [false, true, true] (wt ws))
  | .c k :: ws => app [true, true, true, true, true] (rep k [false, true, true] (wt ws))

theorem wt_eq : ∀ ws, wt ws = cons true (wtl ws)
  | [] => rfl
  | .o _ :: _ => rfl
  | .c _ :: _ => rfl

/-- What follows the block: `top` is `1 0^inf`; `deep m c` is `1 0 1 0 b^m` followed by `rhs c`. -/
inductive Cx where
  | top
  | deep (m : Nat) (c : Cx)

def rhs : Cx → Tape
  | .top => cons true blank
  | .deep m c => cons true (cons false (cons true (cons false (rep m [true, true, false] (rhs c)))))

/-- Using up `u` copies of the block of the context (none at the top). -/
def Cx.sub : Cx → Nat → Option Cx
  | .top, _ => some .top
  | .deep m c, u => if u ≤ m then some (.deep (m - u) c) else none

theorem Cx.sub_zero : ∀ c : Cx, c.sub 0 = some c
  | .top => rfl
  | .deep m c => by simp [Cx.sub]

theorem Cx.sub_add : ∀ (c : Cx) (a b : Nat) {c' : Cx}, c.sub (a + b) = some c' →
    ∃ c1, c.sub a = some c1 ∧ c1.sub b = some c'
  | .top, _, _, _, h => ⟨.top, rfl, h⟩
  | .deep m c, a, b, c', h => by
    simp only [Cx.sub] at h
    split at h
    · next hab =>
      refine ⟨.deep (m - a) c, ?_, ?_⟩
      · simp [Cx.sub, show a ≤ m by omega]
      · simp only [Cx.sub, show b ≤ m - a by omega, ite_true, ← h, show m - a - b = m - (a + b) by omega]
    · cases h

/-- `W b^x 111 F> b^(y+1) rhs(c)`: the junction; with `x = 0` the signal odd arriving at the wall `W`. -/
def CALL (W : Tape) (x y : Nat) (c : Cx) : Config :=
  ⟨app [true, true, true] (rep x [false, true, true] W), rep (y + 1) [true, true, false] (rhs c), .F⟩

/-- `L F> 1 b^n rhs(c)` (the wall is `L 1`): the signal even arriving at the wall. -/
def QQ (L : Tape) (n : Nat) (c : Cx) : Config :=
  ⟨L, cons true (rep n [true, true, false] (rhs c)), .F⟩

/-- `W A> 0 b^M rhs(c)`: the answer of the wall; at the top, the start of the next step. -/
def START (W : Tape) (M : Nat) (c : Cx) : Config :=
  ⟨W, cons false (rep M [true, true, false] (rhs c)), .A⟩

/-- Reachability. -/
def Reach (a b : Config) : Prop := ∃ n, steps n a = some b

theorem Reach.trans {a b c : Config} (h1 : Reach a b) (h2 : Reach b c) : Reach a c := by
  obtain ⟨n, hn⟩ := h1; obtain ⟨m, hm⟩ := h2; exact ⟨n + m, steps_seq H3292.trans hn hm⟩

theorem Reach.of {n : Nat} {a b : Config} (h : steps n a = some b) : Reach a b := ⟨n, h⟩

theorem Reach.refl (a : Config) : Reach a a := ⟨0, rfl⟩

end H3292
