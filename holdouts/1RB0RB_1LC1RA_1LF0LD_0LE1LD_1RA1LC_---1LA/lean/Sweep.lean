import Machine

/-!
# 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA: the exact pass machine

The tape is read in **pairs** of cells whose second cell is 1: the letter `b` is the pair `b 1`, so `x = 11`
(`true`) and `z = 01` (`false`).  A **turn configuration** `RT out rest` has the head in state C on the first
cell of a pair `11`; to its left, the pairs `out` (nearest first) and then blank tape; to its right, after the
pair, the cells `rest` and then blank tape.  At every turn at the right end of the tape `rest = []`.

One **macro step** `mstep out rest` is what the machine does from such a configuration to the next one:

* a **left pass** (`scanF`): C writes 0 into the pair and D, E, C run left.  D skips the pairs `11`; after a pair
  `01` it looks at the next pair: `11` becomes `01` and the pass goes on, `01` becomes `11` and the head turns
  (`turn`).  The pass may instead run off the left end of the word (`edgeD`, `edgeE`) or halt (`halt`: the turn
  would need a pair left of the leftmost one).  At the left end E0 = `1RA` writes a 1 and steps back right, so the
  word gains a pair `0 1` whose first cell is blank (`edgeE_run`, `edgeD_x`, `edgeD_z`);
* a **right pass** (`apass`): A and B run right over the cells two at a time; a pair `a 1` becomes `(¬a) 1`, a pair
  `1 0` *bounces* (8 steps: it becomes `0 1` and the pair before it has its first cell flipped back), and a pair
  `0 0` (blank tape, or a gap) ends the pass in a new turn configuration.

The lemmas are proved for all lists (by induction), so `mstep_sound` is the machine itself, read pass by pass:
`mstep out rest = .go n out' rest'` means `steps n (RT out rest) = some (RT out' rest')`, and `.halt n` means the
machine halts after `n` steps.  Everything is checked by Lean's kernel.
-/

namespace H73071

open TM

/-- Pairs on the left of the head, nearest first: the letter `b` is the two cells `b 1`, the `1` nearer. -/
def pl : List Bool → Tape → Tape
  | [], L => L
  | b :: bs, L => cons true (cons b (pl bs L))

/-- The cells of a list of pairs, in reading order. -/
def cells : List Bool → List Bool
  | [] => []
  | b :: bs => b :: true :: cells bs

theorem pl_append (a b : List Bool) (L : Tape) : pl (a ++ b) L = pl a (pl b L) := by
  induction a with
  | nil => rfl
  | cons x a ih => simp only [List.cons_append, pl, ih]

/-- The turn configuration. -/
def RT (out rest : List Bool) : Config := ⟨pl out blank, cons true (cons true (app rest blank)), .C⟩

/-- The start of a right pass: A on the first of the cells `cl`, the pairs `cs` on the left. -/
def AS (cs cl : List Bool) : Config := ⟨pl cs blank, app cl blank, .A⟩

/-- The left pass, D on the second cell of the pair `b` (the head of the list), `m` the pairs already passed. -/
def cfgF : List Bool → List Bool → Tape → Config
  | b :: bs, m, R => ⟨cons b (pl bs blank), cons true (app (cells m) R), .D⟩
  | [], m, R => ⟨blank, cons false (app (cells m) R), .D⟩

/-- The left pass, E on the blank cell left of the word. -/
def cfgE (m : List Bool) (R : Tape) : Config := ⟨blank, cons false (app (cells m) R), .E⟩

/-! ## The left pass -/

/-- Outcomes of the left pass, with their step counts (`edgeD n b m` stands for the passed pairs `b :: m`). -/
inductive SR where
  | turn (n : Nat) (cs q : List Bool)
  | edgeD (n : Nat) (b : Bool) (m : List Bool)
  | edgeE (n : Nat) (m : List Bool)
  | halt (n : Nat)

def SR.add : SR → Nat → SR
  | .turn n cs q, k => .turn (n + k) cs q
  | .edgeD n b m, k => .edgeD (n + k) b m
  | .edgeE n m, k => .edgeE (n + k) m
  | .halt n, k => .halt (n + k)

/-- The left pass from `cfgF l (b :: m)`. -/
def scanF : List Bool → Bool → List Bool → SR
  | [], b, m => .edgeD 0 b m
  | true :: bs, b, m => (scanF bs true (b :: m)).add 2
  | [false], b, m => .edgeE 2 (false :: b :: m)
  | false :: true :: cs, b, m => (scanF cs false (false :: b :: m)).add 4
  | false :: false :: c :: cs, b, m => .turn 5 cs (c :: true :: false :: b :: m)
  | [false, false], _, _ => .halt 4

/-- What an outcome says about a configuration. -/
def SR.ok (R : Tape) : SR → Config → Prop
  | .turn n cs q, c => steps n c = some ⟨pl cs blank, app (cells q) R, .A⟩
  | .edgeD n b m, c => steps n c = some (cfgF [] (b :: m) R)
  | .edgeE n m, c => steps n c = some (cfgE m R)
  | .halt n, c => ∃ c', steps n c = some c' ∧ step c' = none

theorem SR.ok_add {R : Tape} {r : SR} {c c' : Config} {k : Nat} (h : steps k c = some c') (h' : r.ok R c') :
    (r.add k).ok R c := by
  cases r with
  | turn n cs q => exact steps_congr trans (by omega) (steps_seq trans h h')
  | edgeD n b m => exact steps_congr trans (by omega) (steps_seq trans h h')
  | edgeE n m => exact steps_congr trans (by omega) (steps_seq trans h h')
  | halt n =>
    obtain ⟨c'', h1, h2⟩ := h'
    exact ⟨c'', steps_congr trans (by omega) (steps_seq trans h h1), h2⟩

theorem fx (bs m : List Bool) (R : Tape) : steps 2 (cfgF (true :: bs) m R) = some (cfgF bs (true :: m) R) := by
  cases bs <;> rfl

theorem fz0 (m : List Bool) (R : Tape) : steps 2 (cfgF [false] m R) = some (cfgE (false :: m) R) := rfl

theorem fzx (cs m : List Bool) (R : Tape) :
    steps 4 (cfgF (false :: true :: cs) m R) = some (cfgF cs (false :: false :: m) R) := by
  cases cs <;> rfl

theorem fzz (c : Bool) (cs m : List Bool) (R : Tape) :
    steps 5 (cfgF (false :: false :: c :: cs) m R) =
      some ⟨pl cs blank, app (cells (c :: true :: false :: m)) R, .A⟩ := by
  cases c <;> rfl

theorem fhalt (m : List Bool) (R : Tape) :
    steps 4 (cfgF [false, false] m R) = some ⟨blank, cons false (app (cells (true :: false :: m)) R), .F⟩
    := rfl

theorem scanF_sound (R : Tape) : ∀ (l : List Bool) (b : Bool) (m : List Bool), (scanF l b m).ok R (cfgF l (b :: m) R)
  | [], _, _ => rfl
  | true :: bs, b, m => SR.ok_add (fx bs (b :: m) R) (scanF_sound R bs true (b :: m))
  | [false], b, m => fz0 (b :: m) R
  | false :: true :: cs, b, m => SR.ok_add (fzx cs (b :: m) R) (scanF_sound R cs false (false :: b :: m))
  | false :: false :: c :: cs, b, m => fzz c cs (b :: m) R
  | [false, false], b, m => ⟨_, fhalt (b :: m) R, rfl⟩

/-! ## The right pass -/

/-- Outcomes of a macro step. -/
inductive MR where
  | go (n : Nat) (out rest : List Bool)
  | halt (n : Nat)
  deriving DecidableEq, Repr

def MR.add : MR → Nat → MR
  | .go n o r, k => .go (n + k) o r
  | .halt n, k => .halt (n + k)

def MR.ok : MR → Config → Prop
  | .go n o r, c => steps n c = some (RT o r)
  | .halt n, c => ∃ c', steps n c = some c' ∧ step c' = none

theorem MR.ok_add {r : MR} {c c' : Config} {k : Nat} (h : steps k c = some c') (h' : r.ok c') :
    (r.add k).ok c := by
  cases r with
  | go n o r => exact steps_congr trans (by omega) (steps_seq trans h h')
  | halt n =>
    obtain ⟨c'', h1, h2⟩ := h'
    exact ⟨c'', steps_congr trans (by omega) (steps_seq trans h h1), h2⟩

/-- The right pass from `AS cs cl`. -/
def apass : List Bool → List Bool → MR
  | cs, a :: true :: cl => (apass ((!a) :: cs) cl).add 2
  | p :: cs, true :: false :: cl => (apass (false :: (!p) :: cs) cl).add 8
  | [], true :: false :: _ => .halt 3
  | cs, false :: false :: cl => .go 2 cs cl
  | p :: cs, [true] => (apass (false :: (!p) :: cs) []).add 8
  | [], [true] => .halt 3
  | cs, [false] => .go 2 cs []
  | cs, [] => .go 2 cs []

theorem a_pair (a : Bool) (cs cl : List Bool) : steps 2 (AS cs (a :: true :: cl)) = some (AS ((!a) :: cs) cl) := by
  cases a <;> rfl

theorem a_bounce (p : Bool) (cs cl : List Bool) :
    steps 8 (AS (p :: cs) (true :: false :: cl)) = some (AS (false :: (!p) :: cs) cl) := by
  cases p <;> rfl

theorem a_bounce_end (p : Bool) (cs : List Bool) : steps 8 (AS (p :: cs) [true]) = some (AS (false :: (!p) :: cs) []) := by
  cases p <;> rfl

theorem a_end (cs cl : List Bool) : steps 2 (AS cs (false :: false :: cl)) = some (RT cs cl) := rfl
theorem a_end1 (cs : List Bool) : steps 2 (AS cs [false]) = some (RT cs []) := rfl
theorem a_end0 (cs : List Bool) : steps 2 (AS cs []) = some (RT cs []) := rfl

theorem apass_sound : ∀ (cs cl : List Bool), (apass cs cl).ok (AS cs cl)
  | cs, a :: true :: cl => MR.ok_add (a_pair a cs cl) (apass_sound ((!a) :: cs) cl)
  | p :: cs, true :: false :: cl => MR.ok_add (a_bounce p cs cl) (apass_sound (false :: (!p) :: cs) cl)
  | [], true :: false :: _ => ⟨_, rfl, rfl⟩
  | cs, false :: false :: cl => a_end cs cl
  | p :: cs, [true] => MR.ok_add (a_bounce_end p cs) (apass_sound (false :: (!p) :: cs) [])
  | [], [true] => ⟨_, rfl, rfl⟩
  | cs, [false] => a_end1 cs
  | cs, [] => a_end0 cs

/-! ## The left end of the tape

This machine differs from its sibling `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA` only in E0 (`1RA` here, `1LA`
there), and E reads a 0 only at the left end of the word.  Here E writes a 1 and steps back right, so the word gains
the pair `0 1` whose first cell is the blank cell left of that 1 (`cons true blank = pl [false] blank`).
-/

theorem cons_true_blank : cons true blank = pl [false] blank := by
  show cons true blank = cons true (cons false blank)
  rw [cons_false_blank]

theorem cons3_true_blank : cons true (cons true (cons true blank)) = pl [true, false] blank := by
  show _ = cons true (cons true (cons true (cons false blank)))
  rw [cons_false_blank]

/-- D on the blank cell left of the word, the last pair passed `11`: E writes a 1 there and steps back, and a right
pass starts one cell out of step with the old pairs. -/
theorem edgeD_x (m rest : List Bool) :
    steps 4 (cfgF [] (true :: m) (app rest blank)) = some (AS [true, false] (true :: (cells m ++ rest))) := by
  have h : steps 4 (cfgF [] (true :: m) (app rest blank)) =
      some ⟨cons true (cons true (cons true blank)), cons true (app (cells m) (app rest blank)), .A⟩ := rfl
  rw [h, app_app, cons3_true_blank]; rfl

/-- The same with the last pair passed `01`: the right pass ends at once, in a turn inside the word. -/
theorem edgeD_z (m rest : List Bool) :
    steps 4 (cfgF [] (false :: m) (app rest blank)) = some (RT [false] (true :: (cells m ++ rest))) := by
  have h : steps 4 (cfgF [] (false :: m) (app rest blank)) =
      some ⟨cons true blank, cons true (cons true (cons true (app (cells m) (app rest blank)))), .C⟩ := rfl
  rw [h, app_app, cons_true_blank]; rfl

/-- E on the blank cell left of the word: a new pair `0 1` (its first cell blank) and a right pass in step with the
old pairs. -/
theorem edgeE_run (m rest : List Bool) :
    steps 1 (cfgE m (app rest blank)) = some (AS [false] (cells m ++ rest)) := by
  have h : steps 1 (cfgE m (app rest blank)) = some ⟨cons true blank, app (cells m) (app rest blank), .A⟩ := rfl
  rw [h, app_app, cons_true_blank]; rfl

/-! ## One macro step -/

def mstep (out rest : List Bool) : MR :=
  match scanF out false [] with
  | .turn n cs q => (apass cs (cells q ++ rest)).add (n + 1)
  | .edgeD n true m => (apass [true, false] (true :: (cells m ++ rest))).add (n + 5)
  | .edgeD n false m => .go (n + 5) [false] (true :: (cells m ++ rest))
  | .edgeE n m => (apass [false] (cells m ++ rest)).add (n + 2)
  | .halt n => .halt (n + 1)

theorem first_step (out rest : List Bool) : steps 1 (RT out rest) = some (cfgF out [false] (app rest blank)) := by
  cases out <;> rfl

theorem mstep_sound (out rest : List Bool) : (mstep out rest).ok (RT out rest) := by
  have h1 := first_step out rest
  have hs := scanF_sound (app rest blank) out false []
  unfold mstep
  cases e : scanF out false [] with
  | turn n cs q =>
    rw [e] at hs
    have hs' : steps n (cfgF out [false] (app rest blank)) = some (AS cs (cells q ++ rest)) := by
      rw [show (AS cs (cells q ++ rest)) = ⟨pl cs blank, app (cells q) (app rest blank), .A⟩ by
        rw [app_app]; rfl]
      exact hs
    exact MR.ok_add (steps_congr trans (by omega) (steps_seq trans h1 hs')) (apass_sound cs _)
  | edgeD n b m =>
    rw [e] at hs
    cases b with
    | true =>
      have h2 := steps_seq trans (steps_seq trans h1 hs) (edgeD_x m rest)
      exact MR.ok_add (steps_congr trans (by omega) h2) (apass_sound _ _)
    | false =>
      have h2 := steps_seq trans (steps_seq trans h1 hs) (edgeD_z m rest)
      exact steps_congr trans (by omega) h2
  | edgeE n m =>
    rw [e] at hs
    have h2 := steps_seq trans (steps_seq trans h1 hs) (edgeE_run m rest)
    exact MR.ok_add (steps_congr trans (by omega) h2) (apass_sound _ _)
  | halt n =>
    rw [e] at hs
    obtain ⟨c', h2, h3⟩ := hs
    exact ⟨c', steps_congr trans (by omega) (steps_seq trans h1 h2), h3⟩

theorem MR.add_go {r : MR} {k n : Nat} {o r' : List Bool} (h : r.add k = .go n o r') : k ≤ n := by
  cases r with
  | go n' o' r'' => simp only [MR.add, MR.go.injEq] at h; omega
  | halt n' => simp only [MR.add, reduceCtorEq] at h

theorem mstep_pos {out rest o r : List Bool} {n : Nat} (h : mstep out rest = .go n o r) : 1 ≤ n := by
  unfold mstep at h
  split at h
  · have := MR.add_go h; omega
  · have := MR.add_go h; omega
  · simp only [MR.go.injEq] at h; omega
  · have := MR.add_go h; omega
  · cases h

/-- Blank tape reaches the first turn configuration (the word `x`) after 2 steps. -/
theorem init_RT : steps 2 init = some (RT [] []) := rfl

end H73071
