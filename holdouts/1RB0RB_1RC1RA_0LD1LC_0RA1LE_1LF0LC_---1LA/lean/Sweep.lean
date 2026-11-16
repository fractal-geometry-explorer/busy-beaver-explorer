import Machine

/-!
# 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA: the exact macro machine

The tape is read in **pairs** of cells whose second cell is 1: the letter `b` is the pair `b 1`, so `x = 11`
(`true`) and `z = 01` (`false`).  A **turn configuration** `RT out` has the head in state D on the second cell of a
pair `11` at the right end of the tape; to its left, the pairs `out` (nearest first) and then blank tape.

One **macro step** `mstep` from `RT out`:

* the head pair becomes `01` (D1, E1), and a **left pass** (`scan`) runs over the pairs: C skips the pairs `11`;
  after a pair `01`, D and E look at the next pair: `11` becomes `01` and the pass goes on, `01` becomes `11` and
  F, A turn at the pair before it (`turn`).  At the very first pair the turn would need the cell left of the word:
  F reads 0 and the machine halts (`halt`);
* a **right pass** (`apass`): A and B flip the first cell of every pair, and at the blank end write a new pair
  `11`; C, D turn back onto it.  So a turn inside the word leads to `RT out'` again;
* the left pass may run off the left end of the word.  Right after a pair `01` (`edgeD`), D0 = `0RA` sends A into
  the first pair, in step, and the right pass leads to `RT out'`.  Otherwise (`edgeF`) C0, D0 send A right one
  cell out of step with the pairs; what follows takes several passes and has no closed form here, so the macro
  machine keeps the configuration as it is, on lists (`FCfg` of `tools/lean/TM/Fin.lean`), and runs it cell by
  cell (`rawRun`) until it is a turn configuration `RT out'` again (`asRT`).

So a state of the macro machine is `.rt out` or `.raw c`.  All lemmas are proved for all lists (by induction):
`mstep_sound` is the machine itself, read macro step by macro step.  Everything is checked by Lean's kernel.
-/

namespace H25821

open TM

/-- Pairs on the left of the head, nearest first: the letter `b` is the two cells `b 1`, the `1` nearer. -/
def pl : List Bool → Tape → Tape
  | [], L => L
  | b :: bs, L => cons true (cons b (pl bs L))

/-- The cells of a list of pairs, in reading order. -/
def cells : List Bool → List Bool
  | [] => []
  | b :: bs => b :: true :: cells bs

/-- The turn configuration: D on the second cell of the last pair `11`, blank tape to its right. -/
def RT (out : List Bool) : Config := ⟨cons true (pl out blank), cons true blank, .D⟩

/-- The start of a right pass: A on the first of the cells `cl`, the pairs `cs` on the left. -/
def AS (cs cl : List Bool) : Config := ⟨pl cs blank, app cl blank, .A⟩

/-- The left pass, in state `s` on the second cell of the pair at the head of the list (on the blank cell left of
the word for `[]`), `m` the pairs already passed, in reading order. -/
def cfgS (s : St) : List Bool → List Bool → Tape → Config
  | b :: bs, m, R => ⟨cons b (pl bs blank), cons true (app (cells m) R), s⟩
  | [], m, R => ⟨blank, cons false (app (cells m) R), s⟩

/-! ## The left pass

`scan true` is C (no pair `01` just passed), `scan false` is D (a pair `01` just passed). -/

/-- Outcomes of the left pass, with their step counts. -/
inductive SR where
  | turn (n : Nat) (cs q : List Bool)
  | edgeD (n : Nat) (m : List Bool)
  | edgeF (n : Nat) (m : List Bool)
  | halt (n : Nat)

def SR.add : SR → Nat → SR
  | .turn n cs q, k => .turn (n + k) cs q
  | .edgeD n m, k => .edgeD (n + k) m
  | .edgeF n m, k => .edgeF (n + k) m
  | .halt n, k => .halt (n + k)

def scan : Bool → List Bool → List Bool → SR
  | true, [], m => .edgeF 0 m
  | false, [], m => .edgeD 0 m
  | true, b :: bs, m => (scan b bs (b :: m)).add 2
  | false, true :: bs, m => (scan true bs (false :: m)).add 2
  | false, false :: c :: cs, m => .turn 3 cs (c :: true :: m)
  | false, [false], _ => .halt 2

def stOf : Bool → St
  | true => .C
  | false => .D

/-- What an outcome says about a configuration. -/
def SR.ok (R : Tape) : SR → Config → Prop
  | .turn n cs q, c => steps n c = some ⟨pl cs blank, app (cells q) R, .A⟩
  | .edgeD n m, c => steps n c = some (cfgS .D [] m R)
  | .edgeF n m, c => steps n c = some (cfgS .C [] m R)
  | .halt n, c => ∃ c', steps n c = some c' ∧ step c' = none

theorem SR.ok_add {R : Tape} {r : SR} {c c' : Config} {k : Nat} (h : steps k c = some c') (h' : r.ok R c') :
    (r.add k).ok R c := by
  cases r with
  | turn n cs q => exact steps_congr trans (by omega) (steps_seq trans h h')
  | edgeD n m => exact steps_congr trans (by omega) (steps_seq trans h h')
  | edgeF n m => exact steps_congr trans (by omega) (steps_seq trans h h')
  | halt n =>
    obtain ⟨c'', h1, h2⟩ := h'
    exact ⟨c'', steps_congr trans (by omega) (steps_seq trans h h1), h2⟩

/-- C skips a pair. -/
theorem cx (bs m : List Bool) (R : Tape) :
    steps 2 (cfgS .C (true :: bs) m R) = some (cfgS .C bs (true :: m) R) := by
  cases bs <;> rfl

/-- C passes a pair `01`: D next. -/
theorem cz (bs m : List Bool) (R : Tape) :
    steps 2 (cfgS .C (false :: bs) m R) = some (cfgS .D bs (false :: m) R) := by
  cases bs <;> rfl

/-- D after a pair `01`, the next pair `11`: it becomes `01`, C next. -/
theorem dx (bs m : List Bool) (R : Tape) :
    steps 2 (cfgS .D (true :: bs) m R) = some (cfgS .C bs (false :: m) R) := by
  cases bs <;> rfl

/-- D after a pair `01`, the next pair `01`: it becomes `11`, and A starts the right pass at the pair before. -/
theorem dz (c : Bool) (cs m : List Bool) (R : Tape) :
    steps 3 (cfgS .D (false :: c :: cs) m R) = some ⟨pl cs blank, app (cells (c :: true :: m)) R, .A⟩ := by
  cases c <;> rfl

/-- The same at the first pair: F reads the blank cell left of the word. -/
theorem dhalt (m : List Bool) (R : Tape) :
    steps 2 (cfgS .D [false] m R) = some ⟨blank, cons false (app (cells (true :: m)) R), .F⟩ := rfl

theorem scan_sound (R : Tape) : ∀ (f : Bool) (l m : List Bool), (scan f l m).ok R (cfgS (stOf f) l m R)
  | true, [], _ => rfl
  | false, [], _ => rfl
  | true, true :: bs, m => SR.ok_add (cx bs m R) (scan_sound R true bs (true :: m))
  | true, false :: bs, m => SR.ok_add (cz bs m R) (scan_sound R false bs (false :: m))
  | false, true :: bs, m => SR.ok_add (dx bs m R) (scan_sound R true bs (false :: m))
  | false, false :: c :: cs, m => dz c cs m R
  | false, [false], m => ⟨_, dhalt m R, rfl⟩

/-! ## The right pass -/

/-- The right pass from A on the first of the pairs `q`: the pairs on the left at the end, and the step count. -/
def apass : List Bool → List Bool → List Bool × Nat
  | cs, [] => (cs, 3)
  | cs, a :: q => let r := apass ((!a) :: cs) q; (r.1, r.2 + 2)

theorem a_pair (a : Bool) (cs q : List Bool) :
    steps 2 (AS cs (cells (a :: q))) = some (AS ((!a) :: cs) (cells q)) := by
  cases a <;> rfl

theorem a_end (cs : List Bool) : steps 3 (AS cs []) = some (RT cs) := by
  have h : steps 3 (AS cs []) = some ⟨cons true (pl cs blank), cons true (cons false blank), .D⟩ := rfl
  rw [h, cons_false_blank]; rfl

theorem apass_sound : ∀ (cs q : List Bool), steps (apass cs q).2 (AS cs (cells q)) = some (RT (apass cs q).1)
  | cs, [] => a_end cs
  | cs, a :: q => steps_congr trans (by simp only [apass]; omega)
      (steps_seq trans (a_pair a cs q) (apass_sound ((!a) :: cs) q))

/-! ## Back to a turn configuration, on lists -/

/-- The pairs of the cells left of the head pair's first cell (nearest first), if they are pairs `b 1`. -/
def decode : List Bool → Option (List Bool)
  | [] => some []
  | [true] => some [false]
  | true :: b :: l => (decode l).map (b :: ·)
  | false :: l => if l.all (fun x => !x) then some [] else none

theorem app_allfalse : ∀ (l : List Bool), l.all (fun x => !x) = true → app l blank = blank
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨rfl, h⟩ := h
    show cons false (app l blank) = blank
    rw [app_allfalse l h, cons_false_blank]

theorem decode_sound : ∀ (l out : List Bool), decode l = some out → app l blank = pl out blank
  | [], out, h => by simp only [decode, Option.some.injEq] at h; subst h; rfl
  | [true], out, h => by
    simp only [decode, Option.some.injEq] at h; subst h
    show cons true blank = cons true (cons false blank)
    rw [cons_false_blank]
  | true :: b :: l, out, h => by
    simp only [decode] at h
    cases e : decode l with
    | none => rw [e] at h; cases h
    | some o =>
      rw [e] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      show cons true (cons b (app l blank)) = cons true (cons b (pl o blank))
      rw [decode_sound l o e]
  | false :: l, out, h => by
    simp only [decode] at h
    split at h
    · rename_i hl
      simp only [Option.some.injEq] at h; subst h
      exact app_allfalse (false :: l) (by simp only [List.all_cons, Bool.not_false, Bool.true_and]; exact hl)
    · cases h

/-- A list configuration that is a turn configuration, read back. -/
def asRT (c : FCfg St) : Option (List Bool) :=
  match c.l, c.r, c.st with
  | true :: l, true :: r, .D => if r.all (fun x => !x) then decode l else none
  | _, _, _ => none

theorem asRT_sound (c : FCfg St) (out : List Bool) (h : asRT c = some out) : c.toCfg = RT out := by
  obtain ⟨cl, cr, cs⟩ := c
  unfold asRT at h
  split at h
  · rename_i l r h1 h2 h3
    simp only at h1 h2 h3
    subst h1 h2 h3
    split at h
    · rename_i hr
      show (⟨cons true (app l blank), cons true (app r blank), .D⟩ : Config) = RT out
      rw [decode_sound l out h, app_allfalse r hr]; rfl
    · cases h
  · cases h

/-! ## The macro machine -/

/-- A state of the macro machine. -/
inductive MS where
  | rt (out : List Bool)
  | raw (c : FCfg St)

def MS.cfg : MS → Config
  | .rt o => RT o
  | .raw c => c.toCfg

/-- Outcomes of a macro step. -/
inductive MR where
  | go (n : Nat) (s : MS)
  | halt (n : Nat)

def MR.ok : MR → Config → Prop
  | .go n s, c => steps n c = some s.cfg
  | .halt n, c => ∃ c', steps n c = some c' ∧ step c' = none

/-- At most `k` more steps on lists (`i` done so far), stopping at the first turn configuration. -/
def rawRun : Nat → Nat → FCfg St → MR
  | 0, i, c => .go i (.raw c)
  | k + 1, i, c =>
    match fstep c with
    | none => .halt i
    | some c' =>
      match asRT c' with
      | some o => .go (i + 1) (.rt o)
      | none => rawRun k (i + 1) c'

theorem rawRun_sound (c0 : Config) : ∀ (k i : Nat) (c : FCfg St), steps i c0 = some c.toCfg →
    (rawRun k i c).ok c0
  | 0, i, c, h => h
  | k + 1, i, c, h => by
    cases e : fstep c with
    | none =>
      simp only [rawRun, e]
      exact ⟨c.toCfg, h, by
        show TM.step trans c.toCfg = none
        rw [FCfg.step_eq, show TM.fstep trans c = none from e]; rfl⟩
    | some c' =>
      have h1 : steps (i + 1) c0 = some c'.toCfg :=
        steps_seq trans h (by
          show TM.steps trans 1 c.toCfg = some c'.toCfg
          simp only [TM.steps, FCfg.step_eq, e, Option.map_some])
      cases e2 : asRT c' with
      | some o =>
        simp only [rawRun, e, e2]
        show steps (i + 1) c0 = some (RT o)
        rw [← asRT_sound c' o e2]; exact h1
      | none =>
        simp only [rawRun, e, e2]
        exact rawRun_sound c0 k (i + 1) c' h1

/-- The cell-by-cell part runs at most this many steps per macro step. -/
def RAWK : Nat := 1000000

def mstep : MS → MR
  | .rt out =>
    match scan true out [false] with
    | .turn n cs q => .go (n + 2 + (apass cs q).2) (.rt (apass cs q).1)
    | .edgeD n m => .go (n + 3 + (apass [] m).2) (.rt (apass [] m).1)
    | .edgeF n m => .go (n + 4) (.raw ⟨[false], false :: cells m, .A⟩)
    | .halt n => .halt (n + 2)
  | .raw c => rawRun RAWK 0 c

theorem first_steps (out : List Bool) : steps 2 (RT out) = some (cfgS .C out [false] blank) := by
  cases out <;> rfl

theorem edgeD_run (m : List Bool) : steps 1 (cfgS .D [] m blank) = some (AS [] (cells m)) := by
  have h : steps 1 (cfgS .D [] m blank) = some ⟨cons false blank, app (cells m) blank, .A⟩ := rfl
  rw [h, cons_false_blank]; rfl

theorem edgeF_run (m : List Bool) :
    steps 2 (cfgS .C [] m blank) = some (FCfg.toCfg ⟨[false], false :: cells m, .A⟩) := rfl

theorem mstep_sound (s : MS) : (mstep s).ok s.cfg := by
  cases s with
  | raw c => exact rawRun_sound c.toCfg RAWK 0 c rfl
  | rt out =>
    have h1 := first_steps out
    have hs := scan_sound blank true out [false]
    simp only [mstep, MS.cfg]
    cases e : scan true out [false] with
    | turn n cs q =>
      rw [e] at hs
      have hs' : steps n (cfgS .C out [false] blank) = some (AS cs (cells q)) := hs
      exact steps_congr trans (by omega)
        (steps_seq trans (steps_seq trans h1 hs') (apass_sound cs q))
    | edgeD n m =>
      rw [e] at hs
      exact steps_congr trans (by omega)
        (steps_seq trans (steps_seq trans (steps_seq trans h1 hs) (edgeD_run m)) (apass_sound [] m))
    | edgeF n m =>
      rw [e] at hs
      exact steps_congr trans (by omega) (steps_seq trans (steps_seq trans h1 hs) (edgeF_run m))
    | halt n =>
      rw [e] at hs
      obtain ⟨c', h2, h3⟩ := hs
      exact ⟨c', steps_congr trans (by omega) (steps_seq trans h1 h2), h3⟩

theorem rawRun_le : ∀ (k i : Nat) (c : FCfg St) (n : Nat) (s : MS), rawRun k i c = .go n s → i ≤ n
  | 0, i, c, n, s, h => by simp only [rawRun, MR.go.injEq] at h; omega
  | k + 1, i, c, n, s, h => by
    unfold rawRun at h
    split at h
    · cases h
    · split at h
      · simp only [MR.go.injEq] at h; omega
      · have := rawRun_le k (i + 1) _ n s h; omega

theorem mstep_pos {s s' : MS} {n : Nat} (h : mstep s = .go n s') : 1 ≤ n := by
  cases s with
  | rt out =>
    simp only [mstep] at h
    split at h
    · rcases h with ⟨rfl, -⟩; omega
    · rcases h with ⟨rfl, -⟩; omega
    · rcases h with ⟨rfl, -⟩; omega
    · cases h
  | raw c =>
    have h' : rawRun (999999 + 1) 0 c = .go n s' := h
    unfold rawRun at h'
    split at h'
    · cases h'
    · split at h'
      · rcases h' with ⟨rfl, -⟩; omega
      · have := rawRun_le 999999 1 _ n s' h'; omega

/-- Blank tape reaches the first turn configuration (the word `x`) after 3 steps. -/
theorem init_RT : steps 3 init = some (RT []) := a_end []

end H25821
