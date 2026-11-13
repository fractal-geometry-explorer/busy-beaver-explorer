import Rules
import TM.ListFrame

/-!
# The token model of 1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA

At the times the head is in state A on the first cell of a pair `00`, the tape is read in pairs: left of the head
`11` = `o` (one), `00` = `z` (zero), `0101` = `x` (a mark); right of the head's `00`, `11` = `true`, `10` = `false`.
A token frame `TF` is the two words (the left one nearest cell first).  `next` is the rewriting system of the
README ("The token model"): rules R1 to R5.  `next f = some (f', n)` comes with the number `n` of machine steps, and `next_sound` proves that the machine runs from
the configuration of `f` to that of `f'` in exactly `n ≥ 1` steps; for every frame, every length of the words.  The rules
themselves are the theorems of `Rules.lean`.

`next` is not defined when the right word is used up (a block of ones at the right end of the tape): there the
machine rewrites the whole tape (a "reset", not modelled here), and on a few shapes of the left word that the run
has not shown (two marks in a row, a mark chain that does not start at a 0).

Hand-written.
-/

namespace H158007

open TM

inductive Tok where
  | z | o | x
  deriving DecidableEq, Repr

/-- `w` written `n` times in front of `r`. -/
def rpt {α : Type} : Nat → List α → List α → List α
  | 0, _, r => r
  | n + 1, w, r => w ++ rpt n w r

/-- The left word as a tape (nearest cell first). -/
def ltape : List Tok → Tape
  | [] => blank
  | .z :: l => cons false (cons false (ltape l))
  | .o :: l => cons true (cons true (ltape l))
  | .x :: l => cons true (cons false (cons true (cons false (ltape l))))

/-- The right word as a tape. -/
def rtape : List Bool → Tape
  | [] => blank
  | true :: r => cons true (cons true (rtape r))
  | false :: r => cons true (cons false (rtape r))

structure TF where
  L : List Tok
  R : List Bool
  deriving DecidableEq, Repr

def TF.cfg (f : TF) : Config := ⟨ltape f.L, cons false (cons false (rtape f.R)), .A⟩

/-- `g.1` is reached from `f` in exactly `g.2` steps, at least one. -/
def Reach (f : TF) (g : TF × Nat) : Prop := 0 < g.2 ∧ steps g.2 f.cfg = some g.1.cfg

/-! ## Words and tapes -/

theorem rtape_ones (k : Nat) (r : List Bool) : rtape (rpt k [true] r) = rep k [true, true] (rtape r) := by
  induction k with
  | zero => rfl
  | succ k ih => show cons true (cons true (rtape (rpt k [true] r))) = _; rw [ih]; rfl

theorem rtape_001 (j : Nat) (r : List Bool) :
    rtape (rpt j [false, false, true] r) = rep j [true, false, true, false, true, true] (rtape r) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show cons true (cons false (cons true (cons false (cons true (cons true (rtape (rpt j [false, false, true] r))))))) = _
    rw [ih]; rfl

theorem rtape_010 (j : Nat) (r : List Bool) :
    rtape (rpt j [false, true, false] r) = rep j [true, false, true, true, true, false] (rtape r) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show cons true (cons false (cons true (cons true (cons true (cons false (rtape (rpt j [false, true, false] r))))))) = _
    rw [ih]; rfl

theorem ltape_zs (d : Nat) (l : List Tok) : ltape (rpt d [.z] l) = rep d [false, false] (ltape l) := by
  induction d with
  | zero => rfl
  | succ d ih => show cons false (cons false (ltape (rpt d [.z] l))) = _; rw [ih]; rfl

theorem zrot (d : Nat) (T : Tape) :
    cons false (rep d [false, false] (cons false T)) = rep d [false, false] (cons false (cons false T)) :=
  rep_rotate d [false] [false, false] [false, false] rfl (cons false T)

theorem blank2 : cons false (cons false blank) = blank := by rw [cons_false_blank, cons_false_blank]

/-- The ones at the front of the right word. -/
def ones : List Bool → Nat × List Bool
  | true :: r => ((ones r).1 + 1, (ones r).2)
  | r => (0, r)

theorem ones_spec : ∀ r : List Bool, r = rpt (ones r).1 [true] (ones r).2
  | [] => rfl
  | false :: _ => rfl
  | true :: r => by
    show true :: r = true :: rpt (ones r).1 [true] (ones r).2
    rw [← ones_spec r]

/-- The ones at the top of the left word. -/
def lones : List Tok → Nat × List Tok
  | .o :: l => ((lones l).1 + 1, (lones l).2)
  | l => (0, l)

theorem lones_spec : ∀ l : List Tok, ltape l = rep (lones l).1 [true, true] (ltape (lones l).2)
  | [] => rfl
  | .z :: _ => rfl
  | .x :: _ => rfl
  | .o :: l => by
    show cons true (cons true (ltape l)) = cons true (cons true (rep (lones l).1 [true, true] (ltape (lones l).2)))
    rw [← lones_spec l]

/-- The pairs `1 X` at the top of the left word. -/
def chain : List Tok → Nat × List Tok
  | .x :: .o :: l => ((chain l).1 + 1, (chain l).2)
  | l => (0, l)

theorem chain_spec : ∀ l : List Tok,
    ltape l = rep (chain l).1 [true, false, true, false, true, true] (ltape (chain l).2)
  | .x :: .o :: l => by
    show cons true (cons false (cons true (cons false (cons true (cons true (ltape l)))))) =
      cons true (cons false (cons true (cons false (cons true (cons true
        (rep (chain l).1 [true, false, true, false, true, true] (ltape (chain l).2)))))))
    rw [← chain_spec l]
  | [] => rfl
  | .z :: _ => rfl
  | .o :: _ => rfl
  | [.x] => rfl
  | .x :: .z :: _ => rfl
  | .x :: .x :: _ => rfl

/-! ## The rules on frames -/

/-- R4: the right word starts with 0, the left word is `... 0 X (1 X)^j 1^k`. -/
def rZb (k : Nat) : Nat × List Tok → List Bool → Option (TF × Nat)
  | (j, [.x]), r => some (⟨[], false :: false :: true :: rpt j [false, false, true] (rpt k [true] (true :: r))⟩, 8 * j + 4 * k + 14)
  | (j, .x :: .z :: l), r =>
    some (⟨l, false :: false :: true :: rpt j [false, false, true] (rpt k [true] (true :: r))⟩, 8 * j + 4 * k + 14)
  | _, _ => none

/-- R1 and R4: the right word starts with 0 (its tail is `r`); `p` is `lones` of the left word. -/
def rZa : Nat × List Tok → List Bool → Option (TF × Nat)
  | (k, []), r => some (⟨[], true :: rpt k [true] (true :: r)⟩, 4 * k + 10)
  | (k, .z :: l), r => some (⟨l, true :: rpt k [true] (true :: r)⟩, 4 * k + 10)
  | (k, .x :: l), r => rZb k (chain (.x :: l)) r
  | _, _ => none

/-- R5: the right word is `1 0 1 r`; `p` is `chain` of the left word. -/
def rDb : Nat × List Tok → List Bool → Option (TF × Nat)
  | (j, [.x]), r => some (⟨[], false :: false :: true :: false :: rpt j [false, true, false] (false :: false :: r)⟩, 8 * j + 22)
  | (j, .x :: .z :: l), r =>
    some (⟨l, false :: false :: true :: false :: rpt j [false, true, false] (false :: false :: r)⟩, 8 * j + 22)
  | _, _ => none

/-- R5a and R5: the right word is `1 0 1 r`. -/
def rD : List Tok → List Bool → Option (TF × Nat)
  | [], r => some (⟨[], true :: false :: false :: false :: r⟩, 18)
  | .z :: l, r => some (⟨l, true :: false :: false :: false :: r⟩, 18)
  | .x :: l, r => rDb (chain (.x :: l)) r
  | _, _ => none

/-- R2, R3, R5: the right word starts with a block of ones; `p` is `ones` of the right word. -/
def rO (L : List Tok) : Nat × List Bool → Option (TF × Nat)
  | (1, false :: false :: r) => some (⟨.x :: .o :: L, r⟩, 8)
  | (d + 2, false :: false :: r) => some (⟨.x :: rpt d [.z] (.z :: .o :: L), r⟩, 10 * d + 18)
  | (1, false :: true :: r) => rD L r
  | (2, false :: true :: r) => some (⟨.o :: L, false :: false :: false :: r⟩, 24)
  | (d + 3, false :: true :: r) => some (⟨rpt d [.z] (.z :: .o :: L), false :: false :: false :: r⟩, 10 * d + 34)
  | _ => none

/-- One step of the token model. -/
def next (f : TF) : Option (TF × Nat) :=
  match f.R with
  | false :: r => rZa (lones f.L) r
  | _ => rO f.L (ones f.R)

/-! ## Soundness -/

theorem rZb_sound (k : Nat) (p : Nat × List Tok) (r : List Bool) (f' : TF × Nat) (h : rZb k p r = some f')
    (L : List Tok) (hL : ltape L = rep k [true, true] (rep p.1 [true, false, true, false, true, true] (ltape p.2))) :
    Reach ⟨L, false :: r⟩ f' := by
  unfold rZb at h
  split at h
  · rename_i j
    simp only [Option.some.injEq] at h; subst h
    have := unwind j k blank (rtape r)
    rw [blank2] at this
    simp only [Reach, TF.cfg, hL, ltape, rtape, rtape_ones, rtape_001]
    exact ⟨by omega, this⟩
  · rename_i j l
    simp only [Option.some.injEq] at h; subst h
    have := unwind j k (ltape l) (rtape r)
    simp only [Reach, TF.cfg, hL, ltape, rtape, rtape_ones, rtape_001]
    exact ⟨by omega, this⟩
  · simp at h

theorem rZa_sound (p : Nat × List Tok) (r : List Bool) (f' : TF × Nat) (h : rZa p r = some f')
    (L : List Tok) (hL : ltape L = rep p.1 [true, true] (ltape p.2)) : Reach ⟨L, false :: r⟩ f' := by
  unfold rZa at h
  split at h
  · rename_i k
    simp only [Option.some.injEq] at h; subst h
    have := carry k blank (rtape r)
    rw [blank2] at this
    simp only [Reach, TF.cfg, hL, ltape, rtape, rtape_ones]
    exact ⟨by omega, this⟩
  · rename_i k l
    simp only [Option.some.injEq] at h; subst h
    have := carry k (ltape l) (rtape r)
    simp only [Reach, TF.cfg, hL, ltape, rtape, rtape_ones]
    exact ⟨by omega, this⟩
  · rename_i k l
    exact rZb_sound k _ r f' h L (by rw [hL, ← chain_spec])
  · simp at h

theorem rDb_sound (p : Nat × List Tok) (r : List Bool) (f' : TF × Nat) (h : rDb p r = some f')
    (L : List Tok) (hL : ltape L = rep p.1 [true, false, true, false, true, true] (ltape p.2)) :
    Reach ⟨L, true :: false :: true :: r⟩ f' := by
  unfold rDb at h
  split at h
  · rename_i j
    simp only [Option.some.injEq] at h; subst h
    have := dropx j blank (rtape r)
    rw [blank2] at this
    simp only [Reach, TF.cfg, hL, ltape, rtape, rtape_010]
    exact ⟨by omega, this⟩
  · rename_i j l
    simp only [Option.some.injEq] at h; subst h
    have := dropx j (ltape l) (rtape r)
    simp only [Reach, TF.cfg, hL, ltape, rtape, rtape_010]
    exact ⟨by omega, this⟩
  · simp at h

theorem rD_sound (L : List Tok) (r : List Bool) (f' : TF × Nat) (h : rD L r = some f') :
    Reach ⟨L, true :: false :: true :: r⟩ f' := by
  unfold rD at h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    have := drop blank (rtape r)
    rw [blank2] at this
    simp only [Reach, TF.cfg, ltape, rtape]
    exact ⟨by omega, this⟩
  · rename_i l
    simp only [Option.some.injEq] at h; subst h
    have := drop (ltape l) (rtape r)
    simp only [Reach, TF.cfg, ltape, rtape]
    exact ⟨by omega, this⟩
  · exact rDb_sound _ r f' h _ (chain_spec _)
  · simp at h

theorem rO_sound (L : List Tok) (p : Nat × List Bool) (f' : TF × Nat) (h : rO L p = some f') :
    Reach ⟨L, rpt p.1 [true] p.2⟩ f' := by
  unfold rO at h
  split at h
  · rename_i r
    simp only [Option.some.injEq] at h; subst h
    have := push1 (ltape L) (rtape r)
    simp only [Reach, TF.cfg, ltape, rtape, rpt, List.cons_append, List.nil_append]
    exact ⟨by omega, this⟩
  · rename_i d r
    simp only [Option.some.injEq] at h; subst h
    have := push d (ltape L) (rtape r)
    rw [zrot] at this
    simp only [Reach, TF.cfg, ltape, rtape, rtape_ones, ltape_zs]
    exact ⟨by omega, this⟩
  · exact rD_sound L _ f' h
  · rename_i r
    simp only [Option.some.injEq] at h; subst h
    have := load2 (ltape L) (rtape r)
    simp only [Reach, TF.cfg, ltape, rtape, rpt, List.cons_append, List.nil_append]
    exact ⟨by omega, this⟩
  · rename_i d r
    simp only [Option.some.injEq] at h; subst h
    have := load d (ltape L) (rtape r)
    rw [zrot] at this
    simp only [Reach, TF.cfg, ltape, rtape, rtape_ones, ltape_zs]
    exact ⟨by omega, this⟩
  · simp at h

/-- **The token model is sound**: a step of `next` is a run of the machine, for every frame. -/
theorem next_sound (f : TF) (f' : TF × Nat) (h : next f = some f') : Reach f f' := by
  obtain ⟨L, R⟩ := f
  unfold next at h
  split at h
  · rename_i r hr
    simp only at hr; subst hr
    exact rZa_sound _ r f' h L (lones_spec L)
  · have := rO_sound L (ones R) f' h
    rwa [← ones_spec] at this

end H158007
