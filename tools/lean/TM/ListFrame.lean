import TM.Basic
import TM.Fin

/-!
# Frames with list parameters: digit words, counters, and frame maps

Tools for proofs about machines whose tape holds a word of unbounded length, such as the digits of a counter, so
that no finite set of configurations with number parameters (as in a holdout's `Phases.lean`) covers the run.  For
any machine `δ`; kernel only.

## Lists of blocks (`sq`, `sqr`)

`sq f ts X` writes the blocks `f t`, for `t` in the list `ts`, in front of the tape `X`, the first element next to
the head; `sqr f ts X` writes them the other way round (the last element next to the head).  A block `f t : Tape →
Tape` is any tape pattern with a parameter `t` of any type (a digit, a pair of numbers, ...), written as on the side
of the head it is on (left streams nearest cell first).  `sq_append`, `sqr_cons`, `sqr_eq`, `sq_eq`, `sq_map`
rewrite them.  `bbtools/seqtm.py` and `bbtools/listframe.py` write these terms.

## Crossing a list (`seqL`, `seqR`, `seqL'`, `seqR'`)

If the head crosses one block `f t` in state `q` and comes out on the far side in state `q`, the block having become
`g t` (a fixed pattern `U` may travel along next to the head), then it crosses every list of such blocks; the list
comes out reversed (`sq` becomes `sqr`).  `seqL`/`seqR` cross to the left/right; the primed forms cross a list
written with `sqr`.  These are the sequence rules of `bbtools/seqtm.py`, which generates the one-block hypotheses.

## Runs of one digit (`pw`, `carryL`, `carryR`)

`pw f k X` is `f` applied `k` times (`k` copies of one block); `carryL`/`carryR` cross such a run, by induction on
`k`: a carry over a run of maximal digits, or a return sweep over a run of zeros.

## Counters (`incW`, `counter_incL`, `counter_incR`)

A digit word is a `List Nat`, least significant digit first (next to the head), each digit `d ≤ m` written as the
block `D d`; the far end of the word is a fixed tape `E`.  `incW m ext ds` adds one: maximal digits `m` become `0`
and carry, the first digit below `m` goes up by one, and a carry out of the whole word replaces the (empty) rest by
the digits `ext` (an overflow; `ext = [1]` for a plain counter).  `counter_incL` proves for every digit word that the
machine performs this increment, from four one-digit facts:

* `carry`: in state `q`, a maximal digit `D m` on the left is crossed to the left, leaving a block `Z` on the right;
* `bump`: in state `q`, a digit `D d` with `d < m` becomes `D (d + 1)` and the head turns, now in state `r`;
* `ret`: in state `r`, a block `Z` on the right is crossed to the right and becomes the digit `D 0` on the left;
* `ovf`: in state `q`, at the end `E` of the word, the digits `ext` are written and the head returns in state `r`.

All four are stated for all surrounding tapes, so they are what `bbtools.symtm.prove` (or `seqtm.prove`) proves
for one digit.  `counter_incR` is the mirror image (digits on the right of the head).  The statement carries the
rest of the tape `R` (`L`) along, so it composes with other pieces.

## Frame maps (`iterF`, `frames_halts_iff`, `checkF`, `checkF_sound`)

A frame type `α` (any type: tuples of numbers, digit words, ...) with `cfg : α → Cfg Q` and a map
`next : α → Option α`.  `iterF next k p` is `k` steps of the map.  From

* `sound`: on good frames, `next p = some p'` is a run of at least one step from `cfg p` to `cfg p'`,
* `good`: `next` keeps frames good,
* `stop_halts`: a good frame with `Stop p` halts,
* `none_stop`: on a good frame, `next p = none` only if `Stop p`,
* a run from the start configuration `c0` to `cfg p0`, `p0` good,

`frames_halts_iff` gives: the machine halts from `c0` if and only if some iterate of `next` from `p0` satisfies
`Stop`.  `checkF next k p = true` (by `decide` or `native_decide`) shows that the first `k` iterates exist
(`checkF_sound`), hence no frame among them is a `Stop` frame on which `next` fails.  `frames_no_halt` is the
non-halting half on its own: if every iterate exists, the machine never halts.  A machine's `Phases.lean` defines
`α`, `cfg` and `next`, proves `sound` case by case from generated pieces, and then gets `halts_iff` from here.

## Run-length frames (`runs`, `normB`, `RLFrame`, `RLCase`, `rlNext`, `blank_frame`, `rl_no_halt`)

The frame type that needs no hand-made shapes: both sides of the head as lists of runs `(bit, length)`
(`runs rs X`), in normal form (`normB`).  A case table `cs : List (RLCase δ)` (each case a partial map on frames
with its own soundness proof) gives the frame map `rlNext cs` (first matching case on the normal form) and
`rlNext_sound`.  `rl_eq` is the tactic that glues a symbolic run's end to a run list.  `frameAt` / `blank_frame`
reach the first frame from blank tape by evaluation; `checkF` + `rl_reach` give bounded runs; `rl_no_halt` says the
machine never halts if the table is defined forever along the orbit.  `bbtools/listframe.py` fits such a table
from the machine (one `symtm` run per case) and writes `Pieces.lean`, `Cases.lean`, `Frames.lean`.
-/

namespace TM

/-! ## Lists of blocks -/

/-- A stream is its first cell in front of the rest (used when a step left re-reads the head cell). -/
theorem cons_head_tail (s : Tape) : cons (s 0) (tail s) = s := funext fun n => by cases n <;> rfl

/-- The blocks `f t` for `t` in `ts`, in front of `X`, the first next to the head. -/
def sq {α : Type} (f : α → Tape → Tape) : List α → Tape → Tape
  | [], X => X
  | t :: ts, X => f t (sq f ts X)

/-- The blocks `f t` for `t` in `ts`, in front of `X`, the last next to the head. -/
def sqr {α : Type} (f : α → Tape → Tape) (ts : List α) (X : Tape) : Tape :=
  ts.foldl (fun acc t => f t acc) X

@[simp] theorem sq_nil {α : Type} (f : α → Tape → Tape) (X : Tape) : sq f [] X = X := rfl
@[simp] theorem sq_cons {α : Type} (f : α → Tape → Tape) (t : α) (ts : List α) (X : Tape) :
    sq f (t :: ts) X = f t (sq f ts X) := rfl
@[simp] theorem sqr_nil {α : Type} (f : α → Tape → Tape) (X : Tape) : sqr f [] X = X := rfl

theorem sqr_cons {α : Type} (f : α → Tape → Tape) (t : α) (ts : List α) (X : Tape) :
    sqr f (t :: ts) X = sqr f ts (f t X) := rfl

theorem sq_append {α : Type} (f : α → Tape → Tape) (l l' : List α) (X : Tape) :
    sq f (l ++ l') X = sq f l (sq f l' X) := by
  induction l with
  | nil => rfl
  | cons s l ih => simp only [List.cons_append, sq, ih]

theorem sqr_eq {α : Type} (f : α → Tape → Tape) (ts : List α) (X : Tape) : sqr f ts X = sq f ts.reverse X := by
  induction ts generalizing X with
  | nil => rfl
  | cons t ts ih => rw [sqr_cons, ih, List.reverse_cons, sq_append]; rfl

theorem sq_eq {α : Type} (f : α → Tape → Tape) (ts : List α) (X : Tape) : sq f ts X = sqr f ts.reverse X := by
  rw [sqr_eq, List.reverse_reverse]

theorem sq_map {α β : Type} (f : β → Tape → Tape) (h : α → β) (ts : List α) (X : Tape) :
    sq f (ts.map h) X = sq (fun t => f (h t)) ts X := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, sq, ih]

/-- `k` copies of one block. -/
def pw (f : Tape → Tape) : Nat → Tape → Tape
  | 0, X => X
  | k + 1, X => f (pw f k X)

theorem pw_eq_sq (f : Tape → Tape) (k : Nat) (X : Tape) :
    pw f k X = sq (fun (_ : Unit) => f) (List.replicate k ()) X := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pw, List.replicate_succ, sq, ih]

theorem pw_succ' (f : Tape → Tape) (k : Nat) (X : Tape) : pw f (k + 1) X = pw f k (f X) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pw] at ih ⊢; rw [ih]

theorem pw_add (f : Tape → Tape) (a b : Nat) (X : Tape) : pw f (a + b) X = pw f a (pw f b X) := by
  induction a with
  | zero => simp [pw]
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by omega]; simp only [pw, ih]

section
variable {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q))

/-! ## Crossing a list -/

/-- Crossing the blocks `ts` to the left. -/
theorem seqL {α : Type} (f g : α → Tape → Tape) (U : Tape → Tape) (q : Q)
    (h : ∀ t L R, ∃ n, steps δ n ⟨f t L, U R, q⟩ = some ⟨L, U (g t R), q⟩) :
    ∀ (ts : List α) (L R : Tape), ∃ n, steps δ n ⟨sq f ts L, U R, q⟩ = some ⟨L, U (sqr g ts R), q⟩ := by
  intro ts
  induction ts with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons t ts ih =>
    intro L R
    obtain ⟨n1, h1⟩ := h t (sq f ts L) R
    obtain ⟨n2, h2⟩ := ih L (g t R)
    exact ⟨_, steps_seq δ h1 h2⟩

/-- Crossing the blocks `ts`, written last-first, to the left. -/
theorem seqL' {α : Type} (f g : α → Tape → Tape) (U : Tape → Tape) (q : Q)
    (h : ∀ t L R, ∃ n, steps δ n ⟨f t L, U R, q⟩ = some ⟨L, U (g t R), q⟩) :
    ∀ (ts : List α) (L R : Tape), ∃ n, steps δ n ⟨sqr f ts L, U R, q⟩ = some ⟨L, U (sq g ts R), q⟩ := by
  intro ts L R
  have h' := seqL δ f g U q h ts.reverse L R
  rw [sqr_eq g, List.reverse_reverse] at h'
  rw [sqr_eq f]; exact h'

/-- Crossing the blocks `ts` to the right. -/
theorem seqR {α : Type} (f g : α → Tape → Tape) (U : Tape → Tape) (q : Q)
    (h : ∀ t L R, ∃ n, steps δ n ⟨U L, f t R, q⟩ = some ⟨U (g t L), R, q⟩) :
    ∀ (ts : List α) (L R : Tape), ∃ n, steps δ n ⟨U L, sq f ts R, q⟩ = some ⟨U (sqr g ts L), R, q⟩ := by
  intro ts
  induction ts with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons t ts ih =>
    intro L R
    obtain ⟨n1, h1⟩ := h t L (sq f ts R)
    obtain ⟨n2, h2⟩ := ih (g t L) R
    exact ⟨_, steps_seq δ h1 h2⟩

/-- Crossing the blocks `ts`, written last-first, to the right. -/
theorem seqR' {α : Type} (f g : α → Tape → Tape) (U : Tape → Tape) (q : Q)
    (h : ∀ t L R, ∃ n, steps δ n ⟨U L, f t R, q⟩ = some ⟨U (g t L), R, q⟩) :
    ∀ (ts : List α) (L R : Tape), ∃ n, steps δ n ⟨U L, sqr f ts R, q⟩ = some ⟨U (sq g ts L), R, q⟩ := by
  intro ts L R
  have h' := seqR δ f g U q h ts.reverse L R
  rw [sqr_eq g, List.reverse_reverse] at h'
  rw [sqr_eq f]; exact h'

/-! ## Runs of one digit -/

/-- Crossing `k` copies of the block `f` to the left; they become `k` copies of `g` on the right. -/
theorem carryL (f g : Tape → Tape) (U : Tape → Tape) (q : Q)
    (h : ∀ L R, ∃ n, steps δ n ⟨f L, U R, q⟩ = some ⟨L, U (g R), q⟩) :
    ∀ (k : Nat) (L R : Tape), ∃ n, steps δ n ⟨pw f k L, U R, q⟩ = some ⟨L, U (pw g k R), q⟩ := by
  intro k
  induction k with
  | zero => intro L R; exact ⟨0, rfl⟩
  | succ k ih =>
    intro L R
    obtain ⟨n1, h1⟩ := h (pw f k L) R
    obtain ⟨n2, h2⟩ := ih L (g R)
    rw [← pw_succ'] at h2
    exact ⟨_, steps_seq δ h1 h2⟩

/-- Crossing `k` copies of the block `f` to the right; they become `k` copies of `g` on the left. -/
theorem carryR (f g : Tape → Tape) (U : Tape → Tape) (q : Q)
    (h : ∀ L R, ∃ n, steps δ n ⟨U L, f R, q⟩ = some ⟨U (g L), R, q⟩) :
    ∀ (k : Nat) (L R : Tape), ∃ n, steps δ n ⟨U L, pw f k R, q⟩ = some ⟨U (pw g k L), R, q⟩ := by
  intro k
  induction k with
  | zero => intro L R; exact ⟨0, rfl⟩
  | succ k ih =>
    intro L R
    obtain ⟨n1, h1⟩ := h L (pw f k R)
    obtain ⟨n2, h2⟩ := ih (g L) R
    rw [← pw_succ'] at h2
    exact ⟨_, steps_seq δ h1 h2⟩

end

/-! ## Counters -/

/-- Add one to the digit word `ds` (least significant digit first, digits `0..m`); a carry out of the whole word
becomes the digits `ext`. -/
def incW (m : Nat) (ext : List Nat) : List Nat → List Nat
  | [] => ext
  | d :: ds => if d < m then (d + 1) :: ds else 0 :: incW m ext ds

/-- `k` increments. -/
def incN (m : Nat) (ext : List Nat) : Nat → List Nat → List Nat
  | 0, ds => ds
  | k + 1, ds => incN m ext k (incW m ext ds)

/-- The value of a digit word in base `b` (least significant digit first). -/
def valW (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + b * valW b ds

/-- All digits are at most `m`. -/
def DigitsLe (m : Nat) (ds : List Nat) : Prop := ∀ d ∈ ds, d ≤ m

theorem incW_le (m : Nat) (ext : List Nat) (he : DigitsLe m ext) :
    ∀ ds, DigitsLe m ds → DigitsLe m (incW m ext ds)
  | [], _ => he
  | d :: ds, h => by
    simp only [incW]
    split
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact h x (List.mem_cons_of_mem _ hx)
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact incW_le m ext he ds (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx

/-- In base `m + 1` the increment adds one, when the overflow digits `ext` are worth one (`valW (m+1) ext = 1`). -/
theorem valW_incW (m : Nat) (ext : List Nat) (he : valW (m + 1) ext = 1) :
    ∀ ds, DigitsLe m ds → valW (m + 1) (incW m ext ds) = valW (m + 1) ds + 1
  | [], _ => by simp [incW, valW, he]
  | d :: ds, h => by
    simp only [incW]
    have hd : d ≤ m := h d (List.mem_cons_self ..)
    split
    · simp only [valW]; omega
    · have hm : d = m := by omega
      subst hm
      simp only [valW]
      rw [valW_incW d ext he ds (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      rw [Nat.mul_add]; omega

section
variable {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q))

/-- **One increment of a counter written left of the head.**  The digits `ds` (least significant next to the head)
are the blocks `D d`, the word ends in the tape `E`; from state `q` with `R` on the right, the machine reaches the
word `incW m ext ds` with the head back where it was, in state `r`. -/
theorem counter_incL (D : Nat → Tape → Tape) (Z : Tape → Tape) (E : Tape) (m : Nat) (ext : List Nat) (q r : Q)
    (carry : ∀ L R, ∃ n, steps δ n ⟨D m L, R, q⟩ = some ⟨L, Z R, q⟩)
    (bump : ∀ d, d < m → ∀ L R, ∃ n, steps δ n ⟨D d L, R, q⟩ = some ⟨D (d + 1) L, R, r⟩)
    (ret : ∀ L R, ∃ n, steps δ n ⟨L, Z R, r⟩ = some ⟨D 0 L, R, r⟩)
    (ovf : ∀ R, ∃ n, steps δ n ⟨E, R, q⟩ = some ⟨sq D ext E, R, r⟩) :
    ∀ (ds : List Nat) (R : Tape), DigitsLe m ds →
      ∃ n, steps δ n ⟨sq D ds E, R, q⟩ = some ⟨sq D (incW m ext ds) E, R, r⟩
  | [], R, _ => ovf R
  | d :: ds, R, h => by
    have hd : d ≤ m := h d (List.mem_cons_self ..)
    simp only [sq, incW]
    split
    · exact bump d (by omega) (sq D ds E) R
    · have hm : d = m := by omega
      subst hm
      obtain ⟨n1, h1⟩ := carry (sq D ds E) R
      obtain ⟨n2, h2⟩ := counter_incL D Z E d ext q r carry bump ret ovf ds (Z R)
        (fun y hy => h y (List.mem_cons_of_mem _ hy))
      obtain ⟨n3, h3⟩ := ret (sq D (incW d ext ds) E) R
      exact ⟨_, steps_seq δ h1 (steps_seq δ h2 h3)⟩

/-- **One increment of a counter written right of the head** (the mirror image of `counter_incL`). -/
theorem counter_incR (D : Nat → Tape → Tape) (Z : Tape → Tape) (E : Tape) (m : Nat) (ext : List Nat) (q r : Q)
    (carry : ∀ L R, ∃ n, steps δ n ⟨L, D m R, q⟩ = some ⟨Z L, R, q⟩)
    (bump : ∀ d, d < m → ∀ L R, ∃ n, steps δ n ⟨L, D d R, q⟩ = some ⟨L, D (d + 1) R, r⟩)
    (ret : ∀ L R, ∃ n, steps δ n ⟨Z L, R, r⟩ = some ⟨L, D 0 R, r⟩)
    (ovf : ∀ L, ∃ n, steps δ n ⟨L, E, q⟩ = some ⟨L, sq D ext E, r⟩) :
    ∀ (ds : List Nat) (L : Tape), DigitsLe m ds →
      ∃ n, steps δ n ⟨L, sq D ds E, q⟩ = some ⟨L, sq D (incW m ext ds) E, r⟩
  | [], L, _ => ovf L
  | d :: ds, L, h => by
    have hd : d ≤ m := h d (List.mem_cons_self ..)
    simp only [sq, incW]
    split
    · exact bump d (by omega) L (sq D ds E)
    · have hm : d = m := by omega
      subst hm
      obtain ⟨n1, h1⟩ := carry L (sq D ds E)
      obtain ⟨n2, h2⟩ := counter_incR D Z E d ext q r carry bump ret ovf ds (Z L)
        (fun y hy => h y (List.mem_cons_of_mem _ hy))
      obtain ⟨n3, h3⟩ := ret L (sq D (incW d ext ds) E)
      exact ⟨_, steps_seq δ h1 (steps_seq δ h2 h3)⟩

/-- `k` increments in a row (when the head ends where the next increment starts, `r = q`). -/
theorem counter_incL_iter (D : Nat → Tape → Tape) (Z : Tape → Tape) (E : Tape) (m : Nat) (ext : List Nat) (q : Q)
    (hext : DigitsLe m ext)
    (carry : ∀ L R, ∃ n, steps δ n ⟨D m L, R, q⟩ = some ⟨L, Z R, q⟩)
    (bump : ∀ d, d < m → ∀ L R, ∃ n, steps δ n ⟨D d L, R, q⟩ = some ⟨D (d + 1) L, R, q⟩)
    (ret : ∀ L R, ∃ n, steps δ n ⟨L, Z R, q⟩ = some ⟨D 0 L, R, q⟩)
    (ovf : ∀ R, ∃ n, steps δ n ⟨E, R, q⟩ = some ⟨sq D ext E, R, q⟩) :
    ∀ (k : Nat) (ds : List Nat) (R : Tape), DigitsLe m ds →
      ∃ n, steps δ n ⟨sq D ds E, R, q⟩ = some ⟨sq D (incN m ext k ds) E, R, q⟩
  | 0, ds, R, _ => ⟨0, rfl⟩
  | k + 1, ds, R, h => by
    obtain ⟨n1, h1⟩ := counter_incL δ D Z E m ext q q carry bump ret ovf ds R h
    obtain ⟨n2, h2⟩ := counter_incL_iter D Z E m ext q hext carry bump ret ovf k (incW m ext ds) R
      (incW_le m ext hext ds h)
    exact ⟨_, steps_seq δ h1 h2⟩

/-! ## Frame maps -/

/-- `k` steps of a frame map. -/
def iterF {α : Type} (next : α → Option α) : Nat → α → Option α
  | 0, p => some p
  | k + 1, p => (next p).bind (iterF next k)

theorem iterF_succ {α : Type} (next : α → Option α) (k : Nat) (p p' : α) (h : iterF next k p = some p') :
    iterF next (k + 1) p = next p' := by
  induction k generalizing p with
  | zero => simp only [iterF, Option.some.injEq] at h; subst h; simp [iterF]
  | succ k ih =>
    simp only [iterF] at h ⊢
    cases hp : next p with
    | none => simp [hp] at h
    | some q => simp only [hp, Option.bind_some] at h ⊢; exact ih q h

theorem iterF_good {α : Type} (next : α → Option α) (Good : α → Prop)
    (good : ∀ p p', Good p → next p = some p' → Good p') :
    ∀ k p p', Good p → iterF next k p = some p' → Good p'
  | 0, p, p', hg, h => by simp only [iterF, Option.some.injEq] at h; subst h; exact hg
  | k + 1, p, p', hg, h => by
    simp only [iterF] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp, Option.bind_some] at h
      exact iterF_good next Good good k q p' (good p q hg hp) h

/-- `k` steps of the frame map are a run of at least `k` steps of the machine. -/
theorem reach_iterF {α : Type} (cfg : α → Cfg Q) (next : α → Option α) (Good : α → Prop)
    (sound : ∀ p p', Good p → next p = some p' → ∃ n, 0 < n ∧ steps δ n (cfg p) = some (cfg p'))
    (good : ∀ p p', Good p → next p = some p' → Good p') :
    ∀ k p p', Good p → iterF next k p = some p' → ∃ n, k ≤ n ∧ steps δ n (cfg p) = some (cfg p')
  | 0, p, p', _, h => by simp only [iterF, Option.some.injEq] at h; subst h; exact ⟨0, Nat.le_refl 0, rfl⟩
  | k + 1, p, p', hg, h => by
    simp only [iterF] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp, Option.bind_some] at h
      obtain ⟨n1, p1, h1⟩ := sound p q hg hp
      obtain ⟨n2, p2, h2⟩ := reach_iterF cfg next Good sound good k q p' (good p q hg hp) h
      exact ⟨n1 + n2, by omega, steps_seq δ h1 h2⟩

/-- If every iterate of the frame map exists, the machine never halts from `c0`. -/
theorem frames_no_halt {α : Type} (cfg : α → Cfg Q) (next : α → Option α) (Good : α → Prop)
    (sound : ∀ p p', Good p → next p = some p' → ∃ n, 0 < n ∧ steps δ n (cfg p) = some (cfg p'))
    (good : ∀ p p', Good p → next p = some p' → Good p')
    {c0 : Cfg Q} {p0 : α} {n0 : Nat} (h0 : steps δ n0 c0 = some (cfg p0)) (g0 : Good p0)
    (hall : ∀ k, ∃ p, iterF next k p0 = some p) : ¬ Halts δ c0 := by
  apply not_halts_of_forall δ
  apply forall_of_unbounded δ (fun m => ∃ c', steps δ m c0 = some c')
  · intro n
    obtain ⟨p, hp⟩ := hall n
    obtain ⟨m, hm, h⟩ := reach_iterF δ cfg next Good sound good n p0 p g0 hp
    exact ⟨n0 + m, by omega, _, steps_seq δ h0 h⟩
  · exact fun _ h => h

/-- **Halting is reaching a stop frame.**  The machine halts from `c0` if and only if some iterate of `next` from
`p0` is a `Stop` frame. -/
theorem frames_halts_iff {α : Type} (cfg : α → Cfg Q) (next : α → Option α) (Good Stop : α → Prop)
    (sound : ∀ p p', Good p → next p = some p' → ∃ n, 0 < n ∧ steps δ n (cfg p) = some (cfg p'))
    (good : ∀ p p', Good p → next p = some p' → Good p')
    (stop_halts : ∀ p, Good p → Stop p → Halts δ (cfg p))
    (none_stop : ∀ p, Good p → next p = none → Stop p)
    {c0 : Cfg Q} {p0 : α} {n0 : Nat} (h0 : steps δ n0 c0 = some (cfg p0)) (g0 : Good p0) :
    Halts δ c0 ↔ ∃ k p, iterF next k p0 = some p ∧ Stop p := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    have hall : ∀ k, ∃ p, iterF next k p0 = some p := by
      intro k
      induction k with
      | zero => exact ⟨_, rfl⟩
      | succ k ih =>
        obtain ⟨p, hp⟩ := ih
        rw [iterF_succ next k _ p hp]
        cases hn : next p with
        | some q => exact ⟨q, rfl⟩
        | none =>
          exact absurd ⟨k, p, hp, none_stop p (iterF_good next Good good k p0 p g0 hp) hn⟩ hno
    exact frames_no_halt δ cfg next Good sound good h0 g0 hall hh
  · rintro ⟨k, p, h, hs⟩
    obtain ⟨n, -, h1⟩ := reach_iterF δ cfg next Good sound good k p0 p g0 h
    obtain ⟨m, c', h2, h3⟩ := stop_halts p (iterF_good next Good good k p0 p g0 h) hs
    exact ⟨n0 + (n + m), c', steps_seq δ h0 (steps_seq δ h1 h2), h3⟩

end

/-- `next` is defined `k` times in a row from `p` (for `decide` / `native_decide`). -/
def checkF {α : Type} (next : α → Option α) : Nat → α → Bool
  | 0, _ => true
  | k + 1, p => match next p with
    | none => false
    | some q => checkF next k q

theorem checkF_sound {α : Type} (next : α → Option α) :
    ∀ k p, checkF next k p = true → ∀ j, j ≤ k → ∃ p', iterF next j p = some p'
  | 0, p, _, j, hj => by rw [show j = 0 by omega]; exact ⟨p, rfl⟩
  | k + 1, p, h, j, hj => by
    simp only [checkF] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp] at h
      cases j with
      | zero => exact ⟨p, rfl⟩
      | succ j =>
        simp only [iterF, hp, Option.bind_some]
        exact checkF_sound next k q h j (by omega)

/-! ## Run-length frames

A tape side as a list of runs `(b, k)`: `k` cells `b`, the first run next to the head.  `runs rs X` writes them in
front of `X`.  `normR` drops empty runs and merges neighbours with the same symbol; `normB` also drops a last run of
0s, which on blank tape changes nothing (`runs_normR`, `runs_normB`).  An `RLFrame` is a state and the run lists
of both sides, the head on the first cell of the right side (on blank tape if that list is empty); `RLFrame.cfg`
is its configuration and `RLFrame.norm` its normal form, with the same configuration (`RLFrame.cfg_norm`).  A
machine's frame map is `fun f => step1 f.norm`, `step1` a match on the first runs of both sides
(`bbtools/listframe.py` generates it, one symbolic run per case); `rl_eq` closes the tape equations between a
symbolic run's end and the frame it is written as. -/

/-- The runs `rs` in front of `X`, the first next to the head. -/
def runs (rs : List (Bool × Nat)) (X : Tape) : Tape := sq (fun p X => rep p.2 [p.1] X) rs X

@[simp] theorem runs_nil (X : Tape) : runs [] X = X := rfl
@[simp] theorem runs_cons (b : Bool) (k : Nat) (rs : List (Bool × Nat)) (X : Tape) :
    runs ((b, k) :: rs) X = rep k [b] (runs rs X) := rfl

theorem runs_append (l l' : List (Bool × Nat)) (X : Tape) : runs (l ++ l') X = runs l (runs l' X) :=
  sq_append _ l l' X

theorem rep1_rep1 (b : Bool) (j k : Nat) (X : Tape) : rep j [b] (rep k [b] X) = rep (j + k) [b] X :=
  (rep_add j k [b] X).symm

theorem rep_false_blank (k : Nat) : rep k [false] blank = blank := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep_succ, ih]; exact cons_false_blank

/-- Drop empty runs, merge neighbouring runs of the same symbol. -/
def normR : List (Bool × Nat) → List (Bool × Nat)
  | [] => []
  | (_, 0) :: rs => normR rs
  | (b, k + 1) :: rs =>
    match normR rs with
    | [] => [(b, k + 1)]
    | (b', k') :: rs' => if b = b' then (b, k + 1 + k') :: rs' else (b, k + 1) :: (b', k') :: rs'

theorem runs_normR : ∀ (rs : List (Bool × Nat)) (X : Tape), runs (normR rs) X = runs rs X
  | [], _ => rfl
  | (_, 0) :: rs, X => by simp only [normR, runs_cons, rep_zero]; exact runs_normR rs X
  | (b, k + 1) :: rs, X => by
    simp only [normR]
    have ih := runs_normR rs X
    split
    · rename_i h; rw [h] at ih; simp only [runs_cons, ← ih, runs_nil]
    · rename_i b' k' rs' h
      rw [h] at ih
      split
      · rename_i hb; subst hb; simp only [runs_cons, ← ih, rep1_rep1]
      · simp only [runs_cons, ← ih]

/-- Drop the last run if it is a run of 0s. -/
def dropZeroLast : List (Bool × Nat) → List (Bool × Nat)
  | [] => []
  | [p] => if p.1 = true then [p] else []
  | p :: q :: rs => p :: dropZeroLast (q :: rs)

theorem runs_dropZeroLast : ∀ rs : List (Bool × Nat), runs (dropZeroLast rs) blank = runs rs blank
  | [] => rfl
  | [(true, k)] => rfl
  | [(false, k)] => by simp only [dropZeroLast, runs_cons, runs_nil, rep_false_blank]; rfl
  | (b, k) :: q :: rs => by
    simp only [dropZeroLast, runs_cons]
    rw [runs_dropZeroLast (q :: rs)]

/-- The normal form of a side that ends in blank tape. -/
def normB (rs : List (Bool × Nat)) : List (Bool × Nat) := dropZeroLast (normR rs)

theorem runs_normB (rs : List (Bool × Nat)) : runs (normB rs) blank = runs rs blank := by
  simp only [normB, runs_dropZeroLast, runs_normR]

/-- A run-length frame: state, runs left of the head (nearest first), runs from the head cell rightwards. -/
structure RLFrame (Q : Type) where
  q : Q
  l : List (Bool × Nat)
  r : List (Bool × Nat)
  deriving DecidableEq, Repr

def RLFrame.cfg {Q : Type} (f : RLFrame Q) : Cfg Q := ⟨runs f.l blank, runs f.r blank, f.q⟩

def RLFrame.norm {Q : Type} (f : RLFrame Q) : RLFrame Q := ⟨f.q, normB f.l, normB f.r⟩

theorem RLFrame.cfg_norm {Q : Type} (f : RLFrame Q) : f.norm.cfg = f.cfg := by
  simp only [RLFrame.cfg, RLFrame.norm, runs_normB]

/-- A one-cell run, for rewriting a symbolic run's cells into runs. -/
theorem cons_rep1 (b : Bool) (X : Tape) : cons b X = rep 1 [b] X := rfl

theorem rep1_cons (b : Bool) (k : Nat) (X : Tape) : rep k [b] (cons b X) = rep (k + 1) [b] X :=
  rep_app_comm k [b] X

theorem rep_congr' {x y : Nat} {w : List Bool} {X Y : Tape} (h : x = y) (h2 : X = Y) : rep x w X = rep y w Y := by
  rw [h, h2]

theorem cfg_congr' {Q : Type} {l l' r r' : Tape} {q : Q} (hl : l = l') (hr : r = r') :
    (⟨l, r, q⟩ : Cfg Q) = ⟨l', r', q⟩ := by rw [hl, hr]

theorem steps_eq_of' {Q : Type} {δ : Q → Bool → Option (Bool × Dir × Q)} {n : Nat} {c c' d d' : Cfg Q}
    (h : steps δ n c = some d) (hc : c = c') (hd : d = d') : steps δ n c' = some d' := by
  rw [← hc, ← hd]; exact h

/-- Close `X = Y` for two tapes written with `cons`, `rep _ [b]`, `runs` of literal lists and context tapes:
unfold the runs, merge neighbouring cells of one symbol into runs, then match run by run, counts by `omega`. -/
macro "rl_eq" : tactic =>
  `(tactic| focus
    try simp only [runs_cons, runs_nil, runs_append, List.cons_append, List.nil_append]
    try simp only [cons_rep1]
    try simp only [rep1_rep1]
    repeat' (first | rfl | apply rep_congr')
    all_goals omega)

/-! ## Case tables

A machine's run-length frame map is a list of cases, each a partial map with its own soundness proof (one symbolic
run); `firstCase` applies the first case that matches, `rlNext` does so on the normal form of the frame, and
`rlNext_sound` is the `sound` hypothesis of `frames_halts_iff` / `frames_no_halt` (with `Good := fun _ => True`).
Keeping the cases as data keeps every proof small: a case's `sound` is a two-way `split` on its own pattern. -/

/-- One case of a frame map: where `apply` is defined, it is a run of the machine. -/
structure RLCase {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q)) where
  apply : RLFrame Q → Option (RLFrame Q)
  sound : ∀ f f', apply f = some f' → ∃ n, 0 < n ∧ steps δ n f.cfg = some f'.cfg

section
variable {Q : Type} {δ : Q → Bool → Option (Bool × Dir × Q)}

/-- The first case that applies. -/
def firstCase : List (RLCase δ) → RLFrame Q → Option (RLFrame Q)
  | [], _ => none
  | c :: cs, f => match c.apply f with
    | some f' => some f'
    | none => firstCase cs f

theorem firstCase_sound : ∀ (cs : List (RLCase δ)) (f f' : RLFrame Q), firstCase cs f = some f' →
    ∃ n, 0 < n ∧ steps δ n f.cfg = some f'.cfg
  | [], _, _, h => by simp [firstCase] at h
  | c :: cs, f, f', h => by
    simp only [firstCase] at h
    cases hc : c.apply f with
    | some g => rw [hc] at h; simp only [Option.some.injEq] at h; subst h; exact c.sound f g hc
    | none => rw [hc] at h; exact firstCase_sound cs f f' h

/-- The frame map of a case table: the first case that applies to the normal form. -/
def rlNext (cs : List (RLCase δ)) (f : RLFrame Q) : Option (RLFrame Q) := firstCase cs f.norm

theorem rlNext_sound (cs : List (RLCase δ)) (f f' : RLFrame Q) (h : rlNext cs f = some f') :
    ∃ n, 0 < n ∧ steps δ n f.cfg = some f'.cfg := by
  obtain ⟨n, hn, h1⟩ := firstCase_sound cs f.norm f' h
  rw [RLFrame.cfg_norm] at h1
  exact ⟨n, hn, h1⟩

/-- If the case table is defined `k` times in a row from `f0` (`checkF`, by `native_decide`), the machine runs
at least `k` steps from `f0.cfg` without halting, through the frames `iterF (rlNext cs) j f0`. -/
theorem rl_reach (cs : List (RLCase δ)) (k : Nat) (f0 f : RLFrame Q) (h : iterF (rlNext cs) k f0 = some f) :
    ∃ n, k ≤ n ∧ steps δ n f0.cfg = some f.cfg :=
  reach_iterF δ RLFrame.cfg (rlNext cs) (fun _ => True) (fun f f' _ h => rlNext_sound cs f f' h)
    (fun _ _ _ _ => trivial) k f0 f trivial h

end

/-! ## From list configurations to frames

`blank_reaches` (`TM.Fin`) turns a run from blank tape, evaluated on lists, into `steps δ n (blankCfg q) = some
c.toCfg`; `FCfg.toCfg_frame` identifies `c.toCfg` with a frame's configuration by a decidable comparison of cell
lists (trailing 0s ignored), so the first frame of a run is reached by `decide`/`native_decide`. -/

/-- The cells of a run list. -/
def rsCells : List (Bool × Nat) → List Bool
  | [] => []
  | (b, k) :: rs => List.replicate k b ++ rsCells rs

/-- A cell list without its trailing 0s. -/
def stripF (l : List Bool) : List Bool := (l.reverse.dropWhile (· == false)).reverse

theorem app_append' (v w : List Bool) (X : Tape) : app (v ++ w) X = app v (app w X) := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.cons_append, app_cons, ih]

theorem rep_eq_app (k : Nat) (b : Bool) (X : Tape) : rep k [b] X = app (List.replicate k b) X := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep_succ, ih, List.replicate_succ]; rfl

theorem runs_eq_app (rs : List (Bool × Nat)) (X : Tape) : runs rs X = app (rsCells rs) X := by
  induction rs with
  | nil => rfl
  | cons p rs ih => obtain ⟨b, k⟩ := p; simp only [runs_cons, rsCells, ih, rep_eq_app, app_append']

theorem app_falses_blank (k : Nat) : app (List.replicate k false) blank = blank := by
  rw [← rep_eq_app]; exact rep_false_blank k

theorem app_stripF (l : List Bool) : app (stripF l) blank = app l blank := by
  -- l = stripF l ++ (0s)
  have key : ∀ (r : List Bool), app ((r.dropWhile (· == false)).reverse) blank = app r.reverse blank := by
    intro r
    induction r with
    | nil => rfl
    | cons a r ih =>
      cases a with
      | false =>
        simp only [List.dropWhile_cons, beq_self_eq_true, ite_true, List.reverse_cons, app_append']
        rw [ih]; simp only [app_cons, app_nil, cons_false_blank]
      | true => simp
  simpa [stripF] using key l.reverse

theorem FCfg.toCfg_frame {Q : Type} (c : FCfg Q) (f : RLFrame Q)
    (hl : stripF c.l = stripF (rsCells f.l)) (hr : stripF c.r = stripF (rsCells f.r)) (hq : c.st = f.q) :
    c.toCfg = f.cfg := by
  simp only [FCfg.toCfg, RLFrame.cfg, runs_eq_app]
  rw [← app_stripF c.l, hl, app_stripF, ← app_stripF c.r, hr, app_stripF, hq]

section
variable {Q : Type} [DecidableEq Q] (δ : Q → Bool → Option (Bool × Dir × Q))

/-- The run of `n` steps from blank tape in state `q` ends at the frame `f` (a decidable check on lists). -/
def frameAt (n : Nat) (q : Q) (f : RLFrame Q) : Bool :=
  match fsteps δ n (FCfg.blank q) with
  | some c => decide (stripF c.l = stripF (rsCells f.l)) && decide (stripF c.r = stripF (rsCells f.r)) &&
      decide (c.st = f.q)
  | none => false

theorem blank_frame {n : Nat} {q : Q} {f : RLFrame Q} (h : frameAt δ n q f = true) :
    steps δ n (blankCfg q) = some f.cfg := by
  unfold frameAt at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hl, hr⟩, hq⟩ := h
    rw [blank_reaches δ hc, FCfg.toCfg_frame c f hl hr hq]
  · simp at h

omit [DecidableEq Q] in
/-- With a start frame reached from blank tape: if the frame map is defined forever along the orbit, the machine
never halts from blank tape. -/
theorem rl_no_halt (cs : List (RLCase δ)) {n0 : Nat} {q : Q} {f0 : RLFrame Q}
    (h0 : steps δ n0 (blankCfg q) = some f0.cfg) (hall : ∀ k, ∃ f, iterF (rlNext cs) k f0 = some f) :
    ¬ Halts δ (blankCfg q) :=
  frames_no_halt δ RLFrame.cfg (rlNext cs) (fun _ => True) (fun f f' _ h => rlNext_sound cs f f' h)
    (fun _ _ _ _ => trivial) h0 trivial hall

end

end TM
