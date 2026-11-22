import Machine

/-! # 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD: one pulse over any list of words

A *word* is `01` or `011` (a 0, then one or two 1s). For every list of words `ws`, every `k` and every tape `L`, `R`
around them, the head in state A at the start of `ws` followed by a run `0 1^(k+3)` sweeps right over the words,
takes three 1s off the run, carries them back left as a packet `111` and stops in state A where it started, with
the words restored and the packet in front of them (`pulse`):

    L | A> ws 0 1^(k+3) R   →   L | A> 111 ws 0 1^k R        in 10·(|ws| + 1) steps.

The three parts: the right sweep (`right_word`: `A> 01 → 11 A>`, `A> 011 → 100 A>`), the turn at the run
(`turn`, 10 steps) and the packet going left (`left_word`: `11 A>111 → A>111 01`, `100 A>111 → A>111 011`). Each
part reads only the cells written in it, so it holds whatever the tape around it is. If the words are followed by
`0001` instead, the sweep halts the machine (`pulse_halt`). Kernel only: `rfl`, `simp`, `omega`. -/

namespace H126068

open TM

/-- A word: `false` is `01`, `true` is `011` (reading order, left to right). -/
def wd : Bool → List Bool
  | false => [false, true]
  | true => [false, true, true]

/-- What the right sweep leaves of a word, nearest cell first as seen from the right: `01 → 11`, `011 → 100`. -/
def im : Bool → List Bool
  | false => [true, true]
  | true => [false, false, true]

/-- A list of words in front of a tape (reading order). -/
def words : List Bool → Tape → Tape
  | [], R => R
  | b :: bs, R => app (wd b) (words bs R)

/-- The images of a list of words, as the tape to the left of the head after the sweep (last word nearest). -/
def images : List Bool → Tape → Tape
  | [], L => L
  | b :: bs, L => images bs (app (im b) L)

/-- Steps of the right sweep over one word. -/
def cr : Bool → Nat
  | false => 2
  | true => 5

/-- Steps of the packet crossing one word leftward. -/
def cl : Bool → Nat
  | false => 8
  | true => 5

theorem right_word (b : Bool) (L R : Tape) :
    steps (cr b) ⟨L, app (wd b) R, .A⟩ = some ⟨app (im b) L, R, .A⟩ := by
  cases b <;> rfl

theorem left_word (b : Bool) (L R : Tape) :
    steps (cl b) ⟨app (im b) L, app [true, true, true] R, .A⟩ =
      some ⟨L, app [true, true, true] (app (wd b) R), .A⟩ := by
  cases b <;> rfl

theorem turn (L R : Tape) :
    steps 10 ⟨L, app [false, true, true, true] R, .A⟩ = some ⟨L, app [true, true, true, false] R, .A⟩ := by
  rfl

/-- Steps of the right sweep over a list of words. -/
def crs : List Bool → Nat
  | [] => 0
  | b :: bs => cr b + crs bs

/-- Steps of the packet over a list of words. -/
def cls : List Bool → Nat
  | [] => 0
  | b :: bs => cls bs + cl b

theorem crs_cls (ws : List Bool) : crs ws + cls ws = 10 * ws.length := by
  induction ws with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [crs, cls, cr, cl] <;> omega

/-- The right sweep over any list of words. -/
theorem right_words (ws : List Bool) (L R : Tape) :
    steps (crs ws) ⟨L, words ws R, .A⟩ = some ⟨images ws L, R, .A⟩ := by
  induction ws generalizing L with
  | nil => rfl
  | cons b bs ih => exact TM.steps_seq trans (right_word b L (words bs R)) (ih (app (im b) L))

/-- The packet `111` crossing any list of words leftward, restoring them. -/
theorem left_words (ws : List Bool) (L R : Tape) :
    steps (cls ws) ⟨images ws L, app [true, true, true] R, .A⟩ =
      some ⟨L, app [true, true, true] (words ws R), .A⟩ := by
  induction ws generalizing L with
  | nil => rfl
  | cons b bs ih => exact TM.steps_seq trans (ih (app (im b) L)) (left_word b L (words bs R))

/-- **One pulse.** From state A at the start of any list of words followed by `0111`, the machine comes back to
the same cell in state A after `10·(|ws|+1)` steps, with the words unchanged, three 1s taken from the run after
them and put in front of them: `L | A> ws 0 1 1 1 R → L | A> 1 1 1 ws 0 R`. With `R = 1^k …` this takes 3 from a
run `1^(k+3)`. -/
theorem pulse (ws : List Bool) (L R : Tape) :
    steps (10 * (ws.length + 1)) ⟨L, words ws (app [false, true, true, true] R), .A⟩ =
      some ⟨L, app [true, true, true] (words ws (app [false] R)), .A⟩ := by
  have h1 := right_words ws L (app [false, true, true, true] R)
  have h2 := turn (images ws L) R
  have h3 := left_words ws L (app [false] R)
  have e : app [true, true, true, false] R = app [true, true, true] (app [false] R) := rfl
  rw [e] at h2
  have h := TM.steps_seq trans (TM.steps_seq trans h1 h2) h3
  exact TM.steps_congr trans (by have := crs_cls ws; omega) h

/-- **A pulse that meets `0001` halts.** The right sweep crosses the words and then writes `111` over the three 0s,
arriving in D on the 1, which is the halting transition D1. -/
theorem pulse_halt (ws : List Bool) (L R : Tape) :
    steps (crs ws + 3) ⟨L, words ws (app [false, false, false, true] R), .A⟩ =
      some ⟨app [true, true, true] (images ws L), app [true] R, .D⟩ ∧
    step ⟨app [true, true, true] (images ws L), app [true] R, .D⟩ = none := by
  refine ⟨TM.steps_seq trans (right_words ws L _) rfl, rfl⟩

end H126068
