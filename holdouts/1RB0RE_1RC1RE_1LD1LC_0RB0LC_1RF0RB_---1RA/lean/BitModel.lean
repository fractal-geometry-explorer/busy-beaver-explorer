import Machine
import TM.MapOrbit

/-!
# 1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA: one round trip is a 4-state automaton on a bit word

Each time the head turns at the left end (state D on the leftmost cell, blank tape on both sides), the tape is
`w0 1 w1 1 ... wm 1` with `w0 = 0`: a word of bits, each followed by a 1 (`Turn`, with the word written without its
leading 0).  One round trip replaces the word `0 u` by `0 (res X u) 0`, where `res` runs a 4-state automaton over `u`
from left to right, writes one bit for each bit read, and adds a tail that depends on the state at the end:

| state | reads 0 | reads 1 | at the end of the word |
|---|---|---|---|
| `X` | writes 1, to `P` | writes 0, stays | the machine halts |
| `P` | writes 1, to `X` | writes 0, to `Y` | adds 1 |
| `Y` | writes 0, to `X` | writes 1, to `Q` | adds 1 1 |
| `Q` | writes 0, to `Y` | writes 1, to `Y` | the machine halts |

`lap`: from `Turn u` the machine reaches `Turn` of the next word in at least one step, or halts when the automaton
ends in `X` or `Q`.  `start`: the run from blank tape is at `Turn [0, 1]` (the word `0 0 1`) after 15 steps.
`halts_iff_model`: so the machine halts from blank tape if and only if the orbit of the word `0 1` under `next`
stops.  Nothing here says whether it does.

How the machine does it.  Going right, state E at a bit is `X` and state A at a bit is `P`; each reads the bit and
the 1 after it and leaves the written bit and a 1 behind (`pass`, the first two parts).  After `P` reads a 1 the
machine is in state B and leaves `0 0`, then `0 1` for every further 1 it reads: these cells are not final.  When a 0
comes, the head goes back over them (`exc`), turns, and crosses them again as a run of zeros in states E and A
alternately (`zeros`), which writes them as `0 1 1 ... 1`; whether the run of ones was even or odd (`Y` or `Q`)
decides the state it arrives in.  At the right end the same happens with the blank tape as the 0.  Going left in
state C, the head moves every cell one place left, so the new word sits one cell further left (`sweep`).
-/

namespace H98995

open TM

/-- The cells of a word: each bit followed by a 1. -/
def enc : List Bool → Tape → Tape
  | [], R => R
  | b :: v, R => cons b (cons true (enc v R))

/-- A word written left of the head (left streams list the nearest cell first). -/
def wr : List Bool → Tape → Tape
  | [], L => L
  | b :: v, L => wr v (cons true (cons b L))

theorem wr_append (a b : List Bool) (L : Tape) : wr (a ++ b) L = wr b (wr a L) := by
  induction a generalizing L with
  | nil => rfl
  | cons x a ih => exact ih _

theorem wr_ones (k : Nat) (L : Tape) : wr (List.replicate k true) L = rep k [true, true] L := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    show wr (List.replicate k true) (cons true (cons true L)) = _
    rw [ih]
    exact rep_app_comm k [true, true] L

/-- The states of the automaton. -/
inductive MS where
  | X | P | Y | Q

/-- The automaton's output on a word, with the tail of the end state and without the final 0; `none` when it ends
in `X` or `Q`, where the machine halts. -/
def res : MS → List Bool → Option (List Bool)
  | .X, [] => none
  | .P, [] => some [true]
  | .Y, [] => some [true, true]
  | .Q, [] => none
  | .X, false :: u => (res .P u).map ([true] ++ ·)
  | .X, true :: u => (res .X u).map ([false] ++ ·)
  | .P, false :: u => (res .X u).map ([true] ++ ·)
  | .P, true :: u => (res .Y u).map ([false] ++ ·)
  | .Y, false :: u => (res .X u).map ([false] ++ ·)
  | .Y, true :: u => (res .Q u).map ([true] ++ ·)
  | .Q, false :: u => (res .Y u).map ([false] ++ ·)
  | .Q, true :: u => (res .Y u).map ([true] ++ ·)

/-- The state after `P` read a 1 and then `k` more ones. -/
def yq (k : Nat) : MS := if k % 2 = 0 then .Y else .Q

theorem yq_even {k : Nat} (h : k % 2 = 0) : yq k = .Y := by simp [yq, h]
theorem yq_odd {k : Nat} (h : k % 2 = 1) : yq k = .Q := by simp [yq, h]

theorem res_yq_true (k : Nat) (u : List Bool) :
    res (yq k) (true :: u) = (res (yq (k + 1)) u).map ([true] ++ ·) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [yq_even h, yq_odd (by omega : (k + 1) % 2 = 1)]; rfl
  · rw [yq_odd h, yq_even (by omega : (k + 1) % 2 = 0)]; rfl

/-- What a rightward pass comes to: with output `o`, the head is past the right end in state C with `o` written
since `L`; with none, the machine halts. -/
def Fin (c : Config) (L : Tape) : Option (List Bool) → Prop
  | some o => Star trans c ⟨wr o L, blank, .C⟩
  | none => Halts trans c

theorem Fin.pre {c c' : Config} {L L' : Tape} (p : List Bool) {o o' : Option (List Bool)} (h : Star trans c c')
    (hL : L' = wr p L) (ho : o' = o.map (p ++ ·)) (hf : Fin c' L' o) : Fin c L o' := by
  subst hL ho
  cases o with
  | none => exact Halts.pre h hf
  | some o =>
    show Star trans c ⟨wr (p ++ o) L, blank, .C⟩
    rw [wr_append]
    exact h.trans hf

/-- A run of `k` zeros is crossed in states E and A alternately, and written as ones. -/
theorem zeros (k : Nat) : ∀ L R : Tape,
    (k % 2 = 0 →
      Star trans ⟨L, rep k [false, true] R, .E⟩ ⟨rep k [true, true] L, R, .E⟩ ∧
      Star trans ⟨L, rep k [false, true] R, .A⟩ ⟨rep k [true, true] L, R, .A⟩) ∧
    (k % 2 = 1 →
      Star trans ⟨L, rep k [false, true] R, .E⟩ ⟨rep k [true, true] L, R, .A⟩ ∧
      Star trans ⟨L, rep k [false, true] R, .A⟩ ⟨rep k [true, true] L, R, .E⟩) := by
  induction k with
  | zero =>
    intro L R
    exact ⟨fun _ => ⟨Star.refl _, Star.refl _⟩, fun h => by omega⟩
  | succ k ih =>
    intro L R
    have sE : Star trans ⟨L, rep (k + 1) [false, true] R, .E⟩ ⟨cons true (cons true L), rep k [false, true] R, .A⟩ :=
      ⟨2, rfl⟩
    have sA : Star trans ⟨L, rep (k + 1) [false, true] R, .A⟩ ⟨cons true (cons true L), rep k [false, true] R, .E⟩ :=
      ⟨2, rfl⟩
    have e : rep k [true, true] (cons true (cons true L)) = rep (k + 1) [true, true] L :=
      rep_app_comm k [true, true] L
    obtain ⟨h0, h1⟩ := ih (cons true (cons true L)) R
    rw [e] at h0 h1
    constructor
    · intro h
      obtain ⟨a, b⟩ := h1 (by omega)
      exact ⟨sE.trans b, sA.trans a⟩
    · intro h
      obtain ⟨a, b⟩ := h0 (by omega)
      exact ⟨sE.trans b, sA.trans a⟩

/-- The way back: in state B after `0 (0 1)^k 0`, on a 0 followed by the cell `c`, the head returns over the `k`
pairs, turns, and stands in state E at their start, with the pairs now zeros to cross. -/
theorem exc (k : Nat) (c : Bool) (L R : Tape) :
    Star trans ⟨cons false (rep k [true, false] (cons false L)), cons false (cons c R), .B⟩
      ⟨cons true (cons false L), rep k [false, true] (cons c (cons true R)), .E⟩ := by
  have s1 : Star trans ⟨cons false (rep k [true, false] (cons false L)), cons false (cons c R), .B⟩
      ⟨rep k [true, false] (cons false L), cons false (cons c (cons true R)), .C⟩ := by
    cases c <;> exact ⟨3, rfl⟩
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩
      = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have s2 : Star trans ⟨rep k [true, false] (cons false L), cons false (cons c (cons true R)), .C⟩
      ⟨cons false L, cons false (rep k [false, true] (cons c (cons true R))), .C⟩ :=
    ⟨k * 2, cross_l trans c0 k _ _⟩
  have s3 : Star trans ⟨cons false L, cons false (rep k [false, true] (cons c (cons true R))), .C⟩
      ⟨cons true (cons false L), rep k [false, true] (cons c (cons true R)), .E⟩ := ⟨3, rfl⟩
  exact (s1.trans s2).trans s3

/-- The rightward pass over a word, from each of the three kinds of place the head can be in: state E (`X`), state A
(`P`), and state B after `0 (0 1)^k 0` (`Y` for even `k`, `Q` for odd `k`, with the bits `0 1^k` still to be
written). -/
theorem pass (u : List Bool) :
    (∀ L : Tape, Fin ⟨L, enc u blank, .E⟩ L (res .X u)) ∧
    (∀ L : Tape, Fin ⟨L, enc u blank, .A⟩ L (res .P u)) ∧
    (∀ (k : Nat) (L : Tape), Fin ⟨cons false (rep k [true, false] (cons false L)), enc u blank, .B⟩ L
      ((res (yq k) u).map ((false :: List.replicate k true) ++ ·))) := by
  induction u with
  | nil =>
    refine ⟨fun L => ?_, fun L => ?_, fun k L => ?_⟩
    · exact halts_at (n := 1) (d := ⟨cons true L, blank, .F⟩) rfl rfl rfl
    · exact (⟨2, rfl⟩ : Star trans ⟨L, blank, .A⟩ ⟨wr [true] L, blank, .C⟩)
    · have hb : (blank : Tape) = cons false (cons false blank) := by rw [cons_false_blank, cons_false_blank]
      have s1 : Star trans ⟨cons false (rep k [true, false] (cons false L)), enc [] blank, .B⟩
          ⟨cons true (cons false L), rep k [false, true] (cons false (cons true blank)), .E⟩ := by
        have h := exc k false L blank
        rw [← hb] at h
        exact h
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · rw [yq_even h]
        have s2 := ((zeros k (cons true (cons false L)) (cons false (cons true blank))).1 h).1
        have s3 : Star trans ⟨rep k [true, true] (cons true (cons false L)), cons false (cons true blank), .E⟩
            ⟨wr [true, true] (rep k [true, true] (cons true (cons false L))), blank, .C⟩ := ⟨4, rfl⟩
        show Star trans _ ⟨wr ((false :: List.replicate k true) ++ [true, true]) L, blank, .C⟩
        rw [wr_append]
        have e : wr (false :: List.replicate k true) L = rep k [true, true] (cons true (cons false L)) :=
          wr_ones k _
        rw [e]
        exact (s1.trans s2).trans s3
      · rw [yq_odd h]
        have s2 := ((zeros k (cons true (cons false L)) (cons false (cons true blank))).2 h).1
        have s3 : Halts trans ⟨rep k [true, true] (cons true (cons false L)), cons false (cons true blank), .A⟩ :=
          halts_at (n := 3)
            (d := ⟨cons true (cons true (cons true (rep k [true, true] (cons true (cons false L))))), blank, .F⟩)
            rfl rfl rfl
        exact Halts.pre (s1.trans s2) s3
  | cons b u ih =>
    obtain ⟨ihX, ihP, ihB⟩ := ih
    refine ⟨fun L => ?_, fun L => ?_, fun k L => ?_⟩
    · cases b
      · exact Fin.pre [true] (⟨2, rfl⟩ : Star trans ⟨L, enc (false :: u) blank, .E⟩ ⟨wr [true] L, enc u blank, .A⟩)
          rfl rfl (ihP _)
      · exact Fin.pre [false] (⟨2, rfl⟩ : Star trans ⟨L, enc (true :: u) blank, .E⟩ ⟨wr [false] L, enc u blank, .E⟩)
          rfl rfl (ihX _)
    · cases b
      · exact Fin.pre [true] (⟨2, rfl⟩ : Star trans ⟨L, enc (false :: u) blank, .A⟩ ⟨wr [true] L, enc u blank, .E⟩)
          rfl rfl (ihX _)
      · have s : Star trans ⟨L, enc (true :: u) blank, .A⟩
            ⟨cons false (rep 0 [true, false] (cons false L)), enc u blank, .B⟩ := ⟨2, rfl⟩
        refine Fin.pre [] s rfl ?_ (ihB 0 L)
        have e : yq 0 = .Y := rfl
        rw [e]
        show (res .Y u).map ([false] ++ ·) = _
        cases res .Y u <;> rfl
    · cases b
      · have s1 : Star trans ⟨cons false (rep k [true, false] (cons false L)), enc (false :: u) blank, .B⟩
            ⟨cons true (cons false L), rep k [false, true] (cons true (cons true (enc u blank))), .E⟩ :=
          exc k true L (enc u blank)
        have e : wr (false :: List.replicate k true) L = rep k [true, true] (cons true (cons false L)) :=
          wr_ones k _
        rcases Nat.mod_two_eq_zero_or_one k with h | h
        · rw [yq_even h]
          have s2 := ((zeros k (cons true (cons false L)) (cons true (cons true (enc u blank)))).1 h).1
          have s3 : Star trans
              ⟨rep k [true, true] (cons true (cons false L)), cons true (cons true (enc u blank)), .E⟩
              ⟨wr [false] (rep k [true, true] (cons true (cons false L))), enc u blank, .E⟩ := ⟨2, rfl⟩
          refine Fin.pre ((false :: List.replicate k true) ++ [false]) ((s1.trans s2).trans s3) ?_ ?_ (ihX _)
          · rw [wr_append, e]
          · show ((res .X u).map ([false] ++ ·)).map ((false :: List.replicate k true) ++ ·) = _
            cases res .X u <;> simp
        · rw [yq_odd h]
          have s2 := ((zeros k (cons true (cons false L)) (cons true (cons true (enc u blank)))).2 h).1
          have s3 : Star trans
              ⟨rep k [true, true] (cons true (cons false L)), cons true (cons true (enc u blank)), .A⟩
              ⟨cons false (rep 0 [true, false] (cons false (rep k [true, true] (cons true (cons false L))))),
                enc u blank, .B⟩ := ⟨2, rfl⟩
          exact Fin.pre (false :: List.replicate k true) ((s1.trans s2).trans s3) e.symm rfl (ihB 0 _)
      · have s : Star trans ⟨cons false (rep k [true, false] (cons false L)), enc (true :: u) blank, .B⟩
            ⟨cons false (rep (k + 1) [true, false] (cons false L)), enc u blank, .B⟩ := ⟨2, rfl⟩
        refine Fin.pre [] s rfl ?_ (ihB (k + 1) L)
        rw [res_yq_true]
        cases res (yq (k + 1)) u <;> simp [List.replicate_succ']

/-- Going left in state C, every cell moves one place left: a written word comes back as the cells of a word,
with the cell under the head as its last bit. -/
theorem sweep (v : List Bool) : ∀ (b c : Bool) (L R : Tape),
    Star trans ⟨wr (b :: v) L, cons c R, .C⟩ ⟨L, cons b (enc (v ++ [c]) R), .C⟩ := by
  have rule : ∀ (b c : Bool) (L R : Tape),
      Star trans ⟨cons true (cons b L), cons c R, .C⟩ ⟨L, cons b (cons c (cons true R)), .C⟩ := by
    intro b c L R
    cases c <;> exact ⟨2, rfl⟩
  induction v with
  | nil => exact rule
  | cons b' v ih =>
    intro b c L R
    exact (ih b' c (cons true (cons b L)) R).trans (rule b b' L (enc (v ++ [c]) R))

/-- The left-end turn with the word `0 u` on the tape. -/
def Turn (u : List Bool) : Config := ⟨blank, enc (false :: u) blank, .D⟩

/-- One round trip on the word without its leading 0. -/
def next (u : List Bool) : Option (List Bool) := (res .X u).map (· ++ [false])

/-- One round trip of the machine is one step of `next`. -/
theorem lap (u : List Bool) : Lands trans (fun u c => c = Turn u) (Turn u) (next u) := by
  have s0 : Plus trans (Turn u) ⟨wr [false] blank, enc u blank, .E⟩ := ⟨1, rfl⟩
  have h := (pass u).1 (wr [false] blank)
  unfold next
  cases e : res .X u with
  | none =>
    rw [e] at h
    exact Halts.pre s0.star h
  | some o =>
    rw [e] at h
    have h' : Star trans ⟨wr [false] blank, enc u blank, .E⟩ ⟨wr (false :: o) blank, cons false blank, .C⟩ := by
      rw [cons_false_blank]
      exact h
    have s2 := sweep o false false blank blank
    have s3 : Star trans ⟨blank, cons false (enc (o ++ [false]) blank), .C⟩ (Turn (o ++ [false])) := ⟨1, rfl⟩
    exact ⟨_, s0.trans_star ((h'.trans s2).trans s3), rfl⟩

/-- From blank tape the machine is at the turn with the word `0 0 1` after 15 steps. -/
theorem start : steps 15 init = some (Turn [false, true]) := rfl

/-- **The machine halts from blank tape if and only if the orbit of the word `0 1` under `next` stops.** -/
theorem halts_iff_model : HaltsFromBlank ↔ ∃ n, orbit next [false, true] n = none :=
  halts_iff_orbit (Rel := fun u c => c = Turn u) ⟨15, _, start, rfl⟩ (fun u c h => by subst h; exact lap u)

end H98995
