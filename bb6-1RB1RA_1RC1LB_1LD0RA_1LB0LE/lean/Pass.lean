import Blank
import Rules

/-!
# One pass, in closed form, for every block list

A pass start is the tape `1^y1 0 1^y2 0 ... 0 1^yk A>0` with blank tape on both sides.  Here the block list is kept
nearest first, `zs = [yk, ..., y1]`, as the left stream lists cells: `enc zs` is the left stream, and the pass start
is `⟨enc zs, blank, .A⟩`.  Blank tape is the pass start of `[]`.

`next zs` is the closed form of `py/passmap.py`, written recursively:

* `yk = 2m` even: the sweep stops at once; `yk` is dropped and the two blocks before it gain `m + 2` (`bump`).
* `yk` odd: the sweep crosses `yk`, then every even block on its left (`sweep`), recording `g = y/2 - 1` for each
  and `g = (yk + 3)/2` for `yk`.  At the first odd block `y = 2n + 3` it stops: the two blocks before it gain `n + 1`,
  and the zigzag back to the right end (`zag`) turns each recorded `g` into a block.
* the sweep halts if it runs off the left end or meets an empty block (`.halt`), and the closed form is not known
  when it stops at a block of a single 1 (`.one`).

`pass` proves that the machine goes from `⟨enc zs, blank, .A⟩` to `⟨enc zs', blank, .A⟩` whenever
`next zs = .ok zs'`, and `pass_halt` that it halts whenever `next zs = .halt`.  From these and a count of ones
(`next_sum`: a pass adds 4 ones; a halting pass needs an odd count), `halts_only_by_one`: if the machine halts from
blank tape, the orbit of the closed form reaches a pass whose sweep stops at a block of a single 1.

All of it is checked by Lean's kernel, with no `native_decide`: the axioms are `propext`, `Quot.sound` and, for the
last theorems (a proof by contradiction), `Classical.choice` (`Axioms.lean`).
-/

namespace BB6d

open TM

/-! ## The tapes -/

/-- The left stream of the block list `zs`, nearest block first. -/
def enc : List Nat → Tape
  | [] => blank
  | y :: ys => rep y [true] (cons false (enc ys))

/-- What the sweep leaves on the right of the head, after the first crossed stretch: each recorded `g` as
`0 0 1 (01)^g`, then blank. -/
def U : List Nat → Tape
  | [] => blank
  | g :: gs => app [false, false, true] (rep g [false, true] (U gs))

theorem enc_nil_pad : enc [0, 0] = enc [] := by
  show cons false (cons false blank) = blank
  rw [cons_false_blank, cons_false_blank]

theorem enc_one_pad (b : Nat) : enc [b, 0] = enc [b] := by
  show rep b [true] (cons false (cons false blank)) = rep b [true] (cons false blank)
  congr 2; exact cons_false_blank

theorem rep_two (g : Nat) (s : Tape) : rep (2 * g) [true] s = rep g [true, true] s := by
  induction g with
  | zero => rfl
  | succ g ih =>
    rw [show 2 * (g + 1) = 2 * g + 1 + 1 by omega, rep_succ, rep_succ, ih]; rfl

theorem rep_two_one (g : Nat) (s : Tape) : rep (2 * g + 1) [true] s = rep g [true, true] (cons true s) := by
  rw [rep_add, ← rep_two]; rfl

theorem rot (n : Nat) (s : Tape) : cons false (rep n [true, false] s) = rep n [false, true] (cons false s) :=
  rep_rotate n [false] [true, false] [false, true] rfl s

/-! ## The closed form -/

/-- The outcome of a pass. -/
inductive Next where
  | ok (zs : List Nat)
  | halt
  | one
  deriving DecidableEq, Repr

/-- The two blocks nearest the head gain `k` each (blank on the left read as empty blocks): the new nearest block and
the rest. -/
def bump (k : Nat) : List Nat → Nat × List Nat
  | [] => (k, [k])
  | [b] => (b + k, [k])
  | b :: a :: ms => (b + k, (a + k) :: ms)

/-- The zigzag back to the right end: the nearest block `q`, the blocks `ms` behind it, and the recorded `gs`
(nearest first).  Each `g` adds `g + 2` ones to the block before it and becomes a block of `g` ones. -/
def zag (q : Nat) (ms : List Nat) : List Nat → List Nat
  | [] => q :: ms
  | g :: gs => zag g ((q + g + 2) :: ms) gs

/-- The sweep, with `E` at the 0 right of the block list `ys`, having recorded `gs`. -/
def sweep (gs : List Nat) : List Nat → Next
  | [] => .halt
  | y :: ys =>
    if y % 2 = 0 then
      if y = 0 then .halt else sweep ((y / 2 - 1) :: gs) ys
    else if y = 1 then .one
    else .ok (zag (bump ((y - 1) / 2) ys).1 (bump ((y - 1) / 2) ys).2 gs)

/-- The pass map, on block lists nearest first. -/
def next : List Nat → Next
  | [] => .ok [2, 2]
  | y :: ys =>
    if y % 2 = 0 then .ok ((bump (y / 2 + 2) ys).1 :: (bump (y / 2 + 2) ys).2)
    else sweep [(y + 3) / 2] ys

/-- The pass starts from blank tape (pass 0 is blank tape itself). -/
def orbit : Nat → Next
  | 0 => .ok []
  | n + 1 =>
    match orbit n with
    | .ok zs => next zs
    | e => e

/-! ## Runs -/

/-- `c` reaches `c'`. -/
def Reach (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reach.refl (c : Config) : Reach c c := ⟨0, rfl⟩

theorem Reach.of {n : Nat} {c c' : Config} (h : steps n c = some c') : Reach c c' := ⟨n, h⟩

theorem Reach.trans {c c' c'' : Config} (h₁ : Reach c c') (h₂ : Reach c' c'') : Reach c c'' := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨a + b, steps_seq BB6d.trans ha hb⟩

/-- `r` rounds of the zigzag: `M 0 1^p 0 1^q A> (01)^r R` to `M 0 1^(p+r) 0 1^(q+r) A> R`. -/
theorem zigs (r : Nat) : ∀ (p q : Nat) (M R : Tape),
    Reach ⟨rep q [true] (cons false (rep p [true] (cons false M))), rep r [false, true] R, .A⟩
      ⟨rep (q + r) [true] (cons false (rep (p + r) [true] (cons false M))), R, .A⟩ := by
  induction r with
  | zero => intro p q M R; exact Reach.refl _
  | succ r ih =>
    intro p q M R
    have e₁ : q + (r + 1) = (q + 1) + r := by omega
    have e₂ : p + (r + 1) = (p + 1) + r := by omega
    rw [e₁, e₂]
    refine Reach.trans ?_ (ih (p + 1) (q + 1) M R)
    cases q with
    | zero => exact Reach.of (zig_empty (rep p [true] (cons false M)) (rep r [false, true] R))
    | succ q => exact Reach.of (zig q (rep p [true] (cons false M)) (rep r [false, true] R))

/-- The zigzag through what the sweep left. -/
theorem zag_run (gs : List Nat) : ∀ (q : Nat) (ms : List Nat),
    Reach ⟨enc (q :: ms), U gs, .A⟩ ⟨enc (zag q ms gs), blank, .A⟩ := by
  induction gs with
  | nil => intro q ms; exact Reach.refl _
  | cons g gs ih =>
    intro q ms
    have h₁ := turn (enc (q :: ms)) (rep g [false, true] (U gs))
    have h₂ := zigs g (q + 2) 0 (enc ms) (U gs)
    rw [show 0 + g = g by omega, show q + 2 + g = q + g + 2 by omega] at h₂
    exact Reach.trans (Reach.of h₁) (Reach.trans h₂ (ih g ((q + g + 2) :: ms)))

/-- Padding: blank on the left reads as empty blocks. -/
theorem pad (ys : List Nat) : ∃ b a ms, enc ys = enc (b :: a :: ms) ∧ ∀ k, bump k ys = (b + k, (a + k) :: ms) := by
  match ys with
  | [] => exact ⟨0, 0, [], enc_nil_pad.symm, fun k => by simp [bump]⟩
  | [b] => exact ⟨b, 0, [], (enc_one_pad b).symm, fun k => by simp [bump]⟩
  | b :: a :: ms => exact ⟨b, a, ms, rfl, fun k => rfl⟩

/-- The sweep stops (D at the 0 right of `ys`): D turns, B runs back, and `n` rounds of the zigzag follow. -/
theorem stop (b a : Nat) (ms : List Nat) (n : Nat) (X : Tape) :
    Reach ⟨enc (b :: a :: ms), cons false (cons true (cons false (rep n [true, false] X))), .D⟩
      ⟨enc ((b + (n + 1)) :: (a + (n + 1)) :: ms), cons false X, .A⟩ := by
  -- D turns: the 0 before the block `b` moves one cell right
  have h₁ : Reach ⟨enc (b :: a :: ms), cons false (cons true (cons false (rep n [true, false] X))), .D⟩
      ⟨cons false (enc ((a + 1) :: ms)), rep (b + 1) [true] (cons false (rep n [true, false] X)), .A⟩ := by
    cases b with
    | zero => exact Reach.of (d_stop_empty (enc (a :: ms)) _)
    | succ b =>
      have h := d_stop b (enc (a :: ms)) (cons true (cons false (rep n [true, false] X)))
      have e : rep b [true] (cons true (cons true (cons false (rep n [true, false] X))))
          = rep (b + 1 + 1) [true] (cons false (rep n [true, false] X)) := by
        rw [← rep_app_comm, ← rep_app_comm]; rfl
      rw [e] at h
      exact Reach.of h
  have h₂ := a_sweep (b + 1) (cons false (enc ((a + 1) :: ms))) (cons false (rep n [true, false] X))
  have h₃ := zigs n (a + 1) (b + 1) (enc ms) (cons false X)
  rw [show b + 1 + n = b + (n + 1) by omega, show a + 1 + n = a + (n + 1) by omega, ← rot] at h₃
  exact Reach.trans h₁ (Reach.trans (Reach.of h₂) h₃)

/-- E crosses an even block `2g + 2` and continues into the next. -/
theorem cross_even (g : Nat) (ys : List Nat) (g₀ : Nat) (gs : List Nat) :
    Reach ⟨enc ((2 * g + 2) :: ys), cons false (rep g₀ [false, true] (U gs)), .E⟩
      ⟨enc ys, cons false (rep g [false, true] (U (g₀ :: gs))), .E⟩ := by
  have h₁ := e_cross (rep (2 * g) [true] (cons false (enc ys))) (rep g₀ [false, true] (U gs))
  have h₂ := de_sweep g (enc ys) (cons false (cons true (rep g₀ [false, true] (U gs))))
  rw [← rep_two] at h₂
  rw [rot] at h₂
  exact Reach.trans (Reach.of h₁) (Reach.of h₂)

/-- The sweep in closed form: from E at the 0 right of `ys`, having recorded `g₀ :: gs`. -/
theorem sweep_run (ys : List Nat) : ∀ (g₀ : Nat) (gs : List Nat) (out : List Nat),
    sweep (g₀ :: gs) ys = .ok out →
    Reach ⟨enc ys, cons false (rep g₀ [false, true] (U gs)), .E⟩ ⟨enc out, blank, .A⟩ := by
  induction ys with
  | nil => intro g₀ gs out h; simp [sweep] at h
  | cons y ys ih =>
    intro g₀ gs out h
    unfold sweep at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy] at h
      by_cases h0 : y = 0
      · rw [if_pos h0] at h; cases h
      rw [if_neg h0] at h
      obtain ⟨g, rfl⟩ : ∃ g, y = 2 * g + 2 := ⟨y / 2 - 1, by omega⟩
      rw [show (2 * g + 2) / 2 - 1 = g by omega] at h
      exact Reach.trans (cross_even g ys g₀ gs) (ih g (g₀ :: gs) out h)
    · rw [if_neg hy] at h
      by_cases h1 : y = 1
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      obtain ⟨n, rfl⟩ : ∃ n, y = 2 * n + 3 := ⟨(y - 3) / 2, by omega⟩
      rw [show (2 * n + 3 - 1) / 2 = n + 1 by omega] at h
      obtain ⟨b, a, ms, he, hb⟩ := pad ys
      rw [hb] at h
      cases h
      -- E crosses into the odd block, D reaches the 0 before it
      have h₁ := e_cross (rep (2 * n + 1) [true] (cons false (enc ys))) (rep g₀ [false, true] (U gs))
      have h₂ := de_sweep_odd n (enc ys) (cons false (cons true (rep g₀ [false, true] (U gs))))
      rw [← rep_two_one] at h₂
      have h₃ := stop b a ms n (cons false (cons true (rep g₀ [false, true] (U gs))))
      rw [← he] at h₃
      have h₄ := zag_run (g₀ :: gs) (b + (n + 1)) ((a + (n + 1)) :: ms)
      exact Reach.trans (Reach.of h₁) (Reach.trans (Reach.of h₂) (Reach.trans h₃ h₄))

theorem blank3 : (blank : Tape) = cons false (cons false (cons false blank)) := by
  rw [cons_false_blank, cons_false_blank, cons_false_blank]

/-- **One pass in closed form**: from the pass start of `zs` the machine reaches the pass start of `next zs`. -/
theorem pass (zs out : List Nat) (h : next zs = .ok out) :
    ∃ n, steps (n + 1) ⟨enc zs, blank, .A⟩ = some ⟨enc out, blank, .A⟩ := by
  suffices hr : ∀ y ys, (y :: ys = zs ∨ (zs = [] ∧ y = 0 ∧ ys = [])) →
      Reach ⟨cons true (enc (y :: ys)), cons true (cons true blank), .D⟩ ⟨enc out, blank, .A⟩ by
    have hs : ∀ y ys, enc (y :: ys) = enc zs → (y :: ys = zs ∨ (zs = [] ∧ y = 0 ∧ ys = [])) →
        ∃ n, steps (n + 1) ⟨enc zs, blank, .A⟩ = some ⟨enc out, blank, .A⟩ := by
      intro y ys he hor
      obtain ⟨k, hk⟩ := hr y ys hor
      have h₀ := start (enc (y :: ys)) blank
      rw [← blank3] at h₀
      have h₂ := steps_seq trans h₀ hk
      rw [he] at h₂
      exact ⟨k + 2, steps_congr trans (a := 3 + k) (by omega) h₂⟩
    match zs with
    | [] => exact hs 0 [] (by simp [enc, rep, cons_false_blank]) (Or.inr ⟨rfl, rfl, rfl⟩)
    | y :: ys => exact hs y ys rfl (Or.inl rfl)
  intro y ys hor
  have hn : next (y :: ys) = .ok out := by
    rcases hor with e | ⟨rfl, rfl, rfl⟩
    · rw [e]; exact h
    · exact h
  rw [next] at hn
  by_cases hy : y % 2 = 0
  · -- even: D reaches the 0 before the block at once
    rw [if_pos hy] at hn
    cases hn
    obtain ⟨m, rfl⟩ : ∃ m, y = 2 * m := ⟨y / 2, by omega⟩
    rw [show 2 * m / 2 + 2 = m + 2 by omega]
    obtain ⟨b, a, ms, he, hb⟩ := pad ys
    rw [hb]
    have h₁ := de_sweep_odd m (enc ys) (cons true blank)
    rw [← rep_two_one] at h₁
    have h₂ := stop b a ms m (cons true blank)
    rw [← he] at h₂
    have h₃ := zigs 1 (a + (m + 1)) (b + (m + 1)) (enc ms) blank
    rw [show b + (m + 1) + 1 = b + (m + 2) by omega, show a + (m + 1) + 1 = a + (m + 2) by omega] at h₃
    exact Reach.trans (Reach.of h₁) (Reach.trans h₂ h₃)
  · -- odd: D and E cross the block, then the sweep goes on
    rw [if_neg hy] at hn
    obtain ⟨c, rfl⟩ : ∃ c, y = 2 * c + 1 := ⟨y / 2, by omega⟩
    rw [show (2 * c + 1 + 3) / 2 = c + 2 by omega] at hn
    have h₁ := de_sweep (c + 1) (enc ys) (cons true blank)
    rw [← rep_two] at h₁
    have e : cons false (cons false (rep (c + 1) [true, false] (cons true blank)))
        = cons false (rep (c + 2) [false, true] (U [])) := by
      rw [rot]; exact congrArg (cons false) (rep_app_comm (c + 1) [false, true] blank)
    rw [e] at h₁
    exact Reach.trans (Reach.of h₁) (sweep_run ys (c + 2) [] out hn)

/-! ## Halting -/

/-- `0 E>0` halts. -/
theorem halts_at (L R : Tape) : Halts trans ⟨cons false L, cons false R, .E⟩ :=
  let ⟨c, h₁, h₂⟩ := halt_shape L R
  ⟨1, c, h₁, h₂⟩

theorem Reach.halts {c c' : Config} (h₁ : Reach c c') (h₂ : Halts BB6d.trans c') : Halts BB6d.trans c := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, d, hb, hd⟩ := h₂
  exact ⟨a + b, d, steps_seq BB6d.trans ha hb, hd⟩

theorem sweep_halt (ys : List Nat) : ∀ (g₀ : Nat) (gs : List Nat),
    sweep (g₀ :: gs) ys = .halt → Halts trans ⟨enc ys, cons false (rep g₀ [false, true] (U gs)), .E⟩ := by
  induction ys with
  | nil =>
    intro g₀ gs _
    have h := halts_at blank (rep g₀ [false, true] (U gs))
    rwa [cons_false_blank] at h
  | cons y ys ih =>
    intro g₀ gs h
    unfold sweep at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy] at h
      by_cases h0 : y = 0
      · subst h0; exact halts_at (enc ys) _
      rw [if_neg h0] at h
      obtain ⟨g, rfl⟩ : ∃ g, y = 2 * g + 2 := ⟨y / 2 - 1, by omega⟩
      rw [show (2 * g + 2) / 2 - 1 = g by omega] at h
      exact Reach.halts (cross_even g ys g₀ gs) (ih g (g₀ :: gs) h)
    · rw [if_neg hy] at h
      by_cases h1 : y = 1
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h; cases h

/-- When the closed form says halt, the machine halts. -/
theorem pass_halt (zs : List Nat) (h : next zs = .halt) : Halts trans ⟨enc zs, blank, .A⟩ := by
  match zs, h with
  | y :: ys, h =>
    rw [next] at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy] at h; cases h
    rw [if_neg hy] at h
    obtain ⟨c, rfl⟩ : ∃ c, y = 2 * c + 1 := ⟨y / 2, by omega⟩
    rw [show (2 * c + 1 + 3) / 2 = c + 2 by omega] at h
    have h₀ := start (enc ((2 * c + 1) :: ys)) blank
    rw [← blank3] at h₀
    have h₁ := de_sweep (c + 1) (enc ys) (cons true blank)
    rw [← rep_two] at h₁
    have e : cons false (cons false (rep (c + 1) [true, false] (cons true blank)))
        = cons false (rep (c + 2) [false, true] (U [])) := by
      rw [rot]; exact congrArg (cons false) (rep_app_comm (c + 1) [false, true] blank)
    rw [e] at h₁
    exact Reach.halts (Reach.of h₀) (Reach.halts (Reach.of h₁) (sweep_halt ys (c + 2) [] h))

/-! ## Counting ones -/

/-- All blocks are nonempty. -/
def Pos (zs : List Nat) : Prop := ∀ y ∈ zs, 0 < y

/-- The last of `gs`, or `q` if there is none. -/
def lastOr : Nat → List Nat → Nat
  | q, [] => q
  | _, g :: gs => lastOr g gs

theorem lastOr_cons (q g : Nat) (gs : List Nat) (h : gs ≠ []) : lastOr q (g :: gs) = lastOr q gs := by
  match gs, h with
  | _ :: _, _ => rfl

theorem zag_sum (gs : List Nat) : ∀ (q : Nat) (ms : List Nat),
    (zag q ms gs).sum = q + ms.sum + 2 * gs.sum + 2 * gs.length := by
  induction gs with
  | nil => intro q ms; simp [zag]
  | cons g gs ih => intro q ms; simp only [zag, ih, List.sum_cons, List.length_cons]; omega

theorem zag_pos (gs : List Nat) : ∀ (q : Nat) (ms : List Nat), Pos ms → 0 < lastOr q gs → Pos (zag q ms gs) := by
  induction gs with
  | nil =>
    intro q ms hm hq y hy
    simp only [zag, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hq
    · exact hm y hy
  | cons g gs ih =>
    intro q ms hm hq
    apply ih
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · omega
      · exact hm y hy
    · exact hq

theorem bump_sum (k : Nat) (ys : List Nat) : (bump k ys).1 + (bump k ys).2.sum = ys.sum + 2 * k := by
  match ys with
  | [] => simp [bump]; omega
  | [b] => simp [bump]; omega
  | b :: a :: ms => simp [bump]; omega

theorem bump_pos (k : Nat) (ys : List Nat) (hk : 0 < k) (h : Pos ys) :
    0 < (bump k ys).1 ∧ Pos (bump k ys).2 := by
  match ys with
  | [] => exact ⟨hk, by simp [Pos, bump]; omega⟩
  | [b] => exact ⟨by simp [bump]; omega, by simp [Pos, bump]; omega⟩
  | b :: a :: ms =>
    refine ⟨by simp [bump]; omega, ?_⟩
    intro y hy
    simp only [bump, List.mem_cons] at hy
    rcases hy with rfl | hy
    · omega
    · exact h y (by simp [hy])

theorem sweep_ok (ys : List Nat) : ∀ (gs : List Nat) (out : List Nat), gs ≠ [] → 0 < lastOr 0 gs → Pos ys →
    sweep gs ys = .ok out → out.sum + 1 = ys.sum + 2 * gs.sum + 2 * gs.length ∧ Pos out := by
  induction ys with
  | nil => intro gs out _ _ _ h; simp [sweep] at h
  | cons y ys ih =>
    intro gs out hne hl hp h
    have hpy : 0 < y := hp y (by simp)
    have hps : Pos ys := fun z hz => hp z (by simp [hz])
    unfold sweep at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy, if_neg (by omega)] at h
      have := ih ((y / 2 - 1) :: gs) out (by simp) (by rw [lastOr_cons _ _ _ hne]; exact hl) hps h
      simp only [List.sum_cons, List.length_cons] at this ⊢
      refine ⟨by omega, this.2⟩
    · rw [if_neg hy] at h
      by_cases h1 : y = 1
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      cases h
      have hb := bump_sum ((y - 1) / 2) ys
      have hbp := bump_pos ((y - 1) / 2) ys (by omega) hps
      refine ⟨?_, zag_pos gs _ _ hbp.2 ?_⟩
      · rw [zag_sum]; simp only [List.sum_cons]; omega
      · match gs, hne with
        | g :: gs, _ =>
          show 0 < lastOr g gs
          match gs with
          | [] => exact hl
          | g' :: gs' => exact hl

/-- A pass adds 4 ones and keeps every block nonempty. -/
theorem next_sum (zs out : List Nat) (hp : Pos zs) (h : next zs = .ok out) : out.sum = zs.sum + 4 ∧ Pos out := by
  match zs with
  | [] =>
    simp [next] at h; subst h; exact ⟨rfl, by simp [Pos]⟩
  | y :: ys =>
    have hps : Pos ys := fun z hz => hp z (by simp [hz])
    rw [next] at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy] at h
      cases h
      have hb := bump_sum (y / 2 + 2) ys
      have hbp := bump_pos (y / 2 + 2) ys (by omega) hps
      refine ⟨?_, ?_⟩
      · simp only [List.sum_cons]; omega
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hbp.1
        · exact hbp.2 z hz
    · rw [if_neg hy] at h
      have := sweep_ok ys [(y + 3) / 2] out (by simp) (by simp [lastOr]) hps h
      simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at this ⊢
      exact ⟨by omega, this.2⟩

theorem sweep_halt_even (ys : List Nat) : ∀ (gs : List Nat), Pos ys → sweep gs ys = .halt → ys.sum % 2 = 0 := by
  induction ys with
  | nil => intro _ _ _; rfl
  | cons y ys ih =>
    intro gs hp h
    have hpy : 0 < y := hp y (by simp)
    have hps : Pos ys := fun z hz => hp z (by simp [hz])
    unfold sweep at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy, if_neg (by omega)] at h
      have := ih _ hps h
      simp only [List.sum_cons]; omega
    · rw [if_neg hy] at h
      by_cases h1 : y = 1
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h; cases h

/-- A halting pass needs an odd count of ones: the last block odd and the ones it crosses even. -/
theorem next_halt_odd (zs : List Nat) (hp : Pos zs) (h : next zs = .halt) : zs.sum % 2 = 1 := by
  match zs with
  | y :: ys =>
    have hps : Pos ys := fun z hz => hp z (by simp [hz])
    rw [next] at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy] at h; cases h
    rw [if_neg hy] at h
    have := sweep_halt_even ys _ hps h
    simp only [List.sum_cons]; omega

/-! ## The orbit from blank tape -/

theorem orbit_ok (n : Nat) (zs : List Nat) (h : orbit n = .ok zs) :
    zs.sum = 4 * n ∧ Pos zs ∧ ∃ t, n ≤ t ∧ steps t init = some ⟨enc zs, blank, .A⟩ := by
  induction n generalizing zs with
  | zero =>
    simp [orbit] at h; subst h
    exact ⟨rfl, by simp [Pos], 0, Nat.le_refl _, rfl⟩
  | succ n ih =>
    cases hn : orbit n with
    | ok ys =>
      simp only [orbit, hn] at h
      obtain ⟨hs, hp, t, ht, hr⟩ := ih ys hn
      obtain ⟨hs', hp'⟩ := next_sum ys zs hp h
      obtain ⟨k, hk⟩ := pass ys zs h
      exact ⟨by omega, hp', t + (k + 1), by omega, steps_seq trans hr hk⟩
    | halt => simp [orbit, hn] at h
    | one => simp [orbit, hn] at h

/-- Each pass start has 4 times its index in ones, so no pass halts. -/
theorem orbit_ne_halt (n : Nat) : orbit n ≠ .halt := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    intro h
    cases hn : orbit n with
    | ok zs =>
      simp only [orbit, hn] at h
      obtain ⟨hs, hp, _⟩ := orbit_ok n zs hn
      have := next_halt_odd zs hp h
      omega
    | halt => exact ih hn
    | one => simp [orbit, hn] at h

/-- **The reduction**: if the machine halts from blank tape, the closed form's orbit reaches a pass whose sweep stops
at a block of a single 1. -/
theorem halts_only_by_one (h : HaltsFromBlank) : ∃ n, orbit n = .one := by
  refine Classical.byContradiction fun hno => ?_
  have hok : ∀ n, ∃ zs, orbit n = .ok zs := by
    intro n
    cases hn : orbit n with
    | ok zs => exact ⟨zs, rfl⟩
    | halt => exact absurd hn (orbit_ne_halt n)
    | one => exact absurd ⟨n, hn⟩ hno
  have hall : ∀ m, ∃ c, steps m init = some c := by
    intro m
    obtain ⟨zs, hzs⟩ := hok m
    obtain ⟨_, _, t, ht, hr⟩ := orbit_ok m zs hzs
    have e : t = m + (t - m) := by omega
    rw [e] at hr
    exact steps_le trans hr
  exact not_halts_of_forall trans hall h

/-- The same, read forwards: if no pass of the closed form's orbit stops at a block of a single 1, the machine never
halts. -/
theorem never_halts_of_no_one (h : ∀ n, orbit n ≠ .one) : ¬ HaltsFromBlank :=
  fun hh => let ⟨n, hn⟩ := halts_only_by_one hh; h n hn

/-- The first pass starts, computed by the kernel. -/
theorem orbit_12 :
    orbit 12 = .ok [16, 25, 7] := by decide

end BB6d
