import Rules

/-!
# The macro step: the machine as a map on lists of block lengths

From step 15 on, the run from blank tape passes through configurations

  `X ls n cs  =  0^∞ 1^{l_r} 0 … 0 1^{l_1} 0 A> 1^n 0 0 0 1^{c_1} 0 0 1^{c_2} … 0 0 1^{c_s} 0^∞`

with `ls = [l_1, …, l_r]` the blocks to the left of the head, nearest first, separated by single 0s, `n` the block
under the head, and `cs = [c_1, …, c_s]` the blocks to the right, separated by `00` (and by `000` from the head's
block).  `next ls n cs` is one macro step, computed on the lists:

* `n / 2` transfers (`transfers`, from the rule `transfer`): each moves two cells of the head's block, one to `l_1` and
  one to `c_1` (a new block `1` if `cs` is empty);
* then, with `n` even, `l_1` gains one and A sweeps right to the end of the tape (`empty_start`, `sweep`): every `00`
  becomes `0`, the first block gains four cells and the others one, and the last block becomes the head's block;
* with `n` odd, F carries to the left (`carry_start`, `carry`): every block equal to 2 it meets turns into a `001` on
  the right; at the first block `k ≠ 2` it stops, with `k ≥ 3` starting a new transfer phase on `k - 3` and `k = 1`
  starting a sweep; **if every block to the left is 2, it reaches the left end and the machine halts.**

`next_sound` says the machine really does this, with the step counts `next` gives (kernel-checked, every case and every
block length).  `halts_iff` turns the question into one about the lists: the machine halts from blank tape iff the
macro run `runM` reaches a halt, and `next_halt_iff` says when a macro step halts.
-/

namespace BB6b

open TM

/-- Blocks to the left of the head, nearest first, each followed (outward) by a 0. -/
def lt : List Nat → Tape
  | [] => blank
  | l :: ls => rep l [true] (cons false (lt ls))

/-- Blocks to the right of the head's `000`, separated by `00`. -/
def rt : List Nat → Tape
  | [] => blank
  | c :: cs => rep c [true] (cons false (cons false (rt cs)))

/-- The macro configuration: A at the start of the block `1^n`, which has `ls` to its left and `000` then `cs` to its
right. -/
def X (ls : List Nat) (n : Nat) (cs : List Nat) : Config :=
  ⟨cons false (lt ls), rep n [true] (cons false (cons false (cons false (rt cs)))), .A⟩

/-- A during the sweep to the right: at the start of `1^m`, followed by `00` and the blocks `cs`. -/
def W (ls : List Nat) (m : Nat) (cs : List Nat) : Config :=
  ⟨cons false (lt ls), rep m [true] (cons false (cons false (rt cs))), .A⟩

/-- F during the carry to the left: `L 0 1^m F> 1 Q`. -/
def D (m : Nat) (L Q : Tape) : Config := ⟨rep m [true] (cons false L), cons true Q, .F⟩

/-- The first block gains one; an empty list gets a new block `1`. -/
def bump : List Nat → List Nat
  | [] => [1]
  | c :: cs => (c + 1) :: cs

/-- `q` times `bump`: the first block gains `q`. -/
def bumpBy (q : Nat) : List Nat → List Nat
  | [] => if q = 0 then [] else [q]
  | c :: cs => (c + q) :: cs

theorem bumpBy_zero (cs : List Nat) : bumpBy 0 cs = cs := by
  cases cs <;> simp [bumpBy]

theorem bumpBy_succ (q : Nat) (cs : List Nat) : bumpBy (q + 1) cs = bumpBy q (bump cs) := by
  cases cs with
  | nil => simp only [bumpBy, bump]; simp; omega
  | cons c cs => simp only [bumpBy, bump]; congr 1; omega

theorem cons_true_lt (ls : List Nat) : cons true (lt ls) = lt (bump ls) := by
  cases ls with
  | nil => show cons true blank = cons true (cons false blank); rw [cons_false_blank]
  | cons l ls => rfl

theorem cons_true_rt (cs : List Nat) : cons true (rt cs) = rt (bump cs) := by
  cases cs with
  | nil => show cons true blank = cons true (cons false (cons false blank)); rw [cons_false_blank, cons_false_blank]
  | cons c cs => rfl

/-! ## The outcome of a macro step -/

/-- Where a macro step ends: at `X ls n cs` after `t` steps, or at a halting configuration after `t` steps. -/
inductive Out where
  | go (ls : List Nat) (n : Nat) (cs : List Nat) (t : Nat)
  | halt (t : Nat)
  deriving DecidableEq, Repr

/-- The machine does what `o` says, starting from `c`. -/
def Out.Sound (c : Config) : Out → Prop
  | .go ls n cs t => steps t c = some (X ls n cs)
  | .halt t => ∃ c', steps t c = some c' ∧ step c' = none

/-- `a` more steps in front. -/
def Out.addT (a : Nat) : Out → Out
  | .go ls n cs t => .go ls n cs (a + t)
  | .halt t => .halt (a + t)

theorem Out.sound_addT {a : Nat} {c c' : Config} (h : steps a c = some c') {o : Out} (ho : o.Sound c') :
    (o.addT a).Sound c := by
  cases o with
  | go ls n cs t => exact steps_seq trans h ho
  | halt t =>
    obtain ⟨d, h₁, h₂⟩ := ho
    exact ⟨d, steps_seq trans h h₁, h₂⟩

theorem Out.sound_map {a : Nat} {c c' : Config} (h : steps a c = some c') {x : Option Out}
    (hx : ∀ o, x = some o → o.Sound c') : ∀ o, x.map (Out.addT a) = some o → o.Sound c := by
  intro o ho
  cases x with
  | none => cases ho
  | some o' =>
    cases ho
    exact Out.sound_addT h (hx o' rfl)

/-! ## Transfers -/

/-- Steps of `q` transfers that end with `n` cells in the head's block: the transfer from `n + 2j + 2` takes
`2 (n + 2j) + 11` steps, and these add up to `q (2n + 2q + 9)`. -/
def tsteps (n q : Nat) : Nat := q * (2 * n + 2 * q + 9)

theorem tsteps_succ (n q : Nat) : tsteps n (q + 1) = (2 * (n + 2 * q) + 11) + tsteps n q := by
  simp only [tsteps, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem transfers (n : Nat) (ls : List Nat) :
    ∀ (q k : Nat) (cs : List Nat),
      steps (tsteps n q) (X (k :: ls) (n + 2 * q) cs) = some (X ((k + q) :: ls) n (bumpBy q cs)) := by
  intro q
  induction q with
  | zero => intro k cs; simp only [tsteps, bumpBy_zero, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]; rfl
  | succ q ih =>
    intro k cs
    have h₁ : steps (2 * (n + 2 * q) + 11) (X (k :: ls) (n + 2 * (q + 1)) cs)
        = some (X ((k + 1) :: ls) (n + 2 * q) (bump cs)) := by
      have e : n + 2 * (q + 1) = (n + 2 * q) + 2 := by omega
      rw [e]
      have h := transfer (n + 2 * q) (lt (k :: ls)) (rt cs)
      rw [cons_true_rt] at h
      exact h
    have h₂ := ih (k + 1) (bump cs)
    rw [show k + 1 + q = k + (q + 1) by omega, ← bumpBy_succ] at h₂
    rw [tsteps_succ]
    exact steps_seq trans h₁ h₂

/-! ## The sweep to the right -/

/-- The sweep: each block `c` of `cs` costs `m + 3` steps; the last one becomes the head's block. -/
def sweep : List Nat → Nat → List Nat → Option Out
  | ls, m, [] => some (.go ls m [] 0)
  | _, _, 0 :: _ => none
  | ls, m, (c + 1) :: cs => (sweep ((m + 2) :: ls) c cs).map (Out.addT (m + 3))

theorem W_nil (ls : List Nat) (m : Nat) : W ls m [] = X ls m [] := by
  simp only [W, X, rt, cons_false_blank]

theorem sweep_sound : ∀ (cs ls : List Nat) (m : Nat) (o : Out), sweep ls m cs = some o → o.Sound (W ls m cs) := by
  intro cs
  induction cs with
  | nil =>
    intro ls m o h
    cases h
    show steps 0 (W ls m []) = some (X ls m [])
    rw [W_nil]; rfl
  | cons c cs ih =>
    intro ls m o h
    cases c with
    | zero => cases h
    | succ c =>
      exact Out.sound_map (sweep_step m (cons false (lt ls)) (rep c [true] (cons false (cons false (rt cs)))))
        (ih ((m + 2) :: ls) c) o h

/-! ## The carry to the left -/

/-- What the carry leaves on the right after passing `e` blocks of 2: `0 0 (1 0 0)^e 1 R`. -/
def Qt (e : Nat) (cs : List Nat) : Tape := cons false (cons false (rt (List.replicate e 1 ++ bump cs)))

/-- The carry, from `D 0 (lt ls) (Qt e cs)`: F to the right of the 0 after the block `l_1`. -/
def carry : List Nat → Nat → List Nat → Option Out
  | [], _, _ => some (.halt 6)
  | 0 :: _, _, _ => none
  | 1 :: ls, e, cs => (sweep (bump ls) 2 (List.replicate e 1 ++ bump cs)).map (Out.addT 15)
  | 2 :: ls, e, cs => (carry ls (e + 1) cs).map (Out.addT 5)
  | (k + 3) :: ls, e, cs => some (.go (bump ls) k (List.replicate (e + 1) 1 ++ bump cs) (k + 9))

/-- At the left end the carry halts: F, B, C, D, E, C, then D reads a 0. -/
theorem carry_halt (Q : Tape) : ∃ c', steps 6 (D 0 blank Q) = some c' ∧ step c' = none :=
  ⟨_, rfl, rfl⟩

theorem carry_sound : ∀ (ls : List Nat) (e : Nat) (cs : List Nat) (o : Out),
    carry ls e cs = some o → o.Sound (D 0 (lt ls) (Qt e cs)) := by
  intro ls
  induction ls with
  | nil =>
    intro e cs o h
    cases h
    exact carry_halt _
  | cons l ls ih =>
    intro e cs o h
    match l, h with
    | 1, h =>
      have h₁ : steps 15 (D 0 (lt (1 :: ls)) (Qt e cs)) = some (W (bump ls) 2 (List.replicate e 1 ++ bump cs)) := by
        have h := carry_one (lt ls) (Qt e cs)
        rw [cons_true_lt] at h
        exact h
      exact Out.sound_map h₁ (sweep_sound _ _ _) o h
    | 2, h =>
      have h₁ : steps 5 (D 0 (lt (2 :: ls)) (Qt e cs)) = some (D 0 (lt ls) (Qt (e + 1) cs)) :=
        carry_two 0 (lt ls) (Qt e cs)
      exact Out.sound_map h₁ (ih (e + 1) cs) o h
    | k + 3, h =>
      cases h
      have h₁ := carry_two (k + 1) (lt ls) (Qt e cs)
      have h₂ := carry_exit k (lt ls) (cons false (cons false (cons true (Qt e cs))))
      rw [cons_true_lt] at h₂
      have h₃ := steps_seq trans h₁ h₂
      rw [show 5 + (k + 4) = k + 9 by omega] at h₃
      exact h₃

/-! ## One macro step -/

/-- After the transfers: the head's block is empty (`0`) or has one cell (`1`). -/
def exit : List Nat → Nat → List Nat → Option Out
  | ls, 0, [] => some (.go (bump ls) 2 [] 15)
  | ls, 0, c :: cs => (sweep (bump ls) (c + 2) cs).map (Out.addT 15)
  | ls, 1, cs => (carry ls 0 cs).map (Out.addT 6)
  | _, _, _ => none

theorem exit_sound : ∀ (ls : List Nat) (n : Nat) (cs : List Nat) (o : Out),
    exit ls n cs = some o → o.Sound (X ls n cs) := by
  intro ls n cs o h
  match n, cs, h with
  | 0, [], h =>
    cases h
    show steps 15 (X ls 0 []) = some (X (bump ls) 2 [])
    have h := empty_start (lt ls) blank
    rw [cons_true_lt] at h
    simp only [X, rt, rep_succ, rep_zero, app_cons, app_nil, cons_false_blank] at h ⊢
    exact h
  | 0, c :: cs, h =>
    have h₁ : steps 15 (X ls 0 (c :: cs)) = some (W (bump ls) (c + 2) cs) := by
      have h := empty_start (lt ls) (rt (c :: cs))
      rw [cons_true_lt] at h
      exact h
    exact Out.sound_map h₁ (sweep_sound _ _ _) o h
  | 1, cs, h =>
    have h₁ : steps 6 (X ls 1 cs) = some (D 0 (lt ls) (Qt 0 cs)) := by
      have h := carry_start (lt ls) (rt cs)
      rw [cons_true_rt] at h
      exact h
    exact Out.sound_map h₁ (carry_sound _ _ _) o h

/-- One macro step from `X ls n cs`. -/
def next : List Nat → Nat → List Nat → Option Out
  | [], _, _ => none
  | k :: ls, n, cs => (exit ((k + n / 2) :: ls) (n % 2) (bumpBy (n / 2) cs)).map (Out.addT (tsteps (n % 2) (n / 2)))

/-- **The macro step is sound**: the machine goes from `X ls n cs` where `next` says, in the number of steps it
says, or halts where it says. -/
theorem next_sound (ls : List Nat) (n : Nat) (cs : List Nat) (o : Out) (h : next ls n cs = some o) :
    o.Sound (X ls n cs) := by
  match ls, h with
  | [], h => cases h
  | k :: ls, h =>
    have h₁ := transfers (n % 2) ls (n / 2) k cs
    rw [Nat.mod_add_div] at h₁
    exact Out.sound_map h₁ (exit_sound _ _ _) o h

/-! ## The macro run from blank tape -/

/-- `m` macro steps from `o` (tail recursive, for long runs by evaluation). A halt stays a halt. -/
def runFrom : Nat → Out → Option Out
  | 0, o => some o
  | _ + 1, .halt t => some (.halt t)
  | m + 1, .go ls n cs t =>
    match next ls n cs with
    | none => none
    | some o => runFrom m (o.addT t)

/-- The first macro configuration: `0^∞ 1 0 A> 1 1 0^∞` after 15 steps. -/
theorem init_X : steps 15 init = some (X [1] 2 []) := by
  have h := blank_reaches trans (n := 15) (q := St.A) (c := ⟨[false, true], [true, true], .A⟩) (by decide)
  rw [show (⟨[false, true], [true, true], .A⟩ : FCfg St).toCfg = X [1] 2 [] by
    simp only [FCfg.toCfg, X, lt, rt, app_cons, app_nil, rep_succ, rep_zero, cons_false_blank]] at h
  exact h

/-- The macro run from blank tape: where it is after `m` macro steps. -/
def runM (m : Nat) : Option Out := runFrom m (.go [1] 2 [] 15)

theorem runFrom_sound : ∀ (m : Nat) (o o' : Out), o.Sound init → runFrom m o = some o' → o'.Sound init := by
  intro m
  induction m with
  | zero => intro o o' ho h; cases h; exact ho
  | succ m ih =>
    intro o o' ho h
    cases o with
    | halt t => cases h; exact ho
    | go ls n cs t =>
      simp only [runFrom] at h
      cases e : next ls n cs with
      | none => rw [e] at h; cases h
      | some o₁ =>
        rw [e] at h
        exact ih _ _ (Out.sound_addT ho (next_sound ls n cs o₁ e)) h

/-- **The macro run is the machine's run**: after `m` macro steps the machine is at the macro configuration (or the
halt) that `runM m` gives, after the number of steps it gives. -/
theorem runM_sound (m : Nat) (o : Out) (h : runM m = some o) : o.Sound init :=
  runFrom_sound m (.go [1] 2 [] 15) o init_X h

/-! ## When a macro step halts -/

theorem sweep_not_halt : ∀ (cs ls : List Nat) (m t : Nat), sweep ls m cs ≠ some (.halt t) := by
  intro cs
  induction cs with
  | nil => intro ls m t h; cases h
  | cons c cs ih =>
    intro ls m t h
    cases c with
    | zero => cases h
    | succ c =>
      simp only [sweep] at h
      cases e : sweep ((m + 2) :: ls) c cs with
      | none => rw [e] at h; cases h
      | some o =>
        rw [e] at h
        cases o with
        | go => cases h
        | halt t' => exact ih _ _ _ e

theorem carry_halt_iff : ∀ (ls : List Nat) (e : Nat) (cs : List Nat),
    (∃ t, carry ls e cs = some (.halt t)) ↔ ∀ l ∈ ls, l = 2 := by
  intro ls
  induction ls with
  | nil => intro e cs; simp [carry]
  | cons l ls ih =>
    intro e cs
    match l with
    | 0 => simp [carry]
    | 1 =>
      simp only [carry, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨t, h⟩
        cases e' : sweep (bump ls) 2 (List.replicate e 1 ++ bump cs) with
        | none => rw [e'] at h; cases h
        | some o =>
          rw [e'] at h
          cases o with
          | go => cases h
          | halt t' => exact absurd e' (sweep_not_halt _ _ _ _)
      · rintro ⟨h, _⟩; cases h
    | 2 =>
      simp only [carry, List.mem_cons, forall_eq_or_imp, true_and]
      rw [← ih (e + 1) cs]
      constructor
      · rintro ⟨t, h⟩
        cases e' : carry ls (e + 1) cs with
        | none => rw [e'] at h; cases h
        | some o =>
          rw [e'] at h
          cases o with
          | go => cases h
          | halt t' => exact ⟨t', rfl⟩
      · rintro ⟨t, h⟩; exact ⟨5 + t, by rw [h]; rfl⟩
    | k + 3 => simp [carry]

/-- **When the machine halts**: a macro step from `X (k :: ls) n cs` halts iff `n` is odd and, after the transfers
(which add `n / 2` to `k`), every block to the left of the head is 2. -/
theorem next_halt_iff (k : Nat) (ls : List Nat) (n : Nat) (cs : List Nat) :
    (∃ t, next (k :: ls) n cs = some (.halt t)) ↔ n % 2 = 1 ∧ ∀ l ∈ (k + n / 2) :: ls, l = 2 := by
  simp only [next]
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn
  · rw [hn]
    simp only [Nat.zero_ne_one, false_and, iff_false]
    rintro ⟨t, h⟩
    cases e : bumpBy (n / 2) cs with
    | nil => rw [e] at h; simp [exit, Out.addT] at h
    | cons c cs' =>
      rw [e] at h
      simp only [exit] at h
      cases e' : sweep (bump ((k + n / 2) :: ls)) (c + 2) cs' with
      | none => rw [e'] at h; cases h
      | some o =>
        rw [e'] at h
        cases o with
        | go => cases h
        | halt t' => exact absurd e' (sweep_not_halt _ _ _ _)
  · rw [hn]
    simp only [true_and]
    rw [← carry_halt_iff _ 0 (bumpBy (n / 2) cs)]
    simp only [exit]
    constructor
    · rintro ⟨t, h⟩
      cases e : carry ((k + n / 2) :: ls) 0 (bumpBy (n / 2) cs) with
      | none => rw [e] at h; cases h
      | some o =>
        rw [e] at h
        cases o with
        | go => cases h
        | halt t' => exact ⟨t', rfl⟩
    · rintro ⟨t, h⟩; exact ⟨_, by rw [h]; rfl⟩

/-! ## Halting is a question about the lists

Every macro configuration the run reaches has a block to the left and no empty blocks, so `next` never gets stuck,
and every macro step takes at least one machine step.  Hence the machine halts iff the macro run does.
-/

/-- The macro configurations of the run: a block to the left, no empty blocks. -/
def Good (ls : List Nat) (cs : List Nat) : Prop := ls ≠ [] ∧ (∀ l ∈ ls, 0 < l) ∧ (∀ c ∈ cs, 0 < c)

/-- `o` ends at a good macro configuration (or halts). -/
def Out.Good : Out → Prop
  | .go ls _ cs _ => BB6b.Good ls cs
  | .halt _ => True

/-- `o` ends at a good macro configuration after at least one step (or halts). -/
def Out.Fine : Out → Prop
  | .go ls _ cs t => BB6b.Good ls cs ∧ 0 < t
  | .halt _ => True

theorem Out.good_addT (a : Nat) {o : Out} (h : o.Good) : (o.addT a).Good := by
  cases o <;> exact h

theorem Out.fine_addT (a : Nat) {o : Out} (h : o.Fine) : (o.addT a).Fine := by
  cases o with
  | halt t => trivial
  | go ls n cs t => exact ⟨h.1, show 0 < a + t by have := h.2; omega⟩

theorem Out.fine_of_good {a : Nat} (ha : 0 < a) {o : Out} (h : o.Good) : (o.addT a).Fine := by
  cases o with
  | halt t => trivial
  | go ls n cs t => exact ⟨h, show 0 < a + t by omega⟩

theorem bump_pos (cs : List Nat) (h : ∀ c ∈ cs, 0 < c) : ∀ c ∈ bump cs, 0 < c := by
  cases cs with
  | nil => simp [bump]
  | cons c cs =>
    simp only [bump, List.mem_cons, forall_eq_or_imp] at h ⊢
    exact ⟨by omega, h.2⟩

theorem bump_ne (cs : List Nat) : bump cs ≠ [] := by cases cs <;> simp [bump]

theorem bumpBy_pos (q : Nat) (cs : List Nat) (h : ∀ c ∈ cs, 0 < c) : ∀ c ∈ bumpBy q cs, 0 < c := by
  cases cs with
  | nil =>
    simp only [bumpBy]
    split
    · simp
    · simp only [List.mem_singleton, forall_eq]; omega
  | cons c cs =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [bumpBy, List.mem_cons, forall_eq_or_imp]
    exact ⟨by omega, h.2⟩

theorem replicate_pos (e : Nat) (cs : List Nat) (h : ∀ c ∈ cs, 0 < c) :
    ∀ c ∈ List.replicate e 1 ++ cs, 0 < c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · rw [(List.mem_replicate.1 hc).2]; decide
  · exact h c hc

theorem sweep_good : ∀ (cs ls : List Nat) (m : Nat), ls ≠ [] → (∀ l ∈ ls, 0 < l) → (∀ c ∈ cs, 0 < c) →
    ∃ o, sweep ls m cs = some o ∧ o.Good := by
  intro cs
  induction cs with
  | nil => intro ls m h₁ h₂ _; exact ⟨_, rfl, h₁, h₂, by simp⟩
  | cons c cs ih =>
    intro ls m h₁ h₂ h₃
    simp only [List.mem_cons, forall_eq_or_imp] at h₃
    match c, h₃ with
    | c + 1, h₃ =>
      have hl : ∀ l ∈ (m + 2) :: ls, 0 < l := by
        simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by omega, h₂⟩
      obtain ⟨o, e, ho⟩ := ih ((m + 2) :: ls) c (by simp) hl h₃.2
      exact ⟨_, by simp only [sweep, e]; rfl, Out.good_addT _ ho⟩

theorem carry_good : ∀ (ls : List Nat) (e : Nat) (cs : List Nat), (∀ l ∈ ls, 0 < l) → (∀ c ∈ cs, 0 < c) →
    ∃ o, carry ls e cs = some o ∧ o.Good := by
  intro ls
  induction ls with
  | nil => intro e cs _ _; exact ⟨_, rfl, trivial⟩
  | cons l ls ih =>
    intro e cs h₁ h₂
    simp only [List.mem_cons, forall_eq_or_imp] at h₁
    have hb : ∀ l ∈ bump ls, 0 < l := bump_pos ls h₁.2
    match l, h₁ with
    | 1, _ =>
      obtain ⟨o, e', ho⟩ :=
        sweep_good (List.replicate e 1 ++ bump cs) (bump ls) 2 (bump_ne ls) hb (replicate_pos e _ (bump_pos cs h₂))
      exact ⟨_, by simp only [carry, e']; rfl, Out.good_addT _ ho⟩
    | 2, h₁ =>
      obtain ⟨o, e', ho⟩ := ih (e + 1) cs h₁.2 h₂
      exact ⟨_, by simp only [carry, e']; rfl, Out.good_addT _ ho⟩
    | k + 3, _ =>
      exact ⟨_, rfl, bump_ne ls, hb, replicate_pos (e + 1) _ (bump_pos cs h₂)⟩

/-- From a good macro configuration the macro step is defined, takes at least one step, and ends at a good one or
halts. -/
theorem next_fine (ls : List Nat) (n : Nat) (cs : List Nat) (h : Good ls cs) :
    ∃ o, next ls n cs = some o ∧ o.Fine := by
  obtain ⟨hne, h₁, h₂⟩ := h
  match ls, hne, h₁ with
  | k :: ls, _, h₁ =>
    simp only [List.mem_cons, forall_eq_or_imp] at h₁
    have hl : ∀ l ∈ (k + n / 2) :: ls, 0 < l := by
      simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by omega, h₁.2⟩
    have hc := bumpBy_pos (n / 2) cs h₂
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    simp only [next]
    rcases hn with hn | hn <;> rw [hn]
    · have hb : ∀ l ∈ bump ((k + n / 2) :: ls), 0 < l := bump_pos _ hl
      cases e : bumpBy (n / 2) cs with
      | nil =>
        exact ⟨_, rfl, Out.fine_addT _ (o := .go _ 2 [] 15) ⟨⟨bump_ne _, hb, by simp⟩, by decide⟩⟩
      | cons c cs' =>
        rw [e] at hc
        simp only [List.mem_cons, forall_eq_or_imp] at hc
        obtain ⟨o, e', ho⟩ := sweep_good cs' _ (c + 2) (bump_ne _) hb hc.2
        exact ⟨_, by simp only [exit, e']; rfl, Out.fine_addT _ (Out.fine_of_good (by decide) ho)⟩
    · obtain ⟨o, e, ho⟩ := carry_good _ 0 _ hl hc
      exact ⟨_, by simp only [exit, e]; rfl, Out.fine_addT _ (Out.fine_of_good (by decide) ho)⟩

/-- One macro step on an outcome (a halt stays). -/
def Out.next : Out → Option Out
  | .go ls n cs t => (BB6b.next ls n cs).map (Out.addT t)
  | .halt t => some (.halt t)

theorem runFrom_succ : ∀ (m : Nat) (o : Out), runFrom (m + 1) o = (runFrom m o).bind Out.next := by
  intro m
  induction m with
  | zero =>
    intro o
    cases o with
    | halt t => rfl
    | go ls n cs t =>
      simp only [runFrom, Out.next, Option.bind_some]
      cases next ls n cs <;> rfl
  | succ m ih =>
    intro o
    cases o with
    | halt t => simp only [runFrom, Option.bind_some, Out.next]
    | go ls n cs t =>
      simp only [runFrom]
      cases next ls n cs with
      | none => rfl
      | some o' => exact ih _

/-- Along a run that never halts, every macro step is defined and the step count grows by at least one. -/
theorem runM_go (hnh : ∀ m t, runM m ≠ some (.halt t)) :
    ∀ m, ∃ ls n cs t, runM m = some (.go ls n cs t) ∧ Good ls cs ∧ m ≤ t := by
  intro m
  induction m with
  | zero => exact ⟨[1], 2, [], 15, rfl, ⟨by simp, by simp, by simp⟩, by omega⟩
  | succ m ih =>
    obtain ⟨ls, n, cs, t, e, hg, hle⟩ := ih
    obtain ⟨o, e', ho⟩ := next_fine ls n cs hg
    have hr : runM (m + 1) = some (o.addT t) := by
      simp only [runM] at e ⊢
      rw [runFrom_succ, e]
      simp only [Option.bind_some, Out.next, e']
      rfl
    cases o with
    | halt t' => exact absurd hr (hnh (m + 1) (t + t'))
    | go ls' n' cs' t' => exact ⟨ls', n', cs', t + t', hr, ho.1, by have := ho.2; omega⟩

/-- **The machine halts from blank tape iff the macro run halts.** -/
theorem halts_iff : HaltsFromBlank ↔ ∃ m t, runM m = some (.halt t) := by
  constructor
  · intro h
    refine Classical.byContradiction fun hnh => ?_
    have hnh' : ∀ m t, runM m ≠ some (.halt t) := fun m t e => hnh ⟨m, t, e⟩
    apply not_halts_of_forall trans _ h
    intro N
    obtain ⟨ls, n, cs, t, e, _, hle⟩ := runM_go hnh' N
    have hs : steps t init = some (X ls n cs) := runM_sound N _ e
    rw [show t = N + (t - N) by omega] at hs
    exact steps_le trans hs
  · rintro ⟨m, t, e⟩
    obtain ⟨c', h₁, h₂⟩ := runM_sound m _ e
    exact ⟨t, c', h₁, h₂⟩

end BB6b
