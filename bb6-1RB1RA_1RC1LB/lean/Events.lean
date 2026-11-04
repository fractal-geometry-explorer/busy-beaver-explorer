import Wave

/-!
# The event map: one step each time A stands on the blank right of the tape

`py/waves.py` follows the run from one *event* to the next: A on the blank just right of the last block,

  `E (x :: ls)  =  0^∞ 1^{l_r} 0 … 0 1^{l_1} 0 1^x A> 0^∞`      (`ls = [l_1, …, l_r]`, nearest first),

where the last block `x` may be empty.  The super step of `Wave.lean` is every fourth event.  This file proves the
single events from the machine, in closed form:

* `ev (x :: k :: ls)` with `q = x / 2`: for even `x` the next event is `(q + 2) :: (k + q + 1) :: ls`; for odd `x` a
  wave starts at `k` with value `k + q + 2`, and the next event is `q :: W` where `wave (k + q + 2) ls = some W`
  (`none`: the machine halts).  The function `wave` is the one of `Wave.lean`.
* `ev_sound`: from `E b` the machine reaches `E b'` if `ev b = some b'`, and halts if `ev b = none` (kernel-checked,
  every list with positive blocks left of the last).
* `ev4`: four events from `0 :: 5 :: L` are the super step, `0 :: 5 :: superL L`.
* `halts_iff_ev`: the machine halts from blank tape iff the event orbit from `[2, 1]` (step 17) reaches `none`, and
  `evOrbit_tape`: every list of that orbit is a tape of the run from blank tape.

The proof runs the macro step of `Macro.lean` from `X ls x []`, which reaches `E (x :: ls)` after `x` steps, until
the right part `cs` is empty again; `carry_ev` is `carry_wave` of `Wave.lean` with any right part.

`DeepMind.lean` shows that this is the high-level map `highLevelNext` of google-deepmind/cryptids.
-/

namespace BB6b

open TM

/-! ## Events -/

/-- The event tape: A on the blank right of the last block `x`, with the blocks `ls` further left (nearest first). -/
def E : List Nat → Config
  | [] => init
  | x :: ls => ⟨rep x [true] (cons false (lt ls)), blank, .A⟩

/-- **The event map**: the next event after `x :: k :: ls`, or `none` for a halt. -/
def ev : List Nat → Option (List Nat)
  | x :: k :: ls =>
    if x % 2 = 0 then some ((x / 2 + 2) :: (k + x / 2 + 1) :: ls)
    else (wave (k + x / 2 + 2) ls).map (x / 2 :: ·)
  | _ => none

/-- The events of the run: two blocks or more, every block but the last nonempty. -/
def GoodE : List Nat → Prop
  | _ :: k :: ls => 0 < k ∧ ∀ l ∈ ls, 0 < l
  | _ => False

/-- `j` events from `b`. -/
def evOrbit : Nat → List Nat → Option (List Nat)
  | 0, b => some b
  | j + 1, b => (ev b).bind (evOrbit j)

/-! Checks against `py/waves.py` (`python3 waves.py` prints the same events, left to right). -/

example : evOrbit 3 [2, 1] = some [0, 5, 6, 1] := by decide
example : evOrbit 7 [2, 1] = some [0, 5, 8, 7, 4] := by decide
example : evOrbit 11 [2, 1] = some [0, 5, 9, 8, 6, 3, 4, 1] := by decide

/-! ## The final sweep, as lists -/

/-- The sweep of `Macro.lean` on lists: the event it ends at, head first. -/
def sweepL : List Nat → Nat → List Nat → List Nat
  | ls, m, [] => m :: ls
  | ls, m, c :: cs => sweepL ((m + 2) :: ls) (c - 1) cs

/-- The event that the sweep over the right part `S` leaves, with the blocks `W` on its left. -/
def close : List Nat → List Nat → List Nat
  | [], W => W
  | s :: S, W => sweepL W (s - 1) S

theorem close_cons (s : Nat) (S W : List Nat) (hs : 0 < s) (h : S ≠ []) :
    close (s :: S) W = close S ((s + 1) :: W) := by
  match S, h with
  | t :: S, _ =>
    show sweepL ((s - 1 + 2) :: W) (t - 1) S = _
    rw [show s - 1 + 2 = s + 1 by omega]; rfl

theorem sweepL_close (ls : List Nat) (m : Nat) (S : List Nat) (h : S ≠ []) :
    sweepL ls m S = close S ((m + 2) :: ls) := by
  match S, h with
  | t :: S, _ => rfl

/-- Where a macro run is at an event: `X W z []` for the event `z :: W`. -/
def evRes : List Nat → Res
  | [] => .stuck
  | z :: W => .go W z []

theorem res_sweep : ∀ (cs ls : List Nat) (m : Nat), (∀ c ∈ cs, 0 < c) → res (sweep ls m cs) = evRes (sweepL ls m cs) := by
  intro cs
  induction cs with
  | nil => intro ls m _; rfl
  | cons c cs ih =>
    intro ls m h
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    show res ((sweep ((m + 2) :: ls) c cs).map (Out.addT (m + 3))) = _
    rw [res_map_addT, ih _ _ h.2]
    rfl

/-- The outcome `o` leads to the event `b` (`x = some b`) or to a halt (`x = none`). -/
def EndsE (o : Option Out) : Option (List Nat) → Prop
  | some b => ∃ a, (res o).run a = evRes b
  | none => ∃ a, (res o).run a = .halt

theorem endsE_map {a : Nat} {o : Option Out} {x : Option (List Nat)} : EndsE (o.map (Out.addT a)) x ↔ EndsE o x := by
  cases x <;> simp only [EndsE, res_map_addT]

theorem endsE_go {ls n cs t} {x : Option (List Nat)} (h : EndsE (next ls n cs) x) :
    EndsE (some (.go ls n cs t)) x := by
  cases x with
  | some W => obtain ⟨a, h⟩ := h; exact ⟨a + 1, h⟩
  | none => obtain ⟨a, h⟩ := h; exact ⟨a + 1, h⟩

theorem endsE_sweep (ls : List Nat) (m : Nat) (S : List Nat) (W : List Nat) (hS : ∀ c ∈ S, 0 < c)
    (h : sweepL ls m S = W) : EndsE (sweep ls m S) (some W) :=
  ⟨0, by rw [res_sweep S ls m hS, h]; rfl⟩

/-! ## The wave with any right part

`carry_wave` of `Wave.lean` with the right part `cs` arbitrary: the wave ends with a sweep over
`S = 1^e ++ bump cs` (as lists: `e` blocks of one, then `cs` with its first block one longer). -/

/-- The right part the final sweep runs over. -/
def rpart (e : Nat) (cs : List Nat) : List Nat := List.replicate e 1 ++ bump cs

theorem rpart_ne (e : Nat) (cs : List Nat) : rpart e cs ≠ [] := by
  simp [rpart, bump_ne]

theorem rpart_pos (e : Nat) (cs : List Nat) (h : ∀ c ∈ cs, 0 < c) : ∀ c ∈ rpart e cs, 0 < c :=
  replicate_pos e _ (bump_pos cs h)

theorem rpart_succ (e : Nat) (cs : List Nat) : rpart (e + 1) cs = 1 :: rpart e cs := by
  simp [rpart, List.replicate_succ]

theorem rpart_zero_cons (c : Nat) (S : List Nat) : rpart 0 (c :: S) = (c + 1) :: S := rfl

theorem carry_left_ev : ∀ (f d e : Nat) (cs : List Nat), 3 ≤ d → d ≤ f → (∀ c ∈ cs, 0 < c) →
    EndsE (carry [d - 2] e cs) ((leftEnd f d).map (close (rpart e cs))) := by
  intro f
  induction f with
  | zero => intro d e cs h₃ hf _; omega
  | succ f ih =>
    intro d e cs h₃ hf hc
    have hd : d = 3 ∨ d = 4 ∨ (d % 2 = 1 ∧ 5 ≤ d) ∨ (d % 2 = 0 ∧ 6 ≤ d) := by omega
    rcases hd with rfl | rfl | ⟨hd, hd'⟩ | ⟨hd, hd'⟩
    · -- d = 3: the carry meets a block of 1 and A sweeps right
      show EndsE ((sweep [1] 2 (rpart e cs)).map (Out.addT 15)) (some (close (rpart e cs) [4, 1]))
      rw [endsE_map]
      exact endsE_sweep _ _ _ _ (rpart_pos e cs hc) (sweepL_close _ _ _ (rpart_ne e cs))
    · -- d = 4: the carry eats the last block of 2 and the machine halts
      have h : leftEnd (f + 1) 4 = none := by rw [leftEnd_even f 4 (by omega) (by omega)]; rw [leftEnd_two]; rfl
      rw [h]
      exact ⟨0, rfl⟩
    · -- d odd: a new block at the left end, a transfer phase, and a sweep
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 5 := ⟨(d - 5) / 2, by omega⟩
      rw [leftEnd_odd f _ (by omega) hd, show 2 * j + 5 - 2 = 2 * j + 3 by omega,
        show (2 * j + 5 + 5) / 2 = j + 5 by omega, show (2 * j + 5 - 1) / 2 = j + 2 by omega]
      show EndsE (some (.go [1] (2 * j) (1 :: rpart e cs) _)) _
      apply endsE_go
      show EndsE ((exit [1 + 2 * j / 2] (2 * j % 2) (bumpBy (2 * j / 2) (1 :: rpart e cs))).map _) _
      rw [endsE_map, show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega]
      show EndsE ((sweep [1 + j + 1] (1 + j + 2) (rpart e cs)).map _) _
      rw [endsE_map]
      refine endsE_sweep _ _ _ _ (rpart_pos e cs hc) ?_
      rw [sweepL_close _ _ _ (rpart_ne e cs)]
      congr 2
      · omega
      · congr 1; omega
    · -- d even: a new block at the left end, a transfer phase, and the carry again with d / 2
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 6 := ⟨(d - 6) / 2, by omega⟩
      rw [leftEnd_even f _ (by omega) hd, show 2 * j + 6 - 2 = 2 * j + 1 + 3 by omega,
        show (2 * j + 6) / 2 = j + 3 by omega]
      show EndsE (some (.go [1] (2 * j + 1) (1 :: rpart e cs) _)) _
      apply endsE_go
      show EndsE ((exit [1 + (2 * j + 1) / 2] ((2 * j + 1) % 2) (bumpBy ((2 * j + 1) / 2) (1 :: rpart e cs))).map _) _
      rw [endsE_map, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]
      show EndsE ((carry [1 + j] 0 ((1 + j) :: rpart e cs)).map _) _
      rw [endsE_map]
      have hc' : ∀ c ∈ (1 + j) :: rpart e cs, 0 < c := by
        simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by omega, rpart_pos e cs hc⟩
      have h := ih (j + 3) 0 _ (by omega) (by omega) hc'
      rw [show j + 3 - 2 = 1 + j by omega] at h
      have hx : ((leftEnd f (j + 3)).map ((j + 3) :: ·)).map (close (rpart e cs))
          = (leftEnd f (j + 3)).map (close (rpart 0 ((1 + j) :: rpart e cs))) := by
        cases leftEnd f (j + 3) with
        | none => rfl
        | some W =>
          simp only [Option.map_some, rpart_zero_cons]
          rw [close_cons (1 + j + 1) _ _ (by omega) (rpart_ne e cs), show 1 + j + 1 + 1 = j + 3 by omega]
      rw [hx]
      exact h

/-- **The wave is what the macro run does**, for any right part: from a carry with value `d - 2` at the blocks `L`,
`e` blocks of 2 eaten and the right part `cs`, the macro run reaches the event `close (rpart e cs) W` where
`wave d L = some W`, or halts where `wave d L = none`. -/
theorem carry_ev : ∀ (L : List Nat) (d e : Nat) (cs : List Nat), 3 ≤ d → (∀ p ∈ L, 0 < p) → (∀ c ∈ cs, 0 < c) →
    EndsE (carry ((d - 2) :: L) e cs) ((wave d L).map (close (rpart e cs))) := by
  intro L
  induction L with
  | nil => intro d e cs h₃ _ hc; exact carry_left_ev d d e cs h₃ (Nat.le_refl d) hc
  | cons p L ih =>
    intro d e cs h₃ hL hc
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    obtain ⟨hp, hL⟩ := hL
    have hd : d = 3 ∨ d = 4 ∨ (d % 2 = 1 ∧ 5 ≤ d) ∨ (d % 2 = 0 ∧ 6 ≤ d) := by omega
    rcases hd with rfl | rfl | ⟨hd, hd'⟩ | ⟨hd, hd'⟩
    · -- d = 3: the carry meets a block of 1 and A sweeps right
      rw [wave_odd 3 p L (by decide)]
      show EndsE ((sweep ((p + 1) :: L) 2 (rpart e cs)).map (Out.addT 15)) _
      rw [endsE_map]
      exact endsE_sweep _ _ _ _ (rpart_pos e cs hc) (sweepL_close _ _ _ (rpart_ne e cs))
    · -- d = 4: the carry eats a block of 2 and goes on to `p`
      rw [wave_even 4 p L (by decide)]
      show EndsE ((carry (p :: L) (e + 1) cs).map (Out.addT 5)) _
      rw [endsE_map]
      have h := ih (p + 2) (e + 1) cs (by omega) hL hc
      rw [show p + 2 - 2 = p by omega] at h
      have hx : ((wave (p + 4 / 2) L).map (4 / 2 :: ·)).map (close (rpart e cs))
          = (wave (p + 2) L).map (close (rpart (e + 1) cs)) := by
        cases wave (p + 2) L with
        | none => rfl
        | some W => simp only [Option.map_some, rpart_succ, close_cons 1 _ _ (by decide) (rpart_ne e cs)]
      rw [hx]
      exact h
    · -- d odd: the head's block takes a transfer phase, then A sweeps right
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 5 := ⟨(d - 5) / 2, by omega⟩
      rw [wave_odd _ p L hd, show 2 * j + 5 - 2 = 2 * j + 3 by omega,
        show (2 * j + 5 + 5) / 2 = j + 5 by omega, show (2 * j + 5 - 1) / 2 = j + 2 by omega]
      show EndsE (some (.go ((p + 1) :: L) (2 * j) (1 :: rpart e cs) _)) _
      apply endsE_go
      show EndsE ((exit ((p + 1 + 2 * j / 2) :: L) (2 * j % 2) (bumpBy (2 * j / 2) (1 :: rpart e cs))).map _) _
      rw [endsE_map, show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega]
      show EndsE ((sweep ((p + 1 + j + 1) :: L) (1 + j + 2) (rpart e cs)).map _) _
      rw [endsE_map]
      refine endsE_sweep _ _ _ _ (rpart_pos e cs hc) ?_
      rw [sweepL_close _ _ _ (rpart_ne e cs)]
      congr 2
      · omega
      · congr 1; omega
    · -- d even: a transfer phase, and the carry goes on to `p` with `p + d / 2`
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 6 := ⟨(d - 6) / 2, by omega⟩
      rw [wave_even _ p L hd, show 2 * j + 6 - 2 = 2 * j + 1 + 3 by omega, show (2 * j + 6) / 2 = j + 3 by omega]
      show EndsE (some (.go ((p + 1) :: L) (2 * j + 1) (1 :: rpart e cs) _)) _
      apply endsE_go
      show EndsE ((exit ((p + 1 + (2 * j + 1) / 2) :: L) ((2 * j + 1) % 2)
        (bumpBy ((2 * j + 1) / 2) (1 :: rpart e cs))).map _) _
      rw [endsE_map, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]
      show EndsE ((carry ((p + 1 + j) :: L) 0 ((1 + j) :: rpart e cs)).map _) _
      rw [endsE_map]
      have hc' : ∀ c ∈ (1 + j) :: rpart e cs, 0 < c := by
        simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by omega, rpart_pos e cs hc⟩
      have h := ih (p + (j + 3)) 0 _ (by omega) hL hc'
      rw [show p + (j + 3) - 2 = p + 1 + j by omega] at h
      have hx : ((wave (p + (j + 3)) L).map ((j + 3) :: ·)).map (close (rpart e cs))
          = (wave (p + (j + 3)) L).map (close (rpart 0 ((1 + j) :: rpart e cs))) := by
        cases wave (p + (j + 3)) L with
        | none => rfl
        | some W =>
          simp only [Option.map_some, rpart_zero_cons]
          rw [close_cons (1 + j + 1) _ _ (by omega) (rpart_ne e cs), show 1 + j + 1 + 1 = j + 3 by omega]
      rw [hx]
      exact h

/-! ## One event, by the macro step -/

/-- **One event, as lists**: the macro run from `X (k :: ls) x []` reaches the event `ev (x :: k :: ls)`, or halts
where it is `none`. -/
theorem next_ev (x k : Nat) (ls : List Nat) (hk : 0 < k) (hl : ∀ l ∈ ls, 0 < l) :
    EndsE (next (k :: ls) x []) (ev (x :: k :: ls)) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ x = r + 2 * q := ⟨x / 2, x % 2, Nat.mod_lt _ (by decide), by omega⟩
  have h₁ : (r + 2 * q) % 2 = r := by omega
  have h₂ : (r + 2 * q) / 2 = q := by omega
  show EndsE ((exit ((k + (r + 2 * q) / 2) :: ls) ((r + 2 * q) % 2) (bumpBy ((r + 2 * q) / 2) [])).map _) _
  rw [endsE_map]
  simp only [ev, h₁, h₂]
  have hb : bump (bumpBy q []) = [q + 1] := by
    cases q with
    | zero => rfl
    | succ q => simp [bumpBy, bump]
  match r, hr with
  | 0, _ =>
        cases q with
    | zero => exact ⟨0, rfl⟩
    | succ q =>
      show EndsE ((sweep (bump ((k + (q + 1)) :: ls)) (q + 1 + 2) []).map (Out.addT 15)) _
      rw [endsE_map]
      exact ⟨0, by
        show Res.go ((k + (q + 1) + 1) :: ls) (q + 1 + 2) [] = Res.go ((k + (q + 1) + 1) :: ls) (q + 1 + 2) []
        rfl⟩
  | 1, _ =>
    simp only [Nat.one_ne_zero, ite_false]
    show EndsE ((carry ((k + q) :: ls) 0 (bumpBy q [])).map (Out.addT 6)) _
    rw [endsE_map]
    have hc : ∀ c ∈ bumpBy q [], 0 < c := bumpBy_pos q [] (by simp)
    have h := carry_ev ls (k + q + 2) 0 (bumpBy q []) (by omega) hl hc
    rw [show k + q + 2 - 2 = k + q by omega] at h
    have hx : (wave (k + q + 2) ls).map (close (rpart 0 (bumpBy q [])))
        = (wave (k + q + 2) ls).map (q :: ·) := by
      cases wave (k + q + 2) ls with
      | none => rfl
      | some W => simp only [Option.map_some, rpart, List.replicate_zero, List.nil_append, hb]; rfl
    rw [hx] at h
    exact h

/-! ## The event map is sound for the machine -/

theorem steps_add : ∀ (a b : Nat) (c : Config), steps (a + b) c = (steps a c).bind (steps b) := by
  intro a
  induction a with
  | zero => intro b c; simp
  | succ a ih =>
    intro b c
    rw [show a + 1 + b = (a + b) + 1 by omega]
    cases hs : step c with
    | none => simp [steps, TM.steps, hs]
    | some d =>
      show TM.steps trans (a + b + 1) c = (TM.steps trans (a + 1) c).bind (TM.steps trans b)
      rw [steps_succ_of_step trans (a + b) hs, steps_succ_of_step trans a hs]
      exact ih b d

/-- A run that passes `c₁` after `a` steps and `c₂` after `b ≥ a` steps goes from `c₁` to `c₂`. -/
theorem steps_sub {a b : Nat} {c c₁ c₂ : Config} (h₁ : steps a c = some c₁) (h₂ : steps b c = some c₂)
    (h : a ≤ b) : steps (b - a) c₁ = some c₂ := by
  rw [show b = a + (b - a) by omega, steps_add, h₁] at h₂
  exact h₂

/-- What a time-free macro run says about the machine. -/
theorem run_sound : ∀ (a : Nat) (ls : List Nat) (n : Nat) (cs : List Nat),
    (∀ ls' n' cs', (Res.go ls n cs).run a = .go ls' n' cs' → ∃ t, steps t (X ls n cs) = some (X ls' n' cs')) ∧
    ((Res.go ls n cs).run a = .halt → Halts trans (X ls n cs)) := by
  intro a
  induction a with
  | zero =>
    intro ls n cs
    refine ⟨fun ls' n' cs' h => ?_, fun h => by cases h⟩
    cases h
    exact ⟨0, rfl⟩
  | succ a ih =>
    intro ls n cs
    show (∀ ls' n' cs', (res (next ls n cs)).run a = .go ls' n' cs' → _) ∧ ((res (next ls n cs)).run a = .halt → _)
    cases e : next ls n cs with
    | none =>
      refine ⟨fun _ _ _ h => ?_, fun h => ?_⟩ <;> simp [res, Res.run_stuck] at h
    | some o =>
      have ho := next_sound ls n cs o e
      cases o with
      | halt t =>
        refine ⟨fun _ _ _ h => ?_, fun _ => ?_⟩
        · simp [res, Out.res, Res.run_halt] at h
        obtain ⟨c', h₁, h₂⟩ := ho
        exact ⟨t, c', h₁, h₂⟩
      | go ls₁ n₁ cs₁ t =>
        simp only [res, Out.res]
        obtain ⟨ih₁, ih₂⟩ := ih ls₁ n₁ cs₁
        refine ⟨fun ls' n' cs' h => ?_, fun h => ?_⟩
        · obtain ⟨t', h'⟩ := ih₁ ls' n' cs' h
          exact ⟨t + t', steps_seq trans ho h'⟩
        · obtain ⟨t', c', h₁, h₂⟩ := ih₂ h
          exact ⟨t + t', c', steps_seq trans ho h₁, h₂⟩

/-- `X ls x []` reaches the event `E (x :: ls)` in `x` steps: A runs over the block. -/
theorem X_E (ls : List Nat) (x : Nat) : steps x (X ls x []) = some (E (x :: ls)) := by
  have h := a_sweep x (cons false (lt ls)) blank
  simp only [X, rt, cons_false_blank]
  exact h

/-- Every outcome of `next ls x []` comes at least `x` steps after `X ls x []`. -/
def Out.t : Out → Nat
  | .go _ _ _ t => t
  | .halt t => t

theorem Out.t_addT (a : Nat) (o : Out) : (o.addT a).t = a + o.t := by cases o <;> rfl

theorem next_t (k : Nat) (ls : List Nat) (x : Nat) (o : Out) (h : next (k :: ls) x [] = some o) : x ≤ o.t := by
  simp only [next] at h
  cases e : exit ((k + x / 2) :: ls) (x % 2) (bumpBy (x / 2) []) with
  | none => rw [e] at h; cases h
  | some o' =>
    rw [e] at h
    cases h
    rw [Out.t_addT]
    have hq : 2 * (x / 2) ≤ tsteps (x % 2) (x / 2) := by
      simp only [tsteps]
      rw [Nat.mul_comm 2]
      exact Nat.mul_le_mul_left _ (by omega)
    have hr : x % 2 = 1 → 1 ≤ o'.t := by
      intro hx
      rw [hx] at e
      simp only [exit] at e
      cases e' : carry ((k + x / 2) :: ls) 0 (bumpBy (x / 2) []) with
      | none => rw [e'] at e; cases e
      | some o'' => rw [e'] at e; cases e; rw [Out.t_addT]; omega
    by_cases hx : x % 2 = 1
    · have := hr hx; omega
    · omega

theorem ev_good (b b' : List Nat) (hb : GoodE b) (h : ev b = some b') : GoodE b' := by
  match b, hb with
  | x :: k :: ls, ⟨hk, hl⟩ =>
    simp only [ev] at h
    split at h
    · cases h; exact ⟨by omega, hl⟩
    · cases e : wave (k + x / 2 + 2) ls with
      | none => rw [e] at h; cases h
      | some W =>
        rw [e] at h
        cases h
        obtain ⟨hne, hW⟩ := wave_good ls _ W (by omega) hl e
        match W, hne with
        | w :: W, _ =>
          simp only [List.mem_cons, forall_eq_or_imp] at hW
          exact hW

/-- **The event map is sound**: from the event `E b` the machine reaches the event `E b'` if `ev b = some b'`, and
halts if `ev b = none`. -/
theorem ev_sound (b : List Nat) (hb : GoodE b) :
    (∀ b', ev b = some b' → ∃ t, steps t (E b) = some (E b')) ∧ (ev b = none → Halts trans (E b)) := by
  match b, hb with
  | x :: k :: ls, ⟨hk, hl⟩ =>
    have hE := next_ev x k ls hk hl
    obtain ⟨o, e, _⟩ := next_fine (k :: ls) x [] ⟨by simp, by simp [hk]; exact hl, by simp⟩
    have hs := next_sound (k :: ls) x [] o e
    have ht := next_t k ls x o e
    have hX := X_E (k :: ls) x
    rw [e] at hE
    constructor
    · intro b' hb'
      rw [hb'] at hE
      obtain ⟨a, ha⟩ := hE
      cases o with
      | halt t => simp only [res, Out.res, Res.run_halt] at ha; cases b' <;> cases ha
      | go ls₁ n₁ cs₁ t =>
        match b', ha with
        | [], _ => exact absurd (ev_good (x :: k :: ls) _ ⟨hk, hl⟩ hb') id
        | z :: W, ha =>
          simp only [res, Out.res, evRes] at ha
          obtain ⟨t', h'⟩ := (run_sound a ls₁ n₁ cs₁).1 W z [] ha
          have h₁ := steps_sub hX hs ht
          exact ⟨t - x + (t' + z), steps_seq trans h₁ (steps_seq trans h' (X_E W z))⟩
    · intro hn
      rw [hn] at hE
      obtain ⟨a, ha⟩ := hE
      cases o with
      | halt t =>
        obtain ⟨c', h₁, h₂⟩ := hs
        exact ⟨t - x, c', steps_sub hX h₁ ht, h₂⟩
      | go ls₁ n₁ cs₁ t =>
        simp only [res, Out.res] at ha
        obtain ⟨t', c', h₁, h₂⟩ := (run_sound a ls₁ n₁ cs₁).2 ha
        exact ⟨t - x + t', c', steps_seq trans (steps_sub hX hs ht) h₁, h₂⟩

/-! ## Four events are the super step -/

/-- **Four events make a super step**: from `0 :: 5 :: L` (the tape `X (5 :: L) 0 []`), the event map reaches
`0 :: 5 :: W` in four events if `superL L = some W`, and halts if `superL L = none`. -/
theorem ev4 (p : Nat) (L : List Nat) : evOrbit 4 (0 :: 5 :: p :: L) = (superL (p :: L)).map (0 :: 5 :: ·) := by
  have h₁ : ev (0 :: 5 :: p :: L) = some (2 :: 6 :: p :: L) := rfl
  have h₂ : ev (2 :: 6 :: p :: L) = some (3 :: 8 :: p :: L) := rfl
  have h₃ : ev (3 :: 8 :: p :: L) = some (1 :: 8 :: (p + 5) :: L) := by
    show (wave 11 (p :: L)).map (1 :: ·) = _
    rw [wave_odd 11 p L (by decide)]
    rfl
  have h₄ : ev (1 :: 8 :: (p + 5) :: L) = (superL (p :: L)).map (0 :: 5 :: ·) := by
    show (wave 10 ((p + 5) :: L)).map (0 :: ·) = (wave (p + 10) L).map (0 :: 5 :: ·)
    rw [wave_even 10 (p + 5) L (by decide), show p + 5 + 10 / 2 = p + 10 by omega]
    cases wave (p + 10) L <;> rfl
  simp only [evOrbit, h₁, h₂, h₃, h₄, Option.bind_some]
  cases superL (p :: L) <;> rfl

theorem evOrbit_add : ∀ (a b : Nat) (x : List Nat), evOrbit (a + b) x = (evOrbit a x).bind (evOrbit b) := by
  intro a
  induction a with
  | zero => intro b x; simp [evOrbit]
  | succ a ih =>
    intro b x
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [evOrbit]
    cases ev x with
    | none => rfl
    | some y => exact ih b y

theorem orbit_good : ∀ (j : Nat) (L W : List Nat), GoodL L → orbit j L = some W → GoodL W := by
  intro j
  induction j with
  | zero => intro L W hL h; cases h; exact hL
  | succ j ih =>
    intro L W hL h
    simp only [orbit] at h
    cases e : superL L with
    | none => rw [e] at h; cases h
    | some W' => rw [e] at h; exact ih W' W (superL_good L W' hL e) h

/-- `4 j` events from `0 :: 5 :: L` are `j` super steps. -/
theorem evOrbit_orbit : ∀ (j : Nat) (L : List Nat), GoodL L →
    evOrbit (4 * j) (0 :: 5 :: L) = (orbit j L).map (0 :: 5 :: ·) := by
  intro j
  induction j with
  | zero => intro L _; rfl
  | succ j ih =>
    intro L hL
    match L, hL with
    | p :: L', hL =>
      rw [show 4 * (j + 1) = 4 + 4 * j by omega, evOrbit_add, ev4]
      simp only [orbit]
      cases e : superL (p :: L') with
      | none => rfl
      | some W => exact ih W (superL_good _ W hL e)

/-! ## Halting, by events -/

/-- From step 17 the run is at the event `[2, 1]` (`0^∞ 1 0 1 1 A> 0^∞`). -/
theorem init_E : steps 17 init = some (E [2, 1]) :=
  steps_seq trans init_X (X_E [1] 2)

/-- The event orbit from `[2, 1]` reaches the super step's start after three events. -/
theorem evOrbit_start : evOrbit 3 [2, 1] = some [0, 5, 6, 1] := by decide

theorem evOrbit_none (a b : Nat) (x : List Nat) (h : evOrbit a x = none) (hab : a ≤ b) : evOrbit b x = none := by
  rw [show b = a + (b - a) by omega, evOrbit_add, h]; rfl

/-- **The machine halts from blank tape iff the event orbit from `[2, 1]` halts.** -/
theorem halts_iff_ev : HaltsFromBlank ↔ ∃ j, evOrbit j [2, 1] = none := by
  have hg : GoodL [6, 1] := ⟨by simp, by simp⟩
  have key : (∃ j, evOrbit j [2, 1] = none) ↔ ∃ j, orbit j [6, 1] = none := by
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have h := evOrbit_none j (3 + 4 * j) _ hj (by omega)
      rw [evOrbit_add, evOrbit_start, Option.bind_some, evOrbit_orbit j _ hg] at h
      cases e : orbit j [6, 1] with
      | none => rfl
      | some W => rw [e] at h; cases h
    · rintro ⟨j, hj⟩
      exact ⟨3 + 4 * j, by rw [evOrbit_add, evOrbit_start, Option.bind_some, evOrbit_orbit j _ hg, hj]; rfl⟩
  rw [key, halts_iff_pow2]
  constructor
  · rintro ⟨j, W, h₁, h₂⟩
    refine ⟨j + 1, ?_⟩
    have hW := orbit_good j _ W hg h₁
    have h₁' : orbit (j + 1) [6, 1] = (orbit j [6, 1]).bind superL := by
      clear h₁ h₂ hW
      generalize [6, 1] = L
      induction j generalizing L with
      | zero => simp [orbit]
      | succ j ih =>
        simp only [orbit]
        cases superL L with
        | none => rfl
        | some W => exact ih W
    rw [h₁', h₁, Option.bind_some, (superL_none_iff W hW).2 h₂]
  · rintro ⟨j, hj⟩
    induction j with
    | zero => cases hj
    | succ j ih =>
      by_cases h : orbit j [6, 1] = none
      · exact ih h
      · obtain ⟨W, hW⟩ := Option.ne_none_iff_exists'.1 h
        have h₁' : orbit (j + 1) [6, 1] = (orbit j [6, 1]).bind superL := by
          clear hj ih h hW
          generalize [6, 1] = L
          induction j generalizing L with
          | zero => simp [orbit]
          | succ j ih =>
            simp only [orbit]
            cases superL L with
            | none => rfl
            | some W => exact ih W
        rw [h₁', hW, Option.bind_some] at hj
        exact ⟨j, W, hW, (superL_none_iff W (orbit_good j _ W hg hW)).1 hj⟩

/-- **The events occur**: every list of the event orbit from `[2, 1]` is a tape of the run from blank tape. -/
theorem evOrbit_tape (j : Nat) (b : List Nat) (h : evOrbit j [2, 1] = some b) : ∃ t, steps t init = some (E b) := by
  have key : ∀ (j : Nat) (x b : List Nat), GoodE x → evOrbit j x = some b →
      GoodE b ∧ ∃ t, steps t (E x) = some (E b) := by
    intro j
    induction j with
    | zero => intro x b hx h; cases h; exact ⟨hx, 0, rfl⟩
    | succ j ih =>
      intro x b hx h
      simp only [evOrbit] at h
      cases e : ev x with
      | none => rw [e] at h; cases h
      | some y =>
        rw [e] at h
        obtain ⟨t₁, h₁⟩ := (ev_sound x hx).1 y e
        obtain ⟨hb, t₂, h₂⟩ := ih y b (ev_good x y hx e) h
        exact ⟨hb, t₁ + t₂, steps_seq trans h₁ h₂⟩
  obtain ⟨_, t, ht⟩ := key j [2, 1] b ⟨by decide, by simp⟩ h
  exact ⟨17 + t, steps_seq trans init_E ht⟩

end BB6b
