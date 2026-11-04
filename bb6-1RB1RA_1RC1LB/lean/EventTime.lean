import Events
import WaveTime

/-!
# The single events with their step counts

`Events.lean` proves the event map `ev`: each time A stands on the blank right of the tape, the next such tape
follows in closed form (`ev_sound`), but the proof only says that the machine gets there, not in how many steps.
`WaveTime.lean` counts the steps of a whole super step (four events).  This file counts the steps of each event.

With the last block `x`, the one before it `k`, the blocks `ls` further left and `q = x / 2`:

* an even `x` takes `2q² + 8q + 17` steps (`q` transfers, an empty start and the run over the new last block);
* an odd `x` takes `2q² + 9q + 5` steps to start the wave at `k` with value `d = k + q + 2`, then the wave's own time
  `waveTimeE d ls (q + 3)`: `2r² + r − 5` for each block passed with an even value `2r` (`evenT`), and where it turns
  at an odd value `d = 2r + 1`, `2r² + 4r + 11 + B` (`oddE`), with `B` the cost of the sweep back to the right end:
  it starts at `q + 3` and grows by `r + 1` for each block passed.  At the left end the wave goes on with `p = 0` and a
  halt there takes 11 steps.

`evT` is this count and `ev_steps` proves it for every event: from `E b` the machine reaches `E b'` in exactly `evT b`
steps if `ev b = some b'`, and halts after exactly `evT b` steps (the next transition is the halting one) if
`ev b = none` (kernel-checked, every list with positive blocks left of the last).  `ev4_time`: the four events of a
super step add up to `superT` of `WaveTime.lean`.  `evOrbitT_steps`: the event orbit with times is the machine's run,
step for step (from blank tape the events come at steps 17, 44, 101, 136, …).

The proof follows `carry_ev` of `Events.lean` once more with the times of the macro steps (`next_sound`); the time
of the final sweep over the right part `S`, plus the run over the new last block, is `m + Σ (s + 2)` over `S`
(`sweep_reachE`), whatever `S` is, which is why `B` is a plain sum here.
-/

namespace BB6b

open TM

/-! ## The times -/

/-- The cost of the final sweep over the right part `S` (each block `s` costs `s + 2`). -/
def cost (S : List Nat) : Nat := (S.map (· + 2)).sum

/-- Steps from a block with odd value `d` to the next event: `2q² + 4q + 11 + B` with `q = d / 2`, `B` the cost of
the right part the wave has left. -/
def oddE (d B : Nat) : Nat := 2 * (d / 2) * (d / 2) + 4 * (d / 2) + 11 + B

/-- The time of the wave at the left end, with fuel `f` (as `leftEnd`): the halt at `d = 4` takes 11 steps. -/
def leftTimeE : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, d, B =>
    if d % 2 = 1 then oddE d B
    else if d = 4 then 11
    else evenT d + leftTimeE f (d / 2) (B + d / 2 + 1)

/-- The time of `wave d L` to the next event, with `B` the cost of the right part. -/
def waveTimeE : Nat → List Nat → Nat → Nat
  | d, [], B => leftTimeE d d B
  | d, p :: L, B => if d % 2 = 1 then oddE d B else evenT d + waveTimeE (p + d / 2) L (B + d / 2 + 1)

/-- **The steps of one event** `x :: k :: ls`, with `q = x / 2`. -/
def evT : List Nat → Nat
  | x :: k :: ls =>
    if x % 2 = 0 then 2 * (x / 2) * (x / 2) + 8 * (x / 2) + 17
    else 2 * (x / 2) * (x / 2) + 9 * (x / 2) + 5 + waveTimeE (k + x / 2 + 2) ls (x / 2 + 3)
  | _ => 0

theorem leftTimeE_odd (f d B : Nat) (h : d % 2 = 1) : leftTimeE (f + 1) d B = oddE d B := by
  rw [leftTimeE, ite_eq_left h]

theorem leftTimeE_even (f d B : Nat) (h : d % 2 = 0) (h₄ : d ≠ 4) :
    leftTimeE (f + 1) d B = evenT d + leftTimeE f (d / 2) (B + d / 2 + 1) := by
  rw [leftTimeE, ite_eq_right (by omega), ite_eq_right h₄]

theorem waveTimeE_odd (d p : Nat) (L : List Nat) (B : Nat) (h : d % 2 = 1) : waveTimeE d (p :: L) B = oddE d B := by
  rw [waveTimeE, ite_eq_left h]

theorem waveTimeE_even (d p : Nat) (L : List Nat) (B : Nat) (h : d % 2 = 0) :
    waveTimeE d (p :: L) B = evenT d + waveTimeE (p + d / 2) L (B + d / 2 + 1) := by
  rw [waveTimeE, ite_eq_right (by omega)]

/-! ## Reaching an event, with the time -/

/-- The macro run from `o` reaches the event `b` (as the macro configuration `X W z []` for `b = z :: W`) and then
the event tape itself after `t` steps in all (`x = some b`), or halts after `t` steps (`x = none`). -/
def ReachE (o : Option Out) : Option (List Nat) → Nat → Prop
  | some b, t => ∃ W z T, b = z :: W ∧ Reach o (.go W z [] T) ∧ T + z = t
  | none, t => Reach o (.halt t)

theorem reachE_cast {o : Option Out} {x x' : Option (List Nat)} {t t' : Nat} (h : ReachE o x t) (hx : x = x')
    (ht : t = t') : ReachE o x' t' := hx ▸ ht ▸ h

theorem reachE_map {k : Nat} {o : Option Out} {x : Option (List Nat)} {t : Nat} (h : ReachE o x t) :
    ReachE (o.map (Out.addT k)) x (k + t) := by
  cases x with
  | some b =>
    obtain ⟨W, z, T, hb, hr, ht⟩ := h
    exact ⟨W, z, k + T, hb, reach_map hr, by omega⟩
  | none => exact reach_map (o' := .halt t) h

theorem reachE_go {ls n cs s} {x : Option (List Nat)} {t : Nat} (h : ReachE (next ls n cs) x t) :
    ReachE (some (.go ls n cs s)) x (s + t) := by
  cases x with
  | some b =>
    obtain ⟨W, z, T, hb, hr, ht⟩ := h
    exact ⟨W, z, s + T, hb, reach_go hr, by omega⟩
  | none => exact reach_go (o' := .halt t) h

/-- **The sweep, timed**: the sweep over `S` and then the run over the new last block take `m + cost S` steps. -/
theorem sweep_reachE : ∀ (S ls : List Nat) (m : Nat), (∀ c ∈ S, 0 < c) →
    ReachE (sweep ls m S) (some (sweepL ls m S)) (m + cost S) := by
  intro S
  induction S with
  | nil => intro ls m _; exact ⟨ls, m, 0, rfl, reach_eq rfl, by simp [cost]⟩
  | cons c S ih =>
    intro ls m h
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have h' := reachE_map (k := m + 3) (ih ((m + 2) :: ls) c h.2)
    show ReachE ((sweep ((m + 2) :: ls) c S).map (Out.addT (m + 3))) (some (sweepL ((m + 2) :: ls) (c + 1 - 1) S)) _
    rw [show c + 1 - 1 = c by omega]
    refine reachE_cast h' rfl ?_
    simp only [cost, List.map_cons, List.sum_cons]
    omega

theorem cost_rpart_succ (e : Nat) (cs : List Nat) : cost (rpart (e + 1) cs) = cost (rpart e cs) + 4 / 2 + 1 := by
  simp only [rpart_succ, cost, List.map_cons, List.sum_cons]
  omega

theorem cost_rpart_zero_cons (j : Nat) (S : List Nat) :
    cost (rpart 0 ((1 + j) :: S)) = cost S + (2 * j + 6) / 2 + 1 := by
  simp only [rpart_zero_cons, cost, List.map_cons, List.sum_cons]
  omega

/-! ## The wave, timed, with any right part -/

theorem carry_left_reachE : ∀ (f d e : Nat) (cs : List Nat), 3 ≤ d → d ≤ f → (∀ c ∈ cs, 0 < c) →
    ReachE (carry [d - 2] e cs) ((leftEnd f d).map (close (rpart e cs))) (leftTimeE f d (cost (rpart e cs))) := by
  intro f
  induction f with
  | zero => intro d e cs h₃ hf _; omega
  | succ f ih =>
    intro d e cs h₃ hf hc
    have hd : d = 3 ∨ d = 4 ∨ (d % 2 = 1 ∧ 5 ≤ d) ∨ (d % 2 = 0 ∧ 6 ≤ d) := by omega
    rcases hd with rfl | rfl | ⟨hd, hd'⟩ | ⟨hd, hd'⟩
    · -- d = 3: the carry meets a block of 1 and A sweeps right
      rw [leftEnd_odd f 3 (by omega) (by decide), leftTimeE_odd f 3 _ (by decide)]
      show ReachE ((sweep [1] 2 (rpart e cs)).map (Out.addT 15)) _ _
      have h := reachE_map (k := 15) (sweep_reachE (rpart e cs) [1] 2 (rpart_pos e cs hc))
      refine reachE_cast h ?_ ?_
      · rw [sweepL_close _ _ _ (rpart_ne e cs)]; rfl
      · simp only [oddE]; omega
    · -- d = 4: the carry eats the last block of 2 and the machine halts
      have h : leftEnd (f + 1) 4 = none := by rw [leftEnd_even f 4 (by omega) (by omega)]; rw [leftEnd_two]; rfl
      rw [h]
      exact reach_eq rfl
    · -- d odd: a new block at the left end, a transfer phase, and a sweep
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 5 := ⟨(d - 5) / 2, by omega⟩
      rw [leftEnd_odd f _ (by omega) hd, leftTimeE_odd f _ _ hd, show 2 * j + 5 - 2 = 2 * j + 3 by omega,
        show (2 * j + 5 + 5) / 2 = j + 5 by omega, show (2 * j + 5 - 1) / 2 = j + 2 by omega]
      show ReachE (some (.go [1] (2 * j) (1 :: rpart e cs) (2 * j + 9))) _ _
      have h₁ : next [1] (2 * j) (1 :: rpart e cs)
          = ((sweep [1 + j + 1] (1 + j + 2) (rpart e cs)).map (Out.addT 15)).map (Out.addT (tsteps 0 j)) := by
        show (exit [1 + 2 * j / 2] (2 * j % 2) (bumpBy (2 * j / 2) (1 :: rpart e cs))).map _ = _
        rw [show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega]
        rfl
      have h₂ := reachE_map (k := tsteps 0 j)
        (reachE_map (k := 15) (sweep_reachE (rpart e cs) [1 + j + 1] (1 + j + 2) (rpart_pos e cs hc)))
      rw [← h₁] at h₂
      refine reachE_cast (reachE_go (s := 2 * j + 9) h₂) ?_ ?_
      · rw [sweepL_close _ _ _ (rpart_ne e cs), show 1 + j + 2 + 2 = j + 5 by omega, show 1 + j + 1 = j + 2 by omega]
        rfl
      · simp only [oddE, tsteps]
        rw [show (2 * j + 5) / 2 = j + 2 by omega]
        simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
        omega
    · -- d even: a new block at the left end, a transfer phase, and the carry again with d / 2
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 6 := ⟨(d - 6) / 2, by omega⟩
      rw [leftEnd_even f _ (by omega) hd, leftTimeE_even f _ _ hd (by omega), show 2 * j + 6 - 2 = 2 * j + 1 + 3 by omega,
        show (2 * j + 6) / 2 = j + 3 by omega]
      show ReachE (some (.go [1] (2 * j + 1) (1 :: rpart e cs) (2 * j + 1 + 9))) _ _
      have h₁ : next [1] (2 * j + 1) (1 :: rpart e cs)
          = ((carry [1 + j] 0 ((1 + j) :: rpart e cs)).map (Out.addT 6)).map (Out.addT (tsteps 1 j)) := by
        show (exit [1 + (2 * j + 1) / 2] ((2 * j + 1) % 2) (bumpBy ((2 * j + 1) / 2) (1 :: rpart e cs))).map _ = _
        rw [show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]
        rfl
      have hc' : ∀ c ∈ (1 + j) :: rpart e cs, 0 < c := by
        simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by omega, rpart_pos e cs hc⟩
      have h := ih (j + 3) 0 _ (by omega) (by omega) hc'
      rw [show j + 3 - 2 = 1 + j by omega] at h
      have h₂ := reachE_map (k := tsteps 1 j) (reachE_map (k := 6) h)
      rw [← h₁] at h₂
      refine reachE_cast (reachE_go (s := 2 * j + 1 + 9) h₂) ?_ ?_
      · cases leftEnd f (j + 3) with
        | none => rfl
        | some W =>
          simp only [Option.map_some, rpart_zero_cons]
          rw [close_cons (1 + j + 1) _ _ (by omega) (rpart_ne e cs), show 1 + j + 1 + 1 = j + 3 by omega]
      · rw [cost_rpart_zero_cons, show (2 * j + 6) / 2 = j + 3 by omega]
        simp only [evenT, tsteps]
        rw [show (2 * j + 6) / 2 = j + 3 by omega]
        simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
        omega

/-- **The wave, timed, for any right part**: from a carry with value `d - 2` at the blocks `L`, `e` blocks of 2 eaten
and the right part `cs`, the machine reaches the event `close (rpart e cs) W` where `wave d L = some W`, or halts
where `wave d L = none`, after `waveTimeE d L (cost (rpart e cs))` steps. -/
theorem carry_reachE : ∀ (L : List Nat) (d e : Nat) (cs : List Nat), 3 ≤ d → (∀ p ∈ L, 0 < p) →
    (∀ c ∈ cs, 0 < c) →
    ReachE (carry ((d - 2) :: L) e cs) ((wave d L).map (close (rpart e cs))) (waveTimeE d L (cost (rpart e cs))) := by
  intro L
  induction L with
  | nil => intro d e cs h₃ _ hc; exact carry_left_reachE d d e cs h₃ (Nat.le_refl d) hc
  | cons p L ih =>
    intro d e cs h₃ hL hc
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    obtain ⟨hp, hL⟩ := hL
    have hd : d = 3 ∨ d = 4 ∨ (d % 2 = 1 ∧ 5 ≤ d) ∨ (d % 2 = 0 ∧ 6 ≤ d) := by omega
    rcases hd with rfl | rfl | ⟨hd, hd'⟩ | ⟨hd, hd'⟩
    · -- d = 3: the carry meets a block of 1 and A sweeps right
      rw [wave_odd 3 p L (by decide), waveTimeE_odd 3 p L _ (by decide)]
      show ReachE ((sweep ((p + 1) :: L) 2 (rpart e cs)).map (Out.addT 15)) _ _
      have h := reachE_map (k := 15) (sweep_reachE (rpart e cs) ((p + 1) :: L) 2 (rpart_pos e cs hc))
      refine reachE_cast h ?_ ?_
      · rw [sweepL_close _ _ _ (rpart_ne e cs)]; rfl
      · simp only [oddE]; omega
    · -- d = 4: the carry eats a block of 2 and goes on to `p`
      rw [wave_even 4 p L (by decide), waveTimeE_even 4 p L _ (by decide)]
      show ReachE ((carry (p :: L) (e + 1) cs).map (Out.addT 5)) _ _
      have h := ih (p + 2) (e + 1) cs (by omega) hL hc
      rw [show p + 2 - 2 = p by omega] at h
      refine reachE_cast (reachE_map (k := 5) h) ?_ ?_
      · cases wave (p + 2) L with
        | none => rfl
        | some W => simp only [Option.map_some, rpart_succ, close_cons 1 _ _ (by decide) (rpart_ne e cs)]
      · rw [cost_rpart_succ]; rfl
    · -- d odd: the head's block takes a transfer phase, then A sweeps right
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 5 := ⟨(d - 5) / 2, by omega⟩
      rw [wave_odd _ p L hd, waveTimeE_odd _ p L _ hd, show 2 * j + 5 - 2 = 2 * j + 3 by omega,
        show (2 * j + 5 + 5) / 2 = j + 5 by omega, show (2 * j + 5 - 1) / 2 = j + 2 by omega]
      show ReachE (some (.go ((p + 1) :: L) (2 * j) (1 :: rpart e cs) (2 * j + 9))) _ _
      have h₁ : next ((p + 1) :: L) (2 * j) (1 :: rpart e cs)
          = ((sweep ((p + 1 + j + 1) :: L) (1 + j + 2) (rpart e cs)).map (Out.addT 15)).map
            (Out.addT (tsteps 0 j)) := by
        show (exit ((p + 1 + 2 * j / 2) :: L) (2 * j % 2) (bumpBy (2 * j / 2) (1 :: rpart e cs))).map _ = _
        rw [show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega]
        rfl
      have h₂ := reachE_map (k := tsteps 0 j)
        (reachE_map (k := 15) (sweep_reachE (rpart e cs) ((p + 1 + j + 1) :: L) (1 + j + 2) (rpart_pos e cs hc)))
      rw [← h₁] at h₂
      refine reachE_cast (reachE_go (s := 2 * j + 9) h₂) ?_ ?_
      · rw [sweepL_close _ _ _ (rpart_ne e cs), show 1 + j + 2 + 2 = j + 5 by omega,
          show p + 1 + j + 1 = p + (j + 2) by omega]
        rfl
      · simp only [oddE, tsteps]
        rw [show (2 * j + 5) / 2 = j + 2 by omega]
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm]
        omega
    · -- d even: a transfer phase, and the carry goes on to `p` with `p + d / 2`
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 6 := ⟨(d - 6) / 2, by omega⟩
      rw [wave_even _ p L hd, waveTimeE_even _ p L _ hd, show 2 * j + 6 - 2 = 2 * j + 1 + 3 by omega,
        show (2 * j + 6) / 2 = j + 3 by omega]
      show ReachE (some (.go ((p + 1) :: L) (2 * j + 1) (1 :: rpart e cs) (2 * j + 1 + 9))) _ _
      have h₁ : next ((p + 1) :: L) (2 * j + 1) (1 :: rpart e cs)
          = ((carry ((p + 1 + j) :: L) 0 ((1 + j) :: rpart e cs)).map (Out.addT 6)).map (Out.addT (tsteps 1 j)) := by
        show (exit ((p + 1 + (2 * j + 1) / 2) :: L) ((2 * j + 1) % 2)
          (bumpBy ((2 * j + 1) / 2) (1 :: rpart e cs))).map _ = _
        rw [show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]
        rfl
      have hc' : ∀ c ∈ (1 + j) :: rpart e cs, 0 < c := by
        simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by omega, rpart_pos e cs hc⟩
      have h := ih (p + (j + 3)) 0 _ (by omega) hL hc'
      rw [show p + (j + 3) - 2 = p + 1 + j by omega] at h
      have h₂ := reachE_map (k := tsteps 1 j) (reachE_map (k := 6) h)
      rw [← h₁] at h₂
      refine reachE_cast (reachE_go (s := 2 * j + 1 + 9) h₂) ?_ ?_
      · cases wave (p + (j + 3)) L with
        | none => rfl
        | some W =>
          simp only [Option.map_some, rpart_zero_cons]
          rw [close_cons (1 + j + 1) _ _ (by omega) (rpart_ne e cs), show 1 + j + 1 + 1 = j + 3 by omega]
      · rw [cost_rpart_zero_cons, show (2 * j + 6) / 2 = j + 3 by omega]
        simp only [evenT, tsteps]
        rw [show (2 * j + 6) / 2 = j + 3 by omega]
        simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
        omega

/-! ## One event, timed -/

/-- **One event, timed, as lists**: the macro run from `X (k :: ls) x []` (which is `x` steps before the event
`E (x :: k :: ls)`) reaches the next event `ev (x :: k :: ls)` after `x + evT (x :: k :: ls)` steps, or halts then. -/
theorem next_reachE (x k : Nat) (ls : List Nat) (hk : 0 < k) (hl : ∀ l ∈ ls, 0 < l) :
    ReachE (next (k :: ls) x []) (ev (x :: k :: ls)) (x + evT (x :: k :: ls)) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ x = r + 2 * q := ⟨x / 2, x % 2, Nat.mod_lt _ (by decide), by omega⟩
  have h₁ : (r + 2 * q) % 2 = r := by omega
  have h₂ : (r + 2 * q) / 2 = q := by omega
  show ReachE ((exit ((k + (r + 2 * q) / 2) :: ls) ((r + 2 * q) % 2) (bumpBy ((r + 2 * q) / 2) [])).map
    (Out.addT (tsteps ((r + 2 * q) % 2) ((r + 2 * q) / 2)))) _ _
  simp only [ev, evT, h₁, h₂]
  match r, hr with
  | 0, _ =>
    simp only [ite_true]
    cases q with
    | zero => exact ⟨_, 2, 15, rfl, reach_eq rfl, rfl⟩
    | succ q =>
      refine ⟨(k + (q + 1) + 1) :: ls, q + 1 + 2, tsteps 0 (q + 1) + 15, rfl, reach_eq rfl, ?_⟩
      simp only [tsteps]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm]
      omega
  | 1, _ =>
    simp only [Nat.one_ne_zero, ite_false]
    show ReachE (((carry ((k + q) :: ls) 0 (bumpBy q [])).map (Out.addT 6)).map (Out.addT (tsteps 1 q))) _ _
    have hb : bump (bumpBy q []) = [q + 1] := by
      cases q with
      | zero => rfl
      | succ q => simp [bumpBy, bump]
    have hc : ∀ c ∈ bumpBy q [], 0 < c := bumpBy_pos q [] (by simp)
    have h := carry_reachE ls (k + q + 2) 0 (bumpBy q []) (by omega) hl hc
    rw [show k + q + 2 - 2 = k + q by omega] at h
    have hS : rpart 0 (bumpBy q []) = [q + 1] := by
      simp only [rpart, List.replicate_zero, List.nil_append, hb]
    rw [hS] at h
    refine reachE_cast (reachE_map (k := tsteps 1 q) (reachE_map (k := 6) h)) ?_ ?_
    · cases wave (k + q + 2) ls with
      | none => rfl
      | some W => rfl
    · simp only [cost, tsteps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [show q + 1 + 2 + 0 = q + 3 by omega]
      simp only [Nat.mul_add, Nat.mul_comm]
      omega

/-! ## The event map with its step counts is sound for the machine -/

/-- **The step count of one event**: from the event `E b` the machine reaches the event `E b'` in exactly `evT b`
steps if `ev b = some b'`, and halts after exactly `evT b` steps (the next transition is the halting one) if
`ev b = none`. -/
theorem ev_steps (b : List Nat) (hb : GoodE b) :
    (∀ b', ev b = some b' → steps (evT b) (E b) = some (E b')) ∧
    (ev b = none → ∃ c', steps (evT b) (E b) = some c' ∧ step c' = none) := by
  match b, hb with
  | x :: k :: ls, ⟨hk, hl⟩ =>
    have hR := next_reachE x k ls hk hl
    have hX := X_E (k :: ls) x
    constructor
    · intro b' hb'
      rw [hb'] at hR
      obtain ⟨W, z, T, rfl, hr, ht⟩ := hR
      have hs : steps T (X (k :: ls) x []) = some (X W z []) := reach_sound (next_sound _ _ _) hr
      have h₂ := steps_seq trans hs (X_E W z)
      rw [ht] at h₂
      have h := steps_sub hX h₂ (by omega)
      rwa [Nat.add_sub_cancel_left] at h
    · intro hn
      rw [hn] at hR
      obtain ⟨c', h₁, h₂⟩ := reach_sound (c := X (k :: ls) x []) (next_sound _ _ _) hR
      have h := steps_sub hX h₁ (by omega)
      rw [Nat.add_sub_cancel_left] at h
      exact ⟨c', h, h₂⟩

/-! ## Four events are the super step, in time too -/

theorem leftTimeE_eq : ∀ (f d A : Nat), leftTimeE f d (A + 6) = leftTime f d A := by
  intro f
  induction f with
  | zero => intro d A; rfl
  | succ f ih =>
    intro d A
    simp only [leftTimeE, leftTime]
    split
    · simp only [oddE, oddT]; omega
    · split
      · rfl
      · rw [show A + 6 + d / 2 + 1 = (A + d / 2 + 1) + 6 by omega, ih]

theorem waveTimeE_eq : ∀ (L : List Nat) (d A : Nat), waveTimeE d L (A + 6) = waveTime d L A := by
  intro L
  induction L with
  | nil => intro d A; exact leftTimeE_eq d d A
  | cons p L ih =>
    intro d A
    simp only [waveTimeE, waveTime]
    split
    · simp only [oddE, oddT]; omega
    · rw [show A + 6 + d / 2 + 1 = (A + d / 2 + 1) + 6 by omega, ih]

/-- **The four events of a super step take `superT` steps**: 17, 27 and 101 steps, then the wave of the fourth. -/
theorem ev4_time (p : Nat) (L : List Nat) :
    evT (0 :: 5 :: p :: L) + evT (2 :: 6 :: p :: L) + evT (3 :: 8 :: p :: L) + evT (1 :: 8 :: (p + 5) :: L)
      = superT (p :: L) := by
  have h₄ : evT (1 :: 8 :: (p + 5) :: L) = 55 + waveTimeE (p + 10) L (3 + 6) := by
    show 5 + waveTimeE 10 ((p + 5) :: L) 3 = _
    rw [waveTimeE_even 10 (p + 5) L 3 (by decide), show p + 5 + 10 / 2 = p + 10 by omega,
      show evenT 10 = 50 by rfl, show 3 + 10 / 2 + 1 = 3 + 6 by rfl]
    omega
  have h₃ : evT (3 :: 8 :: p :: L) = 101 := by
    show 2 * 1 * 1 + 9 * 1 + 5 + waveTimeE 11 (p :: L) 4 = 101
    rw [waveTimeE_odd 11 p L 4 (by decide)]
    rfl
  rw [h₄, h₃, waveTimeE_eq, show evT (0 :: 5 :: p :: L) = 17 by rfl, show evT (2 :: 6 :: p :: L) = 27 by rfl]
  show _ = 200 + waveTime (p + 10) L 3
  omega

/-! ## The event orbit with times -/

/-- `j` events from `b`, with the machine step `t` at `b`: `some (b', t')` with `b'` the event after `j` events and
`t'` its machine step, or `none` if an event on the way halts. -/
def evOrbitT : Nat → List Nat → Nat → Option (List Nat × Nat)
  | 0, b, t => some (b, t)
  | j + 1, b, t =>
    match ev b with
    | none => none
    | some b' => evOrbitT j b' (t + evT b)

/-- **The timed event orbit is the machine's run**: if the machine is at the event `E b` after `t` steps and
`evOrbitT j b t = some (b', t')`, it is at the event `E b'` after `t'` steps. -/
theorem evOrbitT_steps : ∀ (j : Nat) (b : List Nat) (t : Nat) (b' : List Nat) (t' : Nat), GoodE b →
    steps t init = some (E b) → evOrbitT j b t = some (b', t') → steps t' init = some (E b') := by
  intro j
  induction j with
  | zero => intro b t b' t' _ hs h; cases h; exact hs
  | succ j ih =>
    intro b t b' t' hb hs h
    simp only [evOrbitT] at h
    cases e : ev b with
    | none => rw [e] at h; cases h
    | some c =>
      rw [e] at h
      exact ih c _ b' t' (ev_good b c hb e) (steps_seq trans hs ((ev_steps b hb).1 c e)) h

/-- The events from blank tape, at the steps they come: the event `[2, 1]` at step 17, and from there the timed
event orbit. -/
theorem evOrbitT_tape (j : Nat) (b : List Nat) (t : Nat) (h : evOrbitT j [2, 1] 17 = some (b, t)) :
    steps t init = some (E b) :=
  evOrbitT_steps j [2, 1] 17 b t ⟨by decide, by simp⟩ init_E h

/-! Checks against `py/waves.py` (`events`, which counts the steps of each event by simulating the local rules): the
first events come at steps 17, 44, 101, 136, and the super-step tapes (every fourth event) at steps 136, 544, 1,186,
1,604 and 2,812, as `orbitT` of `WaveTime.lean` says. -/

example : evT [2, 1] = 27 := by decide
example : evOrbitT 3 [2, 1] 17 = some ([0, 5, 6, 1], 136) := by decide
example : evOrbitT 7 [2, 1] 17 = some ([0, 5, 8, 7, 4], 544) := by decide
example : evOrbitT 11 [2, 1] 17 = some ([0, 5, 9, 8, 6, 3, 4, 1], 1186) := by decide
example : evOrbitT 19 [2, 1] 17 = some ([0, 5, 11, 14, 10, 9, 10, 1], 2812) := by decide
example : evOrbitT 2 [2, 1] 17 = some ([1, 3, 4, 1], 101) := by decide
example : evOrbitT 1 [1, 8, 11, 1] 281 = some ([0, 5, 8, 7, 4], 544) := by decide

end BB6b
