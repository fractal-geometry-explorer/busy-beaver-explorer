import Macro

/-!
# The wave model: the machine halts iff a number N is ever a power of two

`py/waves.py` reads the run in another cut.  Every fourth time A stands on the blank right of the tape, the tape is
`0^∞ 1^{p_1} 0 1^{p_2} 0 … 0 1^{p_m} 0 1^5 0 A> 0^∞`, which is the macro configuration `X (5 :: [p_m, …, p_1]) 0 []`
of `Macro.lean`, and the next such configuration follows from `P = (p_1, …, p_m)` by a wave of halvings running left:
put `d_{m+1} = 20`, `d_l = p_l + d_{l+1} / 2`; the wave passes the blocks while `d` is even and turns at the first odd
`d_i`.  This file proves that super step from `next`, and the halting criterion
`N = 10 + Σ p_l · 2^{m-l}` is a power of two.

Here the lists are nearest first, as in `Macro.lean`: `L = [p_m, …, p_1]`.

* `wave d L`: the wave standing at a block with value `d`, with the blocks `L` further left.  At an odd `d` it turns:
  that block becomes `(d + 5) / 2` and the next one gains `(d - 1) / 2`; at an even `d` it leaves `d / 2` and moves on
  with `p + d / 2`.  At the left end (`leftEnd`) it goes on halving with `p = 0`, and **halts when `d` reaches 1**.
* `superL (p_m :: L) = wave (p_m + 10) L`: the new list `W`, nearest first, with the tape `X (5 :: W) 0 []`.
* `super_run`: the macro run goes from `X (5 :: L) 0 []` to `X (5 :: W) 0 []` (at least one macro step), or halts if
  `superL L = none` (kernel-checked, every list).
* `superL_none_iff`: `superL L = none` iff `bigN L = 10 + p_m + 2 p_{m-1} + 4 p_{m-2} + …` is a power of two.
* `halts_iff_pow2`: **the machine halts from blank tape iff some list of the super orbit from `[6, 1]` has `bigN` a
  power of two**; `halts_iff_pow2'` says the same in the order of `waves.py`, with `superstep` and `bigNP`.

Step counts are not carried here: the macro run is followed without its times (`Res`).
-/

namespace BB6b

open TM

/-! ## The macro run without step counts -/

/-- Where the macro run is, without the step count: at `X ls n cs`, halted, or stuck (an ill-formed list). -/
inductive Res where
  | go (ls : List Nat) (n : Nat) (cs : List Nat)
  | halt
  | stuck
  deriving DecidableEq, Repr

def Out.res : Out → Res
  | .go ls n cs _ => .go ls n cs
  | .halt _ => .halt

def res : Option Out → Res
  | some o => o.res
  | none => .stuck

/-- `a` macro steps from `r`. -/
def Res.run : Nat → Res → Res
  | 0, r => r
  | a + 1, .go ls n cs => (res (next ls n cs)).run a
  | _ + 1, .halt => .halt
  | _ + 1, .stuck => .stuck

theorem Res.run_halt (a : Nat) : Res.halt.run a = .halt := by cases a <;> rfl

theorem Res.run_stuck (a : Nat) : Res.stuck.run a = .stuck := by cases a <;> rfl

theorem Res.run_add : ∀ (a b : Nat) (r : Res), (r.run a).run b = r.run (a + b) := by
  intro a
  induction a with
  | zero => intro b r; rw [Nat.zero_add]; rfl
  | succ a ih =>
    intro b r
    cases r with
    | go ls n cs =>
      show ((res (next ls n cs)).run a).run b = Res.run (a + 1 + b) (.go ls n cs)
      rw [ih, show a + 1 + b = (a + b) + 1 by omega]; rfl
    | halt => simp only [run_halt]
    | stuck => simp only [run_stuck]

theorem res_map_addT (a : Nat) (o : Option Out) : res (o.map (Out.addT a)) = res o := by
  cases o with
  | none => rfl
  | some o => cases o <;> rfl

theorem res_runFrom : ∀ (m : Nat) (o : Out), res (runFrom m o) = o.res.run m := by
  intro m
  induction m with
  | zero => intro o; rfl
  | succ m ih =>
    intro o
    cases o with
    | halt t => rw [Out.res, Res.run_halt]; rfl
    | go ls n cs t =>
      simp only [runFrom, Out.res, Res.run]
      cases next ls n cs with
      | none => rw [res, Res.run_stuck]
      | some o => rw [ih]; cases o <;> rfl

/-- The machine halts from blank tape iff the time-free macro run from `X [1] 2 []` halts. -/
theorem halts_iff_run : HaltsFromBlank ↔ ∃ m, (Res.go [1] 2 []).run m = .halt := by
  rw [halts_iff]
  constructor
  · rintro ⟨m, t, e⟩
    have h := res_runFrom m (.go [1] 2 [] 15)
    change res (runM m) = _ at h
    rw [e] at h
    exact ⟨m, h.symm⟩
  · rintro ⟨m, h⟩
    have h' := res_runFrom m (.go [1] 2 [] 15)
    change res (runM m) = _ at h'
    have h'' := h'.trans h
    cases e : runM m with
    | none => rw [e] at h''; cases h''
    | some o =>
      rw [e] at h''
      cases o with
      | go => cases h''
      | halt t => exact ⟨m, t, e⟩

/-- A run that reaches `X ls n cs` in `a` macro steps and halts in `k` passes `X ls n cs` first. -/
theorem Res.run_det {r : Res} {a k : Nat} {ls n cs} (h₁ : r.run k = .halt) (h₂ : r.run a = .go ls n cs) :
    a < k ∧ (Res.go ls n cs).run (k - a) = .halt := by
  by_cases hk : a < k
  · refine ⟨hk, ?_⟩
    rw [← h₂, Res.run_add, show a + (k - a) = k by omega, h₁]
  · exfalso
    have h := Res.run_add k (a - k) r
    rw [h₁, Res.run_halt, show k + (a - k) = a by omega, h₂] at h
    cases h

/-! ## Where an outcome leads -/

/-- The outcome `o` leads to `X W 0 []` (`x = some W`) or to a halt (`x = none`). -/
def Ends (o : Option Out) : Option (List Nat) → Prop
  | some W => ∃ a, (res o).run a = .go W 0 []
  | none => ∃ a, (res o).run a = .halt

theorem ends_map {a : Nat} {o : Option Out} {x : Option (List Nat)} : Ends (o.map (Out.addT a)) x ↔ Ends o x := by
  cases x <;> simp only [Ends, res_map_addT]

theorem ends_go {ls n cs t} {x : Option (List Nat)} (h : Ends (next ls n cs) x) : Ends (some (.go ls n cs t)) x := by
  cases x with
  | some W => obtain ⟨a, h⟩ := h; exact ⟨a + 1, h⟩
  | none => obtain ⟨a, h⟩ := h; exact ⟨a + 1, h⟩

theorem ends_eq {X Y : List Nat} {t : Nat} (h : X = Y) : Ends (some (.go X 0 [] t)) (some Y) := h ▸ ⟨0, rfl⟩

/-! ## The wave -/

/-- The wave at the left end, with fuel `f`: it halves `d` while `d` is even and halts at 1. -/
def leftEnd : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | f + 1, d =>
    if d ≤ 1 then none
    else if d % 2 = 1 then some [(d + 5) / 2, (d - 1) / 2]
    else (leftEnd f (d / 2)).map (d / 2 :: ·)

/-- The wave at a block with value `d` and the blocks `L` further left (nearest first): the new blocks from here on,
nearest first, or `none` for a halt. -/
def wave : Nat → List Nat → Option (List Nat)
  | d, [] => leftEnd d d
  | d, p :: L =>
    if d % 2 = 1 then some ((d + 5) / 2 :: (p + (d - 1) / 2) :: L)
    else (wave (p + d / 2) L).map (d / 2 :: ·)

/-- **The super step** on `L = [p_m, …, p_1]`: the tape `X (5 :: L) 0 []` goes to `X (5 :: W) 0 []`
(`superL L = some W`) or halts (`none`). -/
def superL : List Nat → Option (List Nat)
  | [] => none
  | p :: L => wave (p + 10) L

theorem leftEnd_odd (f d : Nat) (h₁ : 2 ≤ d) (h₂ : d % 2 = 1) :
    leftEnd (f + 1) d = some [(d + 5) / 2, (d - 1) / 2] := by
  rw [leftEnd, ite_eq_right (by omega), ite_eq_left h₂]

theorem leftEnd_even (f d : Nat) (h₁ : 2 ≤ d) (h₂ : d % 2 = 0) :
    leftEnd (f + 1) d = (leftEnd f (d / 2)).map (d / 2 :: ·) := by
  rw [leftEnd, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem leftEnd_two : ∀ f, leftEnd f 2 = none
  | 0 => rfl
  | f + 1 => by rw [leftEnd_even f 2 (by omega) (by omega)]; cases f <;> rfl

theorem wave_odd (d p : Nat) (L : List Nat) (h : d % 2 = 1) :
    wave d (p :: L) = some ((d + 5) / 2 :: (p + (d - 1) / 2) :: L) := by
  rw [wave, ite_eq_left h]

theorem wave_even (d p : Nat) (L : List Nat) (h : d % 2 = 0) :
    wave d (p :: L) = (wave (p + d / 2) L).map (d / 2 :: ·) := by
  rw [wave, ite_eq_right (by omega)]

/-! ## The wave is what the macro run does

During the wave the carry of `Macro.lean` stands at a block whose carry value is `d - 2`, with `e` blocks of 2 just
eaten, and the blocks on the right are `c0 :: R ++ [1]`: `c0 + 2` and `r + 1` (`r ∈ R`) are what the sweep at the end
will leave on the left, after `pre`. -/

/-- What the sweep at the end of the wave leaves next to the head, before the wave's own blocks. -/
def pre (R : List Nat) (c0 e : Nat) : List Nat := (R.map (· + 1)).reverse ++ (c0 + 2) :: List.replicate e 2

theorem sweep_app_one : ∀ (cs ls : List Nat) (m : Nat), (∀ c ∈ cs, 0 < c) →
    ∃ t, sweep ls m (cs ++ [1]) = some (.go ((cs.map (· + 1)).reverse ++ (m + 2) :: ls) 0 [] t) := by
  intro cs
  induction cs with
  | nil => intro ls m _; exact ⟨_, rfl⟩
  | cons c cs ih =>
    intro ls m h
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    obtain ⟨t, e⟩ := ih ((m + 2) :: ls) c' h.2
    refine ⟨m + 3 + t, ?_⟩
    simp only [List.cons_append, sweep, e, Option.map_some, Out.addT, List.map_cons, List.reverse_cons,
      List.append_assoc, List.nil_append]

theorem sweep_pre (R : List Nat) (c0 e m : Nat) (ls : List Nat) (hR : ∀ r ∈ R, 0 < r) :
    ∃ t, sweep ls m (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1])) = some (.go (pre R c0 e ++ (m + 2) :: ls) 0 [] t) := by
  have hc : ∀ c ∈ List.replicate e 1 ++ (c0 + 1) :: R, 0 < c := by
    intro c hc
    simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hc
    rcases hc with ⟨_, rfl⟩ | rfl | hc
    · decide
    · omega
    · exact hR c hc
  obtain ⟨t, e'⟩ := sweep_app_one _ ls m hc
  refine ⟨t, ?_⟩
  rw [show List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]) = (List.replicate e 1 ++ (c0 + 1) :: R) ++ [1] by simp, e']
  simp [pre, List.map_replicate, List.reverse_replicate]

theorem pre_eq (R : List Nat) (c0 e j : Nat) (W : List Nat) :
    pre R c0 e ++ (j + 3) :: W = pre (List.replicate e 1 ++ (c0 + 1) :: R) (1 + j) 0 ++ W := by
  simp [pre, List.map_replicate, List.reverse_replicate]
  omega

theorem carry_left : ∀ (f d e c0 : Nat) (R : List Nat), 3 ≤ d → d ≤ f → (∀ r ∈ R, 0 < r) →
    Ends (carry [d - 2] e (c0 :: (R ++ [1]))) ((leftEnd f d).map (pre R c0 e ++ ·)) := by
  intro f
  induction f with
  | zero => intro d e c0 R h₃ hf _; omega
  | succ f ih =>
    intro d e c0 R h₃ hf hR
    have hd : d = 3 ∨ d = 4 ∨ (d % 2 = 1 ∧ 5 ≤ d) ∨ (d % 2 = 0 ∧ 6 ≤ d) := by omega
    rcases hd with rfl | rfl | ⟨hd, hd'⟩ | ⟨hd, hd'⟩
    · -- d = 3: the carry meets a block of 1 and A sweeps right
      show Ends ((sweep [1] 2 (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))).map (Out.addT 15))
        (some (pre R c0 e ++ [4, 1]))
      rw [ends_map]
      obtain ⟨t, ht⟩ := sweep_pre R c0 e 2 [1] hR
      rw [ht]
      exact ⟨0, rfl⟩
    · -- d = 4: the carry eats the last block of 2 and the machine halts
      have h : leftEnd (f + 1) 4 = none := by rw [leftEnd_even f 4 (by omega) (by omega)]; rw [leftEnd_two]; rfl
      rw [h]
      exact ⟨0, rfl⟩
    · -- d odd: a new block at the left end, a transfer phase, and a sweep
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 5 := ⟨(d - 5) / 2, by omega⟩
      rw [leftEnd_odd f _ (by omega) hd, show 2 * j + 5 - 2 = 2 * j + 3 by omega,
        show (2 * j + 5 + 5) / 2 = j + 5 by omega, show (2 * j + 5 - 1) / 2 = j + 2 by omega]
      show Ends (some (.go [1] (2 * j) (1 :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))) _)) _
      apply ends_go
      show Ends ((exit [1 + 2 * j / 2] (2 * j % 2) (bumpBy (2 * j / 2) _)).map _) _
      rw [ends_map, show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega]
      show Ends ((sweep [1 + j + 1] (1 + j + 2) (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))).map _) _
      rw [ends_map]
      obtain ⟨t, ht⟩ := sweep_pre R c0 e (1 + j + 2) [1 + j + 1] hR
      rw [ht]
      exact ends_eq (by
        show _ = pre R c0 e ++ [j + 5, j + 2]
        rw [show 1 + j + 2 + 2 = j + 5 by omega, show 1 + j + 1 = j + 2 by omega])
    · -- d even: a new block at the left end, a transfer phase, and the carry again with d / 2
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 6 := ⟨(d - 6) / 2, by omega⟩
      rw [leftEnd_even f _ (by omega) hd, show 2 * j + 6 - 2 = 2 * j + 1 + 3 by omega,
        show (2 * j + 6) / 2 = j + 3 by omega]
      show Ends (some (.go [1] (2 * j + 1) (1 :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))) _)) _
      apply ends_go
      show Ends ((exit [1 + (2 * j + 1) / 2] ((2 * j + 1) % 2) (bumpBy ((2 * j + 1) / 2) _)).map _) _
      rw [ends_map, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]
      show Ends ((carry [1 + j] 0 ((1 + j) :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1])))).map _) _
      rw [ends_map]
      have hR' : ∀ r ∈ List.replicate e 1 ++ (c0 + 1) :: R, 0 < r := by
        intro r hr
        simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hr
        rcases hr with ⟨_, rfl⟩ | rfl | hr
        · decide
        · omega
        · exact hR r hr
      have h := ih (j + 3) 0 (1 + j) _ (by omega) (by omega) hR'
      rw [show j + 3 - 2 = 1 + j by omega,
        show (List.replicate e 1 ++ (c0 + 1) :: R) ++ [1] = List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]) by simp] at h
      have hx : ((leftEnd f (j + 3)).map ((j + 3) :: ·)).map (pre R c0 e ++ ·)
          = (leftEnd f (j + 3)).map (pre (List.replicate e 1 ++ (c0 + 1) :: R) (1 + j) 0 ++ ·) := by
        cases leftEnd f (j + 3) with
        | none => rfl
        | some W => simp only [Option.map_some, pre_eq]
      rw [hx]
      exact h

theorem pre_pos (R : List Nat) (c0 e : Nat) (hR : ∀ r ∈ R, 0 < r) : ∀ r ∈ List.replicate e 1 ++ (c0 + 1) :: R, 0 < r := by
  intro r hr
  simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hr
  rcases hr with ⟨_, rfl⟩ | rfl | hr
  · decide
  · omega
  · exact hR r hr

/-- **The wave is what the macro run does**: from a carry with value `d - 2` at the blocks `L`, the macro run ends
at `X (pre R c0 e ++ W) 0 []` where `wave d L = some W`, or halts where `wave d L = none`. -/
theorem carry_wave : ∀ (L : List Nat) (d e c0 : Nat) (R : List Nat), 3 ≤ d → (∀ p ∈ L, 0 < p) → (∀ r ∈ R, 0 < r) →
    Ends (carry ((d - 2) :: L) e (c0 :: (R ++ [1]))) ((wave d L).map (pre R c0 e ++ ·)) := by
  intro L
  induction L with
  | nil => intro d e c0 R h₃ _ hR; exact carry_left d d e c0 R h₃ (Nat.le_refl d) hR
  | cons p L ih =>
    intro d e c0 R h₃ hL hR
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    obtain ⟨hp, hL⟩ := hL
    have hd : d = 3 ∨ d = 4 ∨ (d % 2 = 1 ∧ 5 ≤ d) ∨ (d % 2 = 0 ∧ 6 ≤ d) := by omega
    rcases hd with rfl | rfl | ⟨hd, hd'⟩ | ⟨hd, hd'⟩
    · -- d = 3: the carry meets a block of 1 and A sweeps right
      rw [wave_odd 3 p L (by decide)]
      show Ends ((sweep ((p + 1) :: L) 2 (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))).map (Out.addT 15)) _
      rw [ends_map]
      obtain ⟨t, ht⟩ := sweep_pre R c0 e 2 ((p + 1) :: L) hR
      rw [ht]
      exact ends_eq rfl
    · -- d = 4: the carry eats a block of 2 and goes on to `p`
      rw [wave_even 4 p L (by decide)]
      show Ends ((carry (p :: L) (e + 1) (c0 :: (R ++ [1]))).map (Out.addT 5)) _
      rw [ends_map]
      have h := ih (p + 2) (e + 1) c0 R (by omega) hL hR
      rw [show p + 2 - 2 = p by omega] at h
      have hx : ((wave (p + 4 / 2) L).map (4 / 2 :: ·)).map (pre R c0 e ++ ·)
          = (wave (p + 2) L).map (pre R c0 (e + 1) ++ ·) := by
        cases wave (p + 2) L with
        | none => rfl
        | some W => simp [pre, List.replicate_succ']
      rw [hx]
      exact h
    · -- d odd: the head's block takes a transfer phase, then A sweeps right
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 5 := ⟨(d - 5) / 2, by omega⟩
      rw [wave_odd _ p L hd, show 2 * j + 5 - 2 = 2 * j + 3 by omega,
        show (2 * j + 5 + 5) / 2 = j + 5 by omega, show (2 * j + 5 - 1) / 2 = j + 2 by omega]
      show Ends (some (.go ((p + 1) :: L) (2 * j) (1 :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))) _)) _
      apply ends_go
      show Ends ((exit ((p + 1 + 2 * j / 2) :: L) (2 * j % 2) (bumpBy (2 * j / 2) _)).map _) _
      rw [ends_map, show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega]
      show Ends ((sweep ((p + 1 + j + 1) :: L) (1 + j + 2) (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))).map _) _
      rw [ends_map]
      obtain ⟨t, ht⟩ := sweep_pre R c0 e (1 + j + 2) ((p + 1 + j + 1) :: L) hR
      rw [ht]
      exact ends_eq (by
        show _ = pre R c0 e ++ (j + 5) :: (p + (j + 2)) :: L
        rw [show 1 + j + 2 + 2 = j + 5 by omega, show p + 1 + j + 1 = p + (j + 2) by omega])
    · -- d even: a transfer phase, and the carry goes on to `p` with `p + d / 2`
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 6 := ⟨(d - 6) / 2, by omega⟩
      rw [wave_even _ p L hd, show 2 * j + 6 - 2 = 2 * j + 1 + 3 by omega, show (2 * j + 6) / 2 = j + 3 by omega]
      show Ends (some (.go ((p + 1) :: L) (2 * j + 1) (1 :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))) _)) _
      apply ends_go
      show Ends ((exit ((p + 1 + (2 * j + 1) / 2) :: L) ((2 * j + 1) % 2) (bumpBy ((2 * j + 1) / 2) _)).map _) _
      rw [ends_map, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]
      show Ends ((carry ((p + 1 + j) :: L) 0 ((1 + j) :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1])))).map _) _
      rw [ends_map]
      have h := ih (p + (j + 3)) 0 (1 + j) _ (by omega) hL (pre_pos R c0 e hR)
      rw [show p + (j + 3) - 2 = p + 1 + j by omega,
        show (List.replicate e 1 ++ (c0 + 1) :: R) ++ [1] = List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]) by simp] at h
      have hx : ((wave (p + (j + 3)) L).map ((j + 3) :: ·)).map (pre R c0 e ++ ·)
          = (wave (p + (j + 3)) L).map (pre (List.replicate e 1 ++ (c0 + 1) :: R) (1 + j) 0 ++ ·) := by
        cases wave (p + (j + 3)) L with
        | none => rfl
        | some W => simp only [Option.map_some, pre_eq]
      rw [hx]
      exact h

/-! ## The super step -/

/-- The five macro steps from `X (5 :: p :: L) 0 []` to the first carry of the wave, with value `p + 8`. -/
theorem super_prefix (p : Nat) (L : List Nat) :
    (Res.go (5 :: p :: L) 0 []).run 6 = res (carry ((p + 8) :: L) 0 [3, 1]) := by
  show res (next ((p + 6) :: L) 5 [1, 1]) = _
  show res (((carry ((p + 6 + 2) :: L) 0 [3, 1]).map (Out.addT 6)).map (Out.addT (tsteps 1 2))) = _
  rw [res_map_addT, res_map_addT]

/-- **The super step is sound**: from `X (5 :: L) 0 []` the macro run reaches `X (5 :: W) 0 []` in at least one
macro step if `superL L = some W`, and halts if `superL L = none`. -/
theorem super_run (p : Nat) (L : List Nat) (hL : ∀ q ∈ L, 0 < q) :
    (∀ W, superL (p :: L) = some W → ∃ a, (Res.go (5 :: p :: L) 0 []).run (a + 1) = .go (5 :: W) 0 []) ∧
    (superL (p :: L) = none → ∃ a, (Res.go (5 :: p :: L) 0 []).run a = .halt) := by
  have h := carry_wave L (p + 10) 0 3 [] (by omega) hL (by simp)
  rw [show p + 10 - 2 = p + 8 by rfl] at h
  constructor
  · intro W hW
    simp only [superL] at hW
    rw [hW] at h
    obtain ⟨a, ha⟩ := h
    refine ⟨5 + a, ?_⟩
    rw [show 5 + a + 1 = 6 + a by omega, ← Res.run_add, super_prefix]
    exact ha
  · intro hW
    simp only [superL] at hW
    rw [hW] at h
    obtain ⟨a, ha⟩ := h
    refine ⟨6 + a, ?_⟩
    rw [← Res.run_add, super_prefix]
    exact ha

/-! ## The new lists are well formed -/

def GoodL (L : List Nat) : Prop := L ≠ [] ∧ ∀ p ∈ L, 0 < p

theorem leftEnd_good : ∀ (f d : Nat) (W : List Nat), 3 ≤ d → leftEnd f d = some W → GoodL W := by
  intro f
  induction f with
  | zero => intro d W _ h; cases h
  | succ f ih =>
    intro d W h₃ h
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd
    · rw [leftEnd_even f d (by omega) hd] at h
      cases e : leftEnd f (d / 2) with
      | none => rw [e] at h; cases h
      | some W' =>
        rw [e] at h
        cases h
        by_cases h₃' : 3 ≤ d / 2
        · have := (ih _ _ h₃' e).2
          refine ⟨by simp, ?_⟩
          simp only [List.mem_cons, forall_eq_or_imp]
          exact ⟨by omega, this⟩
        · -- d = 4: then d / 2 = 2 and the left end halts
          have : d / 2 = 2 := by omega
          rw [this, leftEnd_two] at e
          cases e
    · rw [leftEnd_odd f d (by omega) hd] at h
      cases h
      refine ⟨by simp, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      omega

theorem wave_good : ∀ (L : List Nat) (d : Nat) (W : List Nat), 3 ≤ d → (∀ p ∈ L, 0 < p) → wave d L = some W →
    GoodL W := by
  intro L
  induction L with
  | nil => intro d W h₃ _ h; exact leftEnd_good d d W h₃ h
  | cons p L ih =>
    intro d W h₃ hL h
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd
    · rw [wave_even d p L hd] at h
      cases e : wave (p + d / 2) L with
      | none => rw [e] at h; cases h
      | some W' =>
        rw [e] at h
        cases h
        have := (ih _ _ (by omega) hL.2 e).2
        refine ⟨by simp, ?_⟩
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨by omega, this⟩
    · rw [wave_odd d p L hd] at h
      cases h
      refine ⟨by simp, ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨by omega, by omega, hL.2⟩

theorem superL_good (L W : List Nat) (hL : GoodL L) (h : superL L = some W) : GoodL W := by
  match L, hL with
  | p :: L, ⟨_, hL⟩ =>
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    exact wave_good L (p + 10) W (by omega) hL.2 h

/-! ## The halting criterion: N is a power of two -/

/-- The blocks read as binary digits, nearest first the units: `S [p_m, …, p_1] = p_m + 2 p_{m-1} + 4 p_{m-2} + …`. -/
def S : List Nat → Nat
  | [] => 0
  | p :: L => p + 2 * S L

/-- `N = 10 + Σ p_l 2^{m-l}` for `L = [p_m, …, p_1]`. -/
def bigN (L : List Nat) : Nat := 10 + S L

theorem pow2_double (x : Nat) : (∃ a, 2 * x = 2 ^ a) ↔ ∃ a, x = 2 ^ a := by
  constructor
  · rintro ⟨a, h⟩
    cases a with
    | zero => simp at h; omega
    | succ a => exact ⟨a, by rw [Nat.pow_succ] at h; omega⟩
  · rintro ⟨a, h⟩; exact ⟨a + 1, by rw [Nat.pow_succ]; omega⟩

theorem not_pow2_odd (x : Nat) (h₁ : 3 ≤ x) (h₂ : x % 2 = 1) : ¬ ∃ a, x = 2 ^ a := by
  rintro ⟨a, h⟩
  cases a with
  | zero => simp at h; omega
  | succ a => rw [Nat.pow_succ] at h; omega

theorem leftEnd_none_iff : ∀ (f d : Nat), 1 ≤ d → d ≤ f → (leftEnd f d = none ↔ ∃ a, d = 2 ^ a) := by
  intro f
  induction f with
  | zero => intro d h₁ h₂; omega
  | succ f ih =>
    intro d h₁ h₂
    by_cases h₃ : d = 1
    · subst h₃; exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd
    · rw [leftEnd_even f d (by omega) hd]
      have e := ih (d / 2) (by omega) (by omega)
      rw [show d = 2 * (d / 2) by omega, pow2_double, ← e, show 2 * (d / 2) / 2 = d / 2 by omega]
      cases leftEnd f (d / 2) <;> simp
    · rw [leftEnd_odd f d (by omega) hd]
      simp only [reduceCtorEq, false_iff]
      exact not_pow2_odd d (by omega) hd

theorem wave_none_iff : ∀ (L : List Nat) (d : Nat), 3 ≤ d → (∀ p ∈ L, 0 < p) →
    (wave d L = none ↔ ∃ a, d + 2 * S L = 2 ^ a) := by
  intro L
  induction L with
  | nil => intro d h₃ _; simp only [S, Nat.mul_zero, Nat.add_zero]; exact leftEnd_none_iff d d (by omega) (by omega)
  | cons p L ih =>
    intro d h₃ hL
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd
    · rw [wave_even d p L hd]
      have e := ih (p + d / 2) (by omega) hL.2
      rw [show d + 2 * S (p :: L) = 2 * (p + d / 2 + 2 * S L) by simp only [S]; omega, pow2_double, ← e]
      cases wave (p + d / 2) L <;> simp
    · rw [wave_odd d p L hd]
      simp only [reduceCtorEq, false_iff]
      exact not_pow2_odd _ (by omega) (by simp only [S]; omega)

/-- **A super step halts iff N is a power of two.** -/
theorem superL_none_iff (L : List Nat) (hL : GoodL L) : superL L = none ↔ ∃ a, bigN L = 2 ^ a := by
  match L, hL with
  | p :: L, ⟨_, hL⟩ =>
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    rw [superL, wave_none_iff L (p + 10) (by omega) hL.2, bigN, S]
    rw [show p + 10 + 2 * S L = 10 + (p + 2 * S L) by omega]

/-! ## The machine halts iff N is ever a power of two -/

/-- `j` super steps from `L` (`none` once a super step halts). -/
def orbit : Nat → List Nat → Option (List Nat)
  | 0, L => some L
  | j + 1, L => (superL L).bind (orbit j)

/-- From `X (5 :: L) 0 []` the macro run halts iff some list of the super orbit from `L` has `bigN` a power of two. -/
theorem run_halts_iff (L : List Nat) (hL : GoodL L) :
    (∃ m, (Res.go (5 :: L) 0 []).run m = .halt) ↔ ∃ j W, orbit j L = some W ∧ ∃ a, bigN W = 2 ^ a := by
  constructor
  · rintro ⟨m, hm⟩
    induction m using Nat.strongRecOn generalizing L with
    | ind m ihm =>
      match L, hL with
      | p :: L', hL =>
        cases e : superL (p :: L') with
        | none => exact ⟨0, p :: L', rfl, (superL_none_iff _ hL).1 e⟩
        | some W =>
          have hW := superL_good _ _ hL e
          obtain ⟨a, ha⟩ := (super_run p L' (fun q hq => hL.2 q (List.mem_cons_of_mem p hq))).1 W e
          obtain ⟨hlt, hk⟩ := Res.run_det hm ha
          obtain ⟨j, W', h₁, h₂⟩ := ihm (m - (a + 1)) (by omega) W hW hk
          exact ⟨j + 1, W', by simp only [orbit, e, Option.bind_some]; exact h₁, h₂⟩
  · rintro ⟨j, W, h₁, h₂⟩
    induction j generalizing L with
    | zero =>
      cases h₁
      match W, hL with
      | p :: L', hL =>
        exact (super_run p L' (fun q hq => hL.2 q (List.mem_cons_of_mem p hq))).2 ((superL_none_iff _ hL).2 h₂)
    | succ j ih =>
      match L, hL with
      | p :: L', hL =>
        cases e : superL (p :: L') with
        | none => simp only [orbit, e, Option.bind_none] at h₁; cases h₁
        | some W' =>
          simp only [orbit, e, Option.bind_some] at h₁
          obtain ⟨m, hm⟩ := ih W' (superL_good _ _ hL e) h₁
          obtain ⟨a, ha⟩ := (super_run p L' (fun q hq => hL.2 q (List.mem_cons_of_mem p hq))).1 W' e
          exact ⟨a + 1 + m, by rw [← Res.run_add, ha, hm]⟩

/-- The run from blank tape is at `X [5, 6, 1] 0 []` after five macro steps (step 136): the tape `[1, 6, 5, 0]`. -/
theorem run_start : (Res.go [1] 2 []).run 5 = .go [5, 6, 1] 0 [] := by decide

/-- **The machine halts from blank tape iff N is ever a power of two**: iff some list `W` of the super orbit from
`[6, 1]` (the tape `[1, 6, 5, 0]`) has `bigN W = 10 + S W` a power of two. -/
theorem halts_iff_pow2 : HaltsFromBlank ↔ ∃ j W, orbit j [6, 1] = some W ∧ ∃ a, bigN W = 2 ^ a := by
  rw [halts_iff_run, ← run_halts_iff [6, 1] ⟨by simp, by simp⟩]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨_, hk⟩ := Res.run_det hm run_start
    exact ⟨_, hk⟩
  · rintro ⟨m, hm⟩
    exact ⟨5 + m, by rw [← Res.run_add, run_start, hm]⟩

/-- The configurations of the super orbit are configurations of the machine's run from blank tape. -/
theorem orbit_reached : ∀ (j : Nat) (W : List Nat), orbit j [6, 1] = some W →
    ∃ m, (Res.go [1] 2 []).run m = .go (5 :: W) 0 [] := by
  have key : ∀ (j : Nat) (L W : List Nat), GoodL L → orbit j L = some W →
      ∃ m, (Res.go (5 :: L) 0 []).run m = .go (5 :: W) 0 [] := by
    intro j
    induction j with
    | zero => intro L W _ h; cases h; exact ⟨0, rfl⟩
    | succ j ih =>
      intro L W hL h
      match L, hL with
      | p :: L', hL =>
        cases e : superL (p :: L') with
        | none => simp only [orbit, e, Option.bind_none] at h; cases h
        | some W' =>
          simp only [orbit, e, Option.bind_some] at h
          obtain ⟨m, hm⟩ := ih W' W (superL_good _ _ hL e) h
          obtain ⟨a, ha⟩ := (super_run p L' (fun q hq => hL.2 q (List.mem_cons_of_mem p hq))).1 W' e
          exact ⟨a + 1 + m, by rw [← Res.run_add, ha, hm]⟩
  intro j W h
  obtain ⟨m, hm⟩ := key j [6, 1] W ⟨by simp, by simp⟩ h
  exact ⟨5 + m, by rw [← Res.run_add, run_start, hm]⟩

theorem run_reached (m : Nat) (ls : List Nat) (n : Nat) (cs : List Nat) (h : (Res.go [1] 2 []).run m = .go ls n cs) :
    ∃ t, steps t init = some (X ls n cs) := by
  have h' := res_runFrom m (.go [1] 2 [] 15)
  change res (runM m) = (Res.go [1] 2 []).run m at h'
  rw [h] at h'
  cases e : runM m with
  | none => rw [e] at h'; cases h'
  | some o =>
    rw [e] at h'
    cases o with
    | halt => cases h'
    | go ls' n' cs' t =>
      cases h'
      exact ⟨t, runM_sound m _ e⟩

/-- **The wave model's tapes occur**: for every list `W = [p_m, …, p_1]` of the super orbit, the machine from blank
tape reaches `0^∞ 1^{p_1} 0 … 0 1^{p_m} 0 1^5 0 A> 0^∞`. -/
theorem orbit_tape (j : Nat) (W : List Nat) (h : orbit j [6, 1] = some W) :
    ∃ t, steps t init = some (X (5 :: W) 0 []) := by
  obtain ⟨m, hm⟩ := orbit_reached j W h
  exact run_reached m _ _ _ hm

/-! ## In the order of `py/waves.py`

`waves.py` writes the blocks left to right, `P = (p_1, …, p_m)`, and reads N as binary digits. -/

/-- `N = 10 + Σ p_l 2^{m-l}`, by Horner's rule. -/
def bigNP (P : List Nat) : Nat := 10 + P.foldl (fun a p => 2 * a + p) 0

/-- `superstep` of `waves.py`: `P'` with the tape `[P', 5, 0]`, or `none` for a halt. -/
def superstep (P : List Nat) : Option (List Nat) := (superL P.reverse).map List.reverse

def orbitP : Nat → List Nat → Option (List Nat)
  | 0, P => some P
  | j + 1, P => (superstep P).bind (orbitP j)

theorem foldl_S : ∀ (P : List Nat) (x : Nat), P.foldl (fun a p => 2 * a + p) x = 2 ^ P.length * x + S P.reverse := by
  have hS : ∀ (A : List Nat) (q : Nat), S (A ++ [q]) = S A + 2 ^ A.length * q := by
    intro A q
    induction A with
    | nil => simp [S]
    | cons p A ih =>
      simp only [List.cons_append, S, ih, List.length_cons, Nat.pow_succ, Nat.mul_add]
      rw [Nat.mul_comm (2 ^ A.length) 2, Nat.mul_assoc]
      omega
  intro P
  induction P with
  | nil => intro x; simp [S]
  | cons q P ih =>
    intro x
    simp only [List.foldl_cons, ih, List.length_cons, List.reverse_cons, hS, List.length_reverse, Nat.pow_succ,
      Nat.mul_add]
    rw [Nat.mul_comm (2 ^ P.length) 2, Nat.mul_assoc, Nat.mul_left_comm (2 ^ P.length) 2 x]
    omega

theorem bigNP_eq (P : List Nat) : bigNP P = bigN P.reverse := by
  simp [bigNP, bigN, foldl_S]

theorem orbitP_eq : ∀ (j : Nat) (P : List Nat), orbitP j P = (orbit j P.reverse).map List.reverse := by
  intro j
  induction j with
  | zero => intro P; simp [orbitP, orbit]
  | succ j ih =>
    intro P
    simp only [orbitP, orbit, superstep]
    cases superL P.reverse with
    | none => rfl
    | some W => simp only [Option.map_some, Option.bind_some, ih, List.reverse_reverse]

/-- **The machine halts from blank tape iff N is ever a power of two**, in the order of `waves.py`: iff some `P` of
the super orbit from `(1, 6)` has `N = 10 + Σ p_l 2^{m-l}` a power of two. -/
theorem halts_iff_pow2' : HaltsFromBlank ↔ ∃ j P, orbitP j [1, 6] = some P ∧ ∃ a, bigNP P = 2 ^ a := by
  rw [halts_iff_pow2]
  constructor
  · rintro ⟨j, W, h₁, h₂⟩
    refine ⟨j, W.reverse, ?_, by rw [bigNP_eq, List.reverse_reverse]; exact h₂⟩
    rw [orbitP_eq]; simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [h₁]; rfl
  · rintro ⟨j, P, h₁, h₂⟩
    rw [orbitP_eq] at h₁
    cases e : orbit j [6, 1] with
    | none => simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h₁; rw [e] at h₁; cases h₁
    | some W =>
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h₁
      rw [e] at h₁
      cases h₁
      exact ⟨j, W, e, by rw [bigNP_eq] at h₂; simpa using h₂⟩

/-! Checks against `py/waves.py` (its docstring and the first super steps of `python3 waves.py super`). -/

example : superstep [1, 6] = some [4, 7, 8] := by decide
example : superstep [3, 4, 7] = some [3, 12, 11] := by decide
example : superstep [2, 2, 9, 4] = some [3, 6, 5, 8, 7] := by decide
example : bigNP [1, 6] = 18 := by decide

end BB6b
