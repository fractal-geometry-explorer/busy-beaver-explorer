import Machine
import Tick

/-!
# 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB: a checker for long runs from blank tape

A certificate is a list of operations on a configuration kept as two lists (`FCfg`):

* `D n`: `n` plain steps (`fsteps`);
* `L m gs`, `R m gs`: change the layout of the left / right counter (keep the first `m` gap lengths, then `gs`);
* `B d`: `d` ticks of the two counters at once.  The head must be on the base cell, a 0, in state A.  The left list
  is cut by the layout into a first gap and digit pairs with their gaps, the right list (after the base cell) into a
  first gap and single digits with their gaps, and both cuts are checked by rebuilding the lists.  The two sides of
  one tick are then run on windows for every carry length (`Lay.winL`, `Lay.winR`), each must follow the arrivals at
  the base cell of a reference tick (`proto`) and end with its digits incremented, and `TM.batch` turns that into `d`
  ticks with the step count `csum Gs a d + csum Fs b d`.

`run_sound`: whatever the certificate, a successful check is a run of the machine of that many steps.  Nothing in
the soundness proof depends on how the certificate was made (`py/gencert.py`, from the batches of `py/accel.py`).
-/

namespace H56057

open TM

/-- The step budget of one window run (never reached by the certificate). -/
def fuel : Nat := 10000000

/-- Cut the cells after the first gap into digits (`w` cells each) and their gaps; the last gap is the rest. -/
def splitB (w : Nat) : List Nat → List Bool → List (List Bool) × List Bool
  | [], xs => ([xs.drop w], [xs.headD false])
  | g :: gs, xs =>
    let ys := xs.drop w
    let r := splitB w gs (ys.drop g)
    (ys.take g :: r.1, xs.headD false :: r.2)

/-- The value of a list of bits, least significant first. -/
def bval : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bval bs

/-- A side cut by a layout `g0 :: gaps`: its first gap, its digit blocks and the counter's value. -/
def cutSide (w : Nat) (lay : List Nat) (xs : List Bool) : Option (List Bool × List (List Bool) × Nat) :=
  match lay with
  | [] => none
  | g0 :: gs =>
    let r := splitB w gs (xs.drop g0)
    some (xs.take g0, r.1, bval r.2)

/-- The arrivals at the base cell in one tick with both counters at 0 (the reference for all carry lengths). -/
def proto : Nat → List Bool → List Bool → St → Bool → Option (List (St × Bool))
  | 0, _, _, _, _ => none
  | n + 1, WL, WR, q, v =>
    if goesR trans q v then
      match excR trans fuel .A WR q v with
      | some (_, WR', v', q') =>
        if q' = .A ∧ v' = false then some [(q', v')] else (proto n WL WR' q' v').map ((q', v') :: ·)
      | none => none
    else if goesL trans q v then
      match excL trans fuel .A WL q v with
      | some (_, WL', v', q') =>
        if q' = .A ∧ v' = false then some [(q', v')] else (proto n WL' WR q' v').map ((q', v') :: ·)
      | none => none
    else none

/-- `[f k, ..., f (k + n - 1)]` if all are defined. -/
def collect (f : Nat → Option Nat) : Nat → Nat → Option (List Nat)
  | _, 0 => some []
  | k, n + 1 =>
    match f k with
    | none => none
    | some g => (collect f (k + 1) n).map (g :: ·)

theorem collect_spec (f : Nat → Option Nat) :
    ∀ n k Gs, collect f k n = some Gs → ∀ i, i < n → f (k + i) = some (Gs.getD i 0) := by
  intro n
  induction n with
  | zero => intro k Gs _ i hi; omega
  | succ n ih =>
    intro k Gs h i hi
    simp only [collect] at h
    cases hf : f k with
    | none => rw [hf] at h; cases h
    | some g =>
      rw [hf] at h
      cases hc : collect f (k + 1) n with
      | none => rw [hc] at h; cases h
      | some Gs' =>
        rw [hc] at h
        cases h
        cases i with
        | zero => simpa using hf
        | succ i =>
          have := ih (k + 1) Gs' hc i (by omega)
          rw [show k + (i + 1) = k + 1 + i by omega, this]
          simp

/-! ## The sides of a tick for every carry length, with a cache -/

/-- The window of one side up to digit `k` and its gap, its low digits set to `n` (`p`: pair digits, the left). -/
def winS (p : Bool) (g0 : List Bool) (gs : List (List Bool)) (k n : Nat) : List Bool :=
  g0 ++ layD p (gs.take (k + 1)) n

/-- The side checked for carry length `k`: from `2^k - 1` to `2^k` in its low digits, in `c` steps. -/
def okS (p : Bool) (P : List (St × Bool)) (g0 : List Bool) (gs : List (List Bool)) (k c : Nat) : Prop :=
  side trans .A (!p) fuel P (winS p g0 gs k (2 ^ k - 1)) .A false = some (c, winS p g0 gs k (2 ^ k))

def fS (p : Bool) (P : List (St × Bool)) (g0 : List Bool) (gs : List (List Bool)) (k : Nat) : Option Nat :=
  match side trans .A (!p) fuel P (winS p g0 gs k (2 ^ k - 1)) .A false with
  | some (g, W) => if W = winS p g0 gs k (2 ^ k) then some g else none
  | none => none

theorem fS_spec {p : Bool} {P : List (St × Bool)} {g0 : List Bool} {gs : List (List Bool)} {k g : Nat}
    (h : fS p P g0 gs k = some g) : okS p P g0 gs k g := by
  unfold fS at h
  split at h
  · rename_i g' W hs
    by_cases hw : W = winS p g0 gs k (2 ^ k)
    · rw [ite_eq_left hw] at h; cases h; unfold okS; rw [hs, hw]
    · rw [ite_eq_right hw] at h; cases h
  · cases h

/-- The checked carry lengths of the last layout of one side, reused while the layout keeps its first blocks. -/
structure SCache where
  g0 : List Bool
  P : List (St × Bool)
  gs : List (List Bool)
  cs : List Nat

def SCache.Valid (p : Bool) (C : SCache) : Prop := ∀ k, k < C.gs.length → okS p C.P C.g0 C.gs k (C.cs.getD k 0)

def SCache.empty : SCache := ⟨[], [], [], []⟩

theorem SCache.empty_valid (p : Bool) : SCache.empty.Valid p := fun k hk => by simp [SCache.empty] at hk

/-- The length of the common prefix. -/
def cpl : List (List Bool) → List (List Bool) → Nat
  | x :: xs, y :: ys => if x = y then cpl xs ys + 1 else 0
  | _, _ => 0

theorem cpl_take : ∀ (xs ys : List (List Bool)) (k : Nat), k ≤ cpl xs ys → xs.take k = ys.take k := by
  intro xs
  induction xs with
  | nil => intro ys k h; simp [cpl] at h; subst h; rfl
  | cons x xs ih =>
    intro ys k h
    cases ys with
    | nil => simp [cpl] at h; subst h; rfl
    | cons y ys =>
      simp only [cpl] at h
      by_cases e : x = y
      · rw [ite_eq_left e] at h
        cases k with
        | zero => rfl
        | succ k => simp only [List.take_succ_cons, e, ih ys k (by omega)]
      · rw [ite_eq_right e] at h; have : k = 0 := by omega
        subst this; rfl

theorem cpl_le : ∀ (xs ys : List (List Bool)), cpl xs ys ≤ xs.length := by
  intro xs
  induction xs with
  | nil => intro ys; simp [cpl]
  | cons x xs ih =>
    intro ys
    cases ys with
    | nil => simp [cpl]
    | cons y ys =>
      simp only [cpl, List.length_cons]
      split
      · have := ih ys; omega
      · omega

theorem getD_app_left : ∀ (l l' : List Nat) (k : Nat), k < l.length → (l ++ l').getD k 0 = l.getD k 0 := by
  intro l; induction l with
  | nil => intro l' k h; simp at h
  | cons a l ih => intro l' k h; cases k with
    | zero => rfl
    | succ k => simp only [List.cons_append, List.getD_cons_succ]; exact ih l' k (by simp at h; omega)

theorem getD_app_right : ∀ (l l' : List Nat) (k : Nat), l.length ≤ k → (l ++ l').getD k 0 = l'.getD (k - l.length) 0 := by
  intro l; induction l with
  | nil => intro l' k _; simp
  | cons a l ih => intro l' k h; cases k with
    | zero => simp at h
    | succ k =>
      simp only [List.cons_append, List.getD_cons_succ, List.length_cons]
      rw [ih l' k (by simp at h; omega)]; congr 1; omega

theorem getD_take : ∀ (l : List Nat) (m k : Nat), k < m → (l.take m).getD k 0 = l.getD k 0 := by
  intro l; induction l with
  | nil => intro m k _; simp
  | cons a l ih => intro m k h; cases m with
    | zero => omega
    | succ m => cases k with
      | zero => rfl
      | succ k => simp only [List.take_succ_cons, List.getD_cons_succ]; exact ih m k (by omega)

/-- The costs of all carry lengths of a side: those of the cache on the common first blocks, the rest checked. -/
def costsS (p : Bool) (C : SCache) (P : List (St × Bool)) (g0 : List Bool) (gs : List (List Bool)) :
    Option (List Nat) :=
  let m := if C.g0 = g0 ∧ C.P = P then min (cpl C.gs gs) C.cs.length else 0
  (collect (fS p P g0 gs) m (gs.length - m)).map (C.cs.take m ++ ·)

theorem costsS_spec {p : Bool} {C : SCache} {P : List (St × Bool)} {g0 : List Bool} {gs : List (List Bool)}
    {cs : List Nat} (hC : C.Valid p) (h : costsS p C P g0 gs = some cs) :
    ∀ k, k < gs.length → okS p P g0 gs k (cs.getD k 0) := by
  unfold costsS at h
  dsimp only at h
  generalize hm : (if C.g0 = g0 ∧ C.P = P then min (cpl C.gs gs) C.cs.length else 0) = m at h
  cases hc : collect (fS p P g0 gs) m (gs.length - m) with
  | none => rw [hc] at h; cases h
  | some rest =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    intro k hk
    have hlen : (C.cs.take m).length = m := by
      rw [List.length_take]; split at hm <;> omega
    by_cases hkm : k < m
    · have hg : C.g0 = g0 ∧ C.P = P := by
        by_cases e : C.g0 = g0 ∧ C.P = P
        · exact e
        · rw [ite_eq_right e] at hm; omega
      rw [ite_eq_left hg] at hm
      obtain ⟨e1, e2⟩ := hg
      have hk' : k + 1 ≤ cpl C.gs gs := by omega
      have ht := cpl_take C.gs gs (k + 1) hk'
      have hkC : k < C.gs.length := by have := cpl_le C.gs gs; omega
      have := hC k hkC
      rw [getD_app_left _ _ _ (by omega), getD_take _ _ _ hkm]
      unfold okS winS at this ⊢
      rw [← e1, ← e2, ← ht]
      exact this
    · rw [getD_app_right _ _ _ (by omega), hlen]
      have := collect_spec _ _ _ _ hc (k - m) (by omega)
      rw [show m + (k - m) = k by omega] at this
      exact fS_spec this

/-- `d` ticks from a configuration at the base cell, with the layouts `layL`, `layR` and the caches of the last
checked layouts (returned updated). -/
def batchOp (c : FCfg St) (layL layR : List Nat) (d : Nat) (CL CR : SCache) :
    Option (FCfg St × Nat × SCache × SCache) :=
  match c with
  | ⟨l, false :: rr, .A⟩ =>
    match cutSide 2 layL l, cutSide 1 layR rr with
    | some (g0L, gsL, a), some (g0R, gsR, b) =>
      if g0L ++ layD true gsL a = l ∧ g0R ++ layD false gsR b = rr ∧ a + d < 2 ^ gsL.length ∧
          b + d < 2 ^ gsR.length then
        match proto 64 (winS true g0L gsL 0 0) (winS false g0R gsR 0 0) .A false with
        | none => none
        | some P =>
          if lastA (St.A, false) P = (St.A, false) then
            match costsS true CL P g0L gsL, costsS false CR P g0R gsR with
            | some Gs, some Fs =>
              some ((Lay.cfg ⟨g0L, gsL, g0R, gsR⟩ .A (a + d) (b + d)), csum Gs a d + csum Fs b d,
                ⟨g0L, P, gsL, Gs⟩, ⟨g0R, P, gsR, Fs⟩)
            | _, _ => none
          else none
      else none
    | _, _ => none
  | _ => none

theorem batchOp_sound {c c' : FCfg St} {layL layR : List Nat} {d n : Nat} {CL CR CL' CR' : SCache}
    (hL0 : CL.Valid true) (hR0 : CR.Valid false)
    (h : batchOp c layL layR d CL CR = some (c', n, CL', CR')) :
    steps n c.toCfg = some c'.toCfg ∧ CL'.Valid true ∧ CR'.Valid false := by
  unfold batchOp at h
  split at h
  · rename_i l rr
    split at h
    · rename_i g0L gsL a g0R gsR b _ _
      split at h
      · rename_i hc
        obtain ⟨e1, e2, ha, hb⟩ := hc
        split at h
        · cases h
        · rename_i P _
          split at h
          · rename_i hP
            split at h
            · rename_i Gs Fs hG hF
              cases h
              have hL := costsS_spec hL0 hG
              have hR := costsS_spec hR0 hF
              refine ⟨?_, hL, hR⟩
              have := TM.batch trans ⟨g0L, gsL, g0R, gsR⟩ St.A fuel P Gs Fs hP hL hR a b d ha hb
              have ec : (⟨l, false :: rr, St.A⟩ : FCfg St) = Lay.cfg ⟨g0L, gsL, g0R, gsR⟩ St.A a b := by
                simp only [Lay.cfg, e1, e2]
              rw [ec]
              exact this
            · cases h
          · cases h
      · cases h
    · cases h
  · cases h

/-- The operations of a certificate. -/
inductive Op where
  | D (n : Nat)
  | L (m : Nat) (gs : List Nat)
  | R (m : Nat) (gs : List Nat)
  | B (d : Nat)

/-- Run the operations from `c`; `acc` counts the steps. -/
def run : List Op → FCfg St → List Nat → List Nat → SCache → SCache → Nat → Option (FCfg St × Nat)
  | [], c, _, _, _, _, acc => some (c, acc)
  | .D n :: ops, c, lL, lR, CL, CR, acc =>
    match fsteps n c with
    | some c' => run ops c' lL lR CL CR (acc + n)
    | none => none
  | .L m gs :: ops, c, lL, lR, CL, CR, acc => run ops c (lL.take m ++ gs) lR CL CR acc
  | .R m gs :: ops, c, lL, lR, CL, CR, acc => run ops c lL (lR.take m ++ gs) CL CR acc
  | .B d :: ops, c, lL, lR, CL, CR, acc =>
    match batchOp c lL lR d CL CR with
    | some (c', n, CL', CR') => run ops c' lL lR CL' CR' (acc + n)
    | none => none

theorem run_sound : ∀ (ops : List Op) (c : FCfg St) (lL lR : List Nat) (CL CR : SCache) (acc : Nat)
    (c' : FCfg St) (m : Nat), CL.Valid true → CR.Valid false →
    run ops c lL lR CL CR acc = some (c', m) → ∃ k, m = acc + k ∧ steps k c.toCfg = some c'.toCfg := by
  intro ops
  induction ops with
  | nil =>
    intro c lL lR CL CR acc c' m _ _ h
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨0, by omega, rfl⟩
  | cons op ops ih =>
    intro c lL lR CL CR acc c' m hCL hCR h
    cases op with
    | D n =>
      simp only [run] at h
      cases hs : fsteps n c with
      | none => rw [hs] at h; cases h
      | some c1 =>
        rw [hs] at h
        obtain ⟨k, hk, hr⟩ := ih c1 lL lR CL CR (acc + n) c' m hCL hCR h
        have h1 : steps n c.toCfg = some c1.toCfg := by
          show TM.steps trans n c.toCfg = _
          rw [FCfg.steps_eq]; exact congrArg (Option.map FCfg.toCfg) hs
        exact ⟨n + k, by omega, steps_seq trans h1 hr⟩
    | L m' gs => exact ih c _ lR CL CR acc c' m hCL hCR h
    | R m' gs => exact ih c lL _ CL CR acc c' m hCL hCR h
    | B d =>
      simp only [run] at h
      cases hb : batchOp c lL lR d CL CR with
      | none => rw [hb] at h; cases h
      | some t =>
        obtain ⟨c1, n, CL', CR'⟩ := t
        rw [hb] at h
        obtain ⟨hs, hL', hR'⟩ := batchOp_sound hCL hCR hb
        obtain ⟨k, hk, hr⟩ := ih c1 lL lR CL' CR' (acc + n) c' m hL' hR' h
        exact ⟨n + k, by omega, steps_seq trans hs hr⟩

/-! ## Reading a certificate -/

/-- Numbers up to the token `;`, and the tokens after it. -/
def readNats : List String → List Nat → Option (List Nat × List String)
  | [], _ => none
  | t :: ts, acc => if t = ";" then some (acc.reverse, ts) else
      match t.toNat? with
      | some n => readNats ts (n :: acc)
      | none => none

def parseOps : Nat → List String → List Op → Option (List Op)
  | 0, _, _ => none
  | _, [], acc => some acc.reverse
  | f + 1, t :: ts, acc =>
    if t = "D" ∨ t = "B" then
      match ts with
      | u :: us =>
        match u.toNat? with
        | some n => parseOps f us ((if t = "D" then Op.D n else Op.B n) :: acc)
        | none => none
      | [] => none
    else if t = "L" ∨ t = "R" then
      match ts with
      | u :: us =>
        match u.toNat?, readNats us [] with
        | some m, some (gs, rest) => parseOps f rest ((if t = "L" then Op.L m gs else Op.R m gs) :: acc)
        | _, _ => none
      | [] => none
    else none

def parse (s : String) : Option (List Op) :=
  let ts := ((s.splitOn "\n").flatMap (·.splitOn " ")).filter (fun t => !t.isEmpty)
  parseOps (ts.length + 1) ts []

/-- Check a certificate from blank tape: the number of steps it reaches. -/
def checkCert (s : String) : Option Nat :=
  match parse s with
  | some ops => (run ops (FCfg.blank .A) [] [] .empty .empty 0).map Prod.snd
  | none => none

theorem checkCert_sound {s : String} {N : Nat} (h : checkCert s = some N) : ∃ c, steps N init = some c := by
  unfold checkCert at h
  split at h
  · rename_i ops _
    cases hr : run ops (FCfg.blank .A) [] [] .empty .empty 0 with
    | none => rw [hr] at h; cases h
    | some t =>
      obtain ⟨c, m⟩ := t
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨k, hk, hs⟩ := run_sound ops _ [] [] _ _ 0 c m (SCache.empty_valid _) (SCache.empty_valid _) hr
      rw [show m = k by omega]
      exact ⟨_, hs⟩
  · cases h

end H56057
