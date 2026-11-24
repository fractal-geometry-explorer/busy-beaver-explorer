import ResetExc
import SymSim
import Std.Data.HashMap

/-!
# The carries of a phase, many at a time: Hashlife on the tail

`ResetExc.lean` checks a phase by running each of its about `X/4` carries (`cc Eg wg`: the tail excursion
`Exc [0,0,1,1] A D [0,0,1,0]`, then the cells `1010` in front) on the actual tail.  Past phase 36 that is too slow
(`X` grows by 3/2 per phase).  Here the carries are run in blocks of `2^j`:

* A **transform** `Tr` says what `n` carries do to every tail whose first runs have the words of `pat` and counts
  that are either fixed numbers or free variables (one per position): the tail becomes `out ++ rest` (`out` with
  counts linear in the variables, `rest` the untouched runs), under the linear conditions `conds`.  `Sound t` is
  this statement for every valuation satisfying the conditions and every rest of the tape (blank if `endB`); it is
  `Gen n` of `ResetMap.lean`, so the carries' excursions come back for every member of the family.
* `base`: one carry as a transform, by the symbolic excursion simulator of `SymSim.lean` (`base_sound`).
* `compose`: two transforms in a row, the second one's variables replaced by the first one's output counts
  (`compose_sound`).
* `get`: the transform of `2^j` carries at a tail, memoized by the words and small counts of its first runs
  (Hashlife over time).  The memo holds transforms together with their proofs, so a lookup needs no check beyond
  `matchT` (the transform fits the tail); which transform is tried when is unverified search.
* `genF_spec`, `cPhaseF_spec`, `cOrbitF_spec`: `m` carries, a phase, `k` phases in a row, proving `Gen`, `Good`,
  `GoodN`, as `cGen_spec` ... `cOrbit_spec` of `ResetExc.lean` do one carry at a time.
-/

namespace H129771

open TM TM.SX

/-! ## Tails with numbers as counts -/

/-- The valuation used for tails whose counts are constants (it is never read). -/
def env0 : Nat → Int := fun _ => 0

/-- The tape of a tail. -/
abbrev tp (s : SSide) : Tape := den env0 blank s

/-- A side of `ExcSim.lean` as a side with constant counts. -/
def toS (s : TM.Side) : SSide := s.map (fun p => (p.1, Lin.k p.2))

theorem den_toS (env : Nat → Int) (b : Tape) : ∀ s : TM.Side, den env b (toS s) = EX.dB b s
  | [] => rfl
  | (w, n) :: s => by
    have ih := den_toS env b s
    simp only [toS] at ih
    simp [toS, ih]

/-- The counts of `s` evaluated at `env`, as constants. -/
def inst (env : Nat → Int) (s : SSide) : SSide := s.map (fun p => (p.1, ⟨p.2.ev env, []⟩))

theorem den_inst (env env' : Nat → Int) (b : Tape) : ∀ s : SSide, den env' b (inst env s) = den env b s
  | [] => rfl
  | (w, n) :: s => by
    have ih := den_inst env env' b s
    simp only [inst] at ih ⊢
    simp only [List.map, SX.den_cons, ih]
    simp [Lin.cnt, Lin.ev, evT]

/-- Adjacent literal runs (count exactly 1) joined into one word, up to 32 cells (fewer runs to look at). -/
def packS : SSide → SSide
  | [] => []
  | (w, a) :: s =>
    match packS s with
    | (w', b) :: r =>
      if a = Lin.k 1 ∧ b = Lin.k 1 ∧ w.length + w'.length ≤ 32 then (w ++ w', Lin.k 1) :: r
      else (w, a) :: (w', b) :: r
    | [] => [(w, a)]

theorem den_packS (env : Nat → Int) (b : Tape) : ∀ s : SSide, den env b (packS s) = den env b s
  | [] => rfl
  | (w, a) :: s => by
    have ih := den_packS env b s
    simp only [packS]
    split
    · rename_i w' b' r e
      rw [e] at ih
      split
      · rename_i h
        obtain ⟨rfl, rfl, -⟩ := h
        simp only [SX.den_cons, Lin.cnt_k, rep_one] at ih ⊢
        rw [← ih, app_app]
      · simp only [SX.den_cons] at ih ⊢
        rw [ih]
    · rename_i e
      rw [e] at ih
      simp only [SX.den_cons] at ih ⊢
      rw [ih]

/-! ## Carries on symbolic tails -/

/-- A list of excursions in a row, then the cells `w` in front (`cc` of `ResetExc.lean`), on a symbolic side. -/
def ccS (e₀ : Nat → Int) (endB : Bool) : List Sig → List Bool → SSide → Option (SSide × List Lin)
  | [], w, T => some (SX.preL ws w T)
  | (u, q, q', v) :: es, w, T =>
    match SX.exc trans ws e₀ endB FUEL u q q' v T with
    | none => none
    | some (T1, c1) =>
      match ccS e₀ endB es w T1 with
      | none => none
      | some (T2, c2) => some (T2, c2 ++ c1)

theorem ccS_spec (e₀ : Nat → Int) (endB : Bool) : ∀ (es : List Sig) (w : List Bool) (T T' : SSide) (cs : List Lin),
    ccS e₀ endB es w T = some (T', cs) → ∀ env, Holds env cs → ∀ R, (endB = true → R = blank) →
    ∀ K : Tape → Prop, K (den env R T') → HC es w (den env R T) K
  | [], w, T, T', cs, h, env, hc, R, _, K, hK => by
    simp only [ccS, Option.some.injEq] at h
    show K (app w (den env R T))
    rw [← SX.preL_spec R ws T w (by rw [h]; exact hc)]
    rw [h]; exact hK
  | (u, q, q', v) :: es, w, T, T', cs, h, env, hc, R, hR, K, hK => by
    simp only [ccS] at h
    cases e1 : SX.exc trans ws e₀ endB FUEL u q q' v T with
    | none => rw [e1] at h; cases h
    | some p =>
      obtain ⟨T1, c1⟩ := p
      rw [e1] at h
      simp only at h
      cases e2 : ccS e₀ endB es w T1 with
      | none => rw [e2] at h; cases h
      | some p2 =>
        obtain ⟨T2, c2⟩ := p2
        rw [e2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, exc_spec trans ws e₀ endB FUEL u q q' v T T1 c1 e1 env hc.right R hR,
          ccS_spec e₀ endB es w T1 T2 c2 e2 env hc.left R hR K hK⟩

/-- `cc` on a tail with constant counts. -/
def ccC (es : List Sig) (w : List Bool) (T : SSide) : Option SSide :=
  match ccS env0 true es w T with
  | none => none
  | some (T', cs) => if cs.all (fun e => decide (0 ≤ e.ev env0)) then some (packS T') else none

theorem ccC_spec (es : List Sig) (w : List Bool) (T T' : SSide) (h : ccC es w T = some T') (K : Tape → Prop)
    (hK : K (tp T')) : HC es w (tp T) K := by
  unfold ccC at h
  cases e : ccS env0 true es w T with
  | none => rw [e] at h; cases h
  | some p =>
    obtain ⟨T2, cs⟩ := p
    rw [e] at h
    simp only at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      refine ccS_spec env0 true es w T T2 cs e env0 ?_ blank (fun _ => rfl) K (by unfold tp at hK; rwa [den_packS] at hK)
      intro x hx
      simp only [List.all_eq_true, decide_eq_true_eq] at hc
      exact hc x hx
    · cases h

/-! ## Monotonicity and composition of `Gen` -/

theorem HC_mono : ∀ (es : List Sig) (w : List Bool) (T : Tape) (K K' : Tape → Prop), (∀ x, K x → K' x) →
    HC es w T K → HC es w T K'
  | [], _, _, _, _, hk, h => hk _ h
  | (_, _, _, _) :: es, w, _, K, K', hk, ⟨T1, h1, h2⟩ => ⟨T1, h1, HC_mono es w T1 K K' hk h2⟩

theorem Gen_mono : ∀ (n : Nat) (T : Tape) (K K' : Tape → Prop), (∀ x, K x → K' x) → Gen n T K → Gen n T K'
  | 0, _, _, _, hk, h => hk _ h
  | n + 1, T, K, K', hk, h => by
    have h' : Hg T (fun T' => Gen n T' K) := h
    show Hg T _
    rw [Hg_eq] at h' ⊢
    have h := h'
    exact HC_mono Eg wg T _ _ (fun x hx => Gen_mono n x K K' hk hx) h

theorem Gen_add : ∀ (a b : Nat) (T : Tape) (K : Tape → Prop), Gen a T (fun T' => Gen b T' K) → Gen (a + b) T K
  | 0, b, T, K, h => by rw [Nat.zero_add]; exact h
  | a + 1, b, T, K, h => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    have h' : Hg T (fun T' => Gen a T' (fun T' => Gen b T' K)) := h
    show Hg T _
    rw [Hg_eq] at h' ⊢
    have h := h'
    exact HC_mono Eg wg T _ _ (fun x hx => Gen_add a b x K hx) h

/-! ## Transforms -/

/-- A run of a pattern: its word, and its count (`none`: the variable of its position; `some n`: exactly `n`). -/
abbrev Pat := List (List Bool × Option Nat)

def spec (i : Nat) : Option Nat → Lin
  | none => Lin.var i
  | some n => Lin.k n

/-- The pattern as a symbolic side, its first run at position `i`. -/
def patS (i : Nat) : Pat → SSide
  | [] => []
  | (w, sp) :: p => (w, spec i sp) :: patS (i + 1) p

theorem patS_append : ∀ (i : Nat) (p q : Pat), patS i (p ++ q) = patS i p ++ patS (i + p.length) q
  | i, [], q => by simp [patS]
  | i, (w, sp) :: p, q => by
    simp only [List.cons_append, patS, patS_append (i + 1) p q, List.length_cons]
    rw [show i + 1 + p.length = i + (p.length + 1) by omega]

structure Tr where
  pat : Pat
  endB : Bool
  out : SSide
  conds : List Lin
  n : Nat

/-- What `t` claims: `t.n` carries take every tail of the family to its `out`, the untouched rest `R` kept. -/
def Sound (t : Tr) : Prop :=
  ∀ env, Holds env t.conds → ∀ R, (t.endB = true → R = blank) → ∀ K : Tape → Prop,
    K (den env R t.out) → Gen t.n (den env R (patS 0 t.pat)) K

abbrev VTr := {t : Tr // Sound t}

/-! ### Conditions, simplified -/

/-- The least constant for each term list (unverified; checked by `simpC`). -/
def bestC (cs : List Lin) : Std.HashMap Terms Int :=
  cs.foldl (fun m e => if e.t.isEmpty then m else
    match m[e.t]? with
    | some c => if e.c < c then m.insert e.t e.c else m
    | none => m.insert e.t e.c) {}

/-- One condition per term list, the strongest, if that implies all of `cs` (checked); else `cs`. -/
def simpC (cs : List Lin) : List Lin :=
  let m := bestC cs
  if cs.all (fun e => (e.t.isEmpty && decide (0 ≤ e.c)) ||
      match m[e.t]? with
      | some c => decide (c ≤ e.c)
      | none => false)
  then m.toList.map (fun p => ⟨p.2, p.1⟩) else cs

theorem simpC_spec {env : Nat → Int} {cs : List Lin} (h : Holds env (simpC cs)) : Holds env cs := by
  unfold simpC at h
  simp only at h
  split at h
  · rename_i hall
    intro e he
    simp only [List.all_eq_true] at hall
    have := hall e he
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with ⟨h1, h2⟩ | h3
    · have : e.t = [] := List.isEmpty_iff.1 h1
      simp [Lin.ev, this, evT]; exact h2
    · cases e2 : (bestC cs)[e.t]? with
      | none => rw [e2] at h3; cases h3
      | some c =>
        rw [e2] at h3
        simp only [decide_eq_true_eq] at h3
        have hm : (e.t, c) ∈ (bestC cs).toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.2 e2
        have := h ⟨c, e.t⟩ (List.mem_map.2 ⟨(e.t, c), hm, rfl⟩)
        simp only [Lin.ev] at this ⊢
        omega
  · exact h

/-! ### Fitting a transform to a tail -/

def specOk : Option Nat → Lin → Bool
  | none, e => e.t.isEmpty
  | some n, e => decide (e = Lin.k n)

/-- The words and counts of `p` fit the first runs of `s`. -/
def matchP : Pat → SSide → Bool
  | [], _ => true
  | (w, sp) :: p, (w', e) :: s => decide (w = w') && specOk sp e && matchP p s
  | _ :: _, [] => false

/-- The valuation read off a tail: position `i` has the count of the `i`-th run. -/
def envOf (s : SSide) : Nat → Int :=
  let a := (s.map (fun p => p.2.c)).toArray
  fun i => a.getD i 0

theorem envOf_eq (s : SSide) (i : Nat) : envOf s i = (s.map (fun p => p.2.c)).getD i 0 := by
  simp [envOf]

theorem matchP_den (env : Nat → Int) (b : Tape) : ∀ (p : Pat) (s : SSide) (i : Nat), matchP p s = true →
    (∀ j, j < p.length → env (i + j) = (s.map (fun p => p.2.c)).getD j 0) →
    den env0 b s = den env (den env0 b (s.drop p.length)) (patS i p)
  | [], s, i, _, _ => by simp [patS]
  | (w, sp) :: p, [], i, h, _ => by simp [matchP] at h
  | (w, sp) :: p, (w', e) :: s, i, h, hE => by
    simp only [matchP, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hs⟩, hp⟩ := h
    simp only [patS, SX.den_cons, List.drop_succ_cons, List.length_cons]
    have ih := matchP_den env b p s (i + 1) hp (fun j hj => by
      have := hE (j + 1) (by simp; omega)
      rw [show i + 1 + j = i + (j + 1) by omega, this]
      simp)
    rw [← ih]
    congr 1
    have h0 := hE 0 (by simp)
    simp only [Nat.add_zero, List.map_cons, List.getD_cons_zero] at h0
    cases sp with
    | none =>
      simp only [specOk] at hs
      have : e.t = [] := List.isEmpty_iff.1 hs
      simp [spec, Lin.cnt, Lin.ev, Lin.var, this, evT, h0]
    | some n =>
      simp only [specOk, decide_eq_true_eq] at hs
      subst hs
      simp [spec]

/-- `t` fits the tail `s`. -/
def matchT (t : Tr) : SSide → Bool := fun s =>
  let env := envOf (s.take t.pat.length)
  matchP t.pat s && (!t.endB || decide (s.length = t.pat.length)) &&
    t.conds.all (fun e => decide (0 ≤ e.ev env))

/-- The tail after `t`. -/
def applyT (t : Tr) (s : SSide) : SSide := inst (envOf (s.take t.pat.length)) t.out ++ s.drop t.pat.length

theorem applyT_spec (t : VTr) (s : SSide) (h : matchT t.1 s = true) (K : Tape → Prop) (hK : K (tp (applyT t.1 s))) :
    Gen t.1.n (tp s) K := by
  simp only [matchT, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨hp, hb⟩, hc⟩ := h
  have hd := matchP_den (envOf (s.take t.1.pat.length)) blank t.1.pat s 0 hp (fun j hj => by
    rw [envOf_eq]; simp [List.getD_eq_getElem?_getD, List.getElem?_take, hj])
  unfold tp
  rw [hd]
  apply t.2 _ hc
  · intro he
    rcases hb with hb | hb
    · rw [hb] at he; cases he
    · rw [List.drop_of_length_le (by omega)]; rfl
  · unfold tp applyT at hK
    rw [den_append, den_inst] at hK
    exact hK

/-! ### One carry -/

/-- The count of a run as a pattern entry: a variable when it is at least `TH`. -/
def TH : Int := 4

def specOf (e : Lin) : Option Nat := if TH ≤ e.c then none else some e.c.toNat

def mkPat (s : SSide) : Pat := s.map (fun p => (p.1, specOf p.2))

/-- One carry on the first `L` runs of `s` as a transform (the family of tails with those words and small counts). -/
def baseAt (s : SSide) (L : Nat) : Option VTr :=
  let pat := mkPat (s.take L)
  let endB := decide (s.length ≤ L)
  match h : ccS (envOf (s.take L)) endB Eg wg (patS 0 pat) with
  | none => none
  | some (out, cs) => some ⟨⟨pat, endB, packS out, simpC cs, 1⟩, by
      intro env hc R hR K hK
      show Hg _ _
      rw [Hg_eq]
      exact ccS_spec (envOf (s.take L)) endB Eg wg _ out cs h env (simpC_spec hc) R hR K
        (by rwa [den_packS] at hK)⟩

/-- The runs at the end of `a` that are also at the end of `b` (the runs a carry did not touch). -/
def commonSuffix (a b : SSide) : Nat :=
  ((a.reverse.zip b.reverse).takeWhile (fun p => decide (p.1 = p.2))).length

/-- One carry at `s`: on the first 1, 2, 4, ... runs until the excursion stays inside them, then on only the runs it
read, if that works. -/
def base (s : SSide) : Nat → Nat → Option VTr
  | 0, _ => none
  | fuel + 1, L =>
    match baseAt s L with
    | some t =>
      let k := commonSuffix (patS 0 t.1.pat) t.1.out
      if 0 < k then
        match baseAt s (min L s.length - k) with
        | some t2 => if matchT t2.1 s then some t2 else some t
        | none => some t
      else some t
    | none => if s.length ≤ L then none else base s fuel (2 * L)

/-! ### Composition -/

/-- The substitution for the second transform's variables: the first one's output counts (or its own variables, past
the first one's output), with the conditions that the fixed counts of the second pattern hold. -/
def mkSub (L1 : Nat) : Pat → SSide → Nat → Option (List Lin × List Lin)
  | [], _, _ => some ([], [])
  | (w, sp) :: p, (w', e) :: o, k =>
    if w = w' then
      match mkSub L1 p o k with
      | none => none
      | some (ms, ex) =>
        match sp with
        | none => some (e :: ms, ex)
        | some n => some (Lin.k n :: ms, (e.addc (-(n : Int))) :: (e.addc (-(n : Int))).neg :: ex)
    else none
  | (_, sp) :: p, [], k =>
    match mkSub L1 p [] (k + 1) with
    | none => none
    | some (ms, ex) => some (spec (L1 + k) sp :: ms, ex)

def subOf (ms : List Lin) : Nat → Lin := fun v => ms.getD v ⟨0, []⟩

theorem mkSub_den (L1 : Nat) (env env2 : Nat → Int) (Rb : Tape) : ∀ (p : Pat) (o : SSide) (k i : Nat)
    (ms ex : List Lin), mkSub L1 p o k = some (ms, ex) → Holds env ex →
    (∀ j, j < p.length → env2 (i + j) = (ms.getD j ⟨0, []⟩).ev env) →
    den env (den env Rb (patS (L1 + k) (p.drop o.length))) o = den env2 (den env Rb (o.drop p.length)) (patS i p)
  | [], o, k, i, ms, ex, _, _, _ => by simp [patS]
  | (w, sp) :: p, (w', e) :: o, k, i, ms, ex, h, hx, hE => by
    simp only [mkSub] at h
    split at h
    · rename_i hw
      subst hw
      cases e1 : mkSub L1 p o k with
      | none => rw [e1] at h; cases h
      | some r =>
        obtain ⟨ms', ex'⟩ := r
        rw [e1] at h
        simp only [List.drop_succ_cons, List.length_cons, SX.den_cons, patS]
        cases sp with
        | none =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have h0 := hE 0 (by simp)
          simp only [Nat.add_zero, List.getD_cons_zero] at h0
          rw [mkSub_den L1 env env2 Rb p o k (i + 1) ms' ex' e1 hx (fun j hj => by
            have := hE (j + 1) (by simp; omega)
            rw [show i + 1 + j = i + (j + 1) by omega, this]; simp)]
          congr 1
          simp [spec, Lin.cnt, h0]
        | some n =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have ha : 0 ≤ (e.addc (-(n : Int))).ev env := hx _ (by simp)
          have hb : 0 ≤ (e.addc (-(n : Int))).neg.ev env := hx _ (by simp)
          have hx' : Holds env ex' := fun x hx2 => hx x (by simp [hx2])
          rw [mkSub_den L1 env env2 Rb p o k (i + 1) ms' ex' e1 hx' (fun j hj => by
            have := hE (j + 1) (by simp; omega)
            rw [show i + 1 + j = i + (j + 1) by omega, this]; simp)]
          congr 1
          simp only [Lin.ev_addc, Lin.ev_neg] at ha hb
          simp only [spec, Lin.cnt_k]
          simp only [Lin.cnt]
          omega
    · cases h
  | (w, sp) :: p, [], k, i, ms, ex, h, hx, hE => by
    simp only [mkSub] at h
    cases e1 : mkSub L1 p [] (k + 1) with
    | none => rw [e1] at h; cases h
    | some r =>
      obtain ⟨ms', ex'⟩ := r
      rw [e1] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := mkSub_den L1 env env2 Rb p [] (k + 1) (i + 1) ms' ex' e1 hx (fun j hj => by
        have := hE (j + 1) (by simp; omega)
        rw [show i + 1 + j = i + (j + 1) by omega, this]; simp)
      simp only [List.length_nil, List.drop_zero, SX.den_nil, List.drop_nil] at ih ⊢
      simp only [patS, SX.den_cons]
      rw [show L1 + (k + 1) = L1 + k + 1 by omega] at ih
      rw [ih]
      congr 1
      have h0 := hE 0 (by simp)
      simp only [Nat.add_zero, List.getD_cons_zero] at h0
      cases sp with
      | none => simp [spec, Lin.cnt, h0]
      | some n => simp [spec]

theorem den_subst (env : Nat → Int) (m : Nat → Lin) (b : Tape) : ∀ (o : SSide),
    den env b (o.map (fun p => (p.1, p.2.subst m))) = den (fun v => (m v).ev env) b o
  | [] => rfl
  | (w, e) :: o => by
    simp only [List.map, SX.den_cons, den_subst env m b o, Lin.cnt, Lin.ev_subst]

def compose (t1 t2 : Tr) : Option Tr :=
  let o := t1.out.length
  let L2 := t2.pat.length
  if t1.endB = true ∧ o < L2 then none else
  if t2.endB = true ∧ L2 < o then none else
  match mkSub t1.pat.length t2.pat t1.out 0 with
  | none => none
  | some (ms, ex) =>
    let m := subOf ms
    some ⟨t1.pat ++ t2.pat.drop o, t1.endB || t2.endB,
      packS (t2.out.map (fun p => (p.1, p.2.subst m)) ++ t1.out.drop L2),
      simpC (t1.conds ++ ex ++ t2.conds.map (Lin.subst m)), t1.n + t2.n⟩

theorem compose_sound (t1 t2 : VTr) (t : Tr) (h : compose t1.1 t2.1 = some t) : Sound t := by
  obtain ⟨t1, s1⟩ := t1
  obtain ⟨t2, s2⟩ := t2
  simp only [compose] at h
  split at h
  · cases h
  rename_i hn1
  split at h
  · cases h
  rename_i hn2
  cases e : mkSub t1.pat.length t2.pat t1.out 0 with
  | none => rw [e] at h; cases h
  | some r =>
    obtain ⟨ms, ex⟩ := r
    rw [e] at h
    simp only [Option.some.injEq] at h
    subst h
    intro env hc R hR K hK
    have hc' := simpC_spec hc
    have hc1 := hc'.left.left
    have hcx := hc'.left.right
    have hc2 : Holds (fun v => (subOf ms v).ev env) t2.conds := by
      intro x hx
      have := hc'.right _ (List.mem_map.2 ⟨x, hx, rfl⟩)
      rwa [Lin.ev_subst] at this
    simp only [Bool.or_eq_true] at hR
    simp only at hK ⊢
    -- the pattern: t1's, then t2's runs past t1's output
    rw [patS_append, den_append]
    apply Gen_add
    apply s1 env hc1
    · intro h1
      have : t2.pat.length ≤ t1.out.length := by
        by_cases hh : t1.out.length < t2.pat.length
        · exact absurd ⟨h1, hh⟩ hn1
        · omega
      rw [List.drop_of_length_le this]
      simp only [patS, SX.den_nil]
      exact hR (Or.inl h1)
    · have hm := mkSub_den t1.pat.length env (fun v => (subOf ms v).ev env) R t2.pat t1.out 0 0 ms ex e hcx
        (fun j _ => by simp [subOf])
      simp only [Nat.add_zero] at hm
      rw [Nat.zero_add, hm]
      apply s2 _ hc2
      · intro h2
        have : t1.out.length ≤ t2.pat.length := by
          by_cases hh : t2.pat.length < t1.out.length
          · exact absurd ⟨h2, hh⟩ hn2
          · omega
        rw [List.drop_of_length_le this]
        exact hR (Or.inr h2)
      · rw [den_packS, den_append, den_subst] at hK
        exact hK

/-! ## Hashlife over the carries -/

/-- Memo keys: level, number of runs, a hash of their words and small counts, whether they are all of the tail. -/
abbrev Key := Nat × Nat × UInt64 × Bool

structure Memo where
  m : Std.HashMap Key (List VTr) := {}
  ls : Std.HashMap Nat (List Nat) := {}
  size : Nat := 0

/-- The hashes of the first `0, 1, ..., n` runs of `s` (their words and `specOf` counts). -/
def phashes (s : SSide) (n : Nat) : Array UInt64 := Id.run do
  let mut h : UInt64 := 7
  let mut a : Array UInt64 := #[h]
  let mut r := s
  for _ in [0:n] do
    match r with
    | [] => break
    | p :: r' =>
      h := mixHash h (hash (p.1, specOf p.2))
      a := a.push h
      r := r'
  return a

/-- A memoized transform of level `j` that fits `s` (unverified search; `matchT` is checked when it is applied). -/
def look (M : Memo) (j : Nat) (s : SSide) : Option VTr :=
  let Ls := M.ls.getD j []
  let H := phashes s (Ls.foldl max 0)
  let n := s.length
  Ls.findSome? fun L =>
    if h : L < H.size then
      (M.m.getD (j, L, H[L], decide (n ≤ L)) []).find? (fun t => matchT t.1 s)
    else none

def store (M : Memo) (j : Nat) (s : SSide) (t : VTr) : Memo :=
  let L := t.1.pat.length
  let H := phashes s L
  let k : Key := (j, L, H.getD L 0, decide (s.length ≤ L))
  let ls := M.ls.getD j []
  { m := M.m.insert k (t :: M.m.getD k []),
    ls := if ls.contains L then M.ls else M.ls.insert j (L :: ls),
    size := M.size + 1 }

def BFUEL : Nat := 24

/-- The transform of `2^j` carries at `s`. -/
def get : Nat → SSide → Memo → Option (VTr × Memo)
  | 0, s, M =>
    match look M 0 s with
    | some t => some (t, M)
    | none =>
      match base s BFUEL 1 with
      | none => none
      | some t => some (t, store M 0 s t)
  | j + 1, s, M =>
    match look M (j + 1) s with
    | some t => some (t, M)
    | none =>
      match get j s M with
      | none => none
      | some (t1, M1) =>
        if matchT t1.1 s then
          match get j (applyT t1.1 s) M1 with
          | none => none
          | some (t2, M2) =>
            match h : compose t1.1 t2.1 with
            | none => none
            | some t => some (⟨t, compose_sound t1 t2 t h⟩, store M2 (j + 1) s ⟨t, compose_sound t1 t2 t h⟩)
        else none

/-- The largest `j ≤ 62` with `2^j ≤ m` (for `m ≥ 1`). -/
def lvl (m : Nat) : Nat := min (m.log2) 62

/-- The memo is emptied when it holds more than this many transforms. -/
def LIMIT : Nat := 400000

/-- `m` carries from `s`, `fuel` chunks at most. -/
def genF : Nat → Nat → SSide → Memo → Option (SSide × Memo)
  | _, 0, s, M => some (s, M)
  | 0, _ + 1, _, _ => none
  | fuel + 1, m + 1, s, M =>
    let M := if LIMIT < M.size then {} else M
    match get (lvl (m + 1)) s M with
    | none => none
    | some (t, M1) =>
      if matchT t.1 s ∧ 1 ≤ t.1.n ∧ t.1.n ≤ m + 1 then genF fuel (m + 1 - t.1.n) (applyT t.1 s) M1 else none

theorem genF_spec : ∀ (fuel m : Nat) (s s' : SSide) (M M' : Memo), genF fuel m s M = some (s', M') →
    ∀ K : Tape → Prop, K (tp s') → Gen m (tp s) K
  | _, 0, s, s', M, M', h, K, hK => by
    cases ‹Nat› <;> (simp only [genF, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact hK)
  | 0, _ + 1, _, _, _, _, h, _, _ => by simp [genF] at h
  | fuel + 1, m + 1, s, s', M, M', h, K, hK => by
    simp only [genF] at h
    split at h
    · cases h
    · rename_i t M1 _
      split at h
      · rename_i hc
        obtain ⟨hm, h1, h2⟩ := hc
        have := genF_spec fuel (m + 1 - t.1.n) _ s' M1 M' h K hK
        have e : m + 1 = t.1.n + (m + 1 - t.1.n) := by omega
        rw [e]
        exact Gen_add _ _ _ _ (applyT_spec t s hm _ this)
      · cases h

/-! ## Phases -/

def cEndF (e : Nat) (T : SSide) : Option SSide := if e % 2 = 0 then ccC Eg we0 T else ccC Ee1 we1 T

theorem cEndF_spec (e : Nat) (T T' : SSide) (K : Tape → Prop) (h : cEndF e T = some T') (hK : K (tp T')) :
    Hend e (tp T) K := by
  unfold cEndF at h
  unfold Hend
  split
  · rename_i he; simp only [he, ↓reduceIte] at h; rw [He0_eq]; exact ccC_spec _ _ _ _ h K hK
  · rename_i he; simp only [he, ↓reduceIte] at h; rw [He1_eq]; exact ccC_spec _ _ _ _ h K hK

/-- A whole phase from `Reset X`, the carries by Hashlife. -/
def cPhaseF (X : Nat) (T : SSide) (M : Memo) : Option (SSide × Memo) :=
  let r := if X % 2 = 0 then (ccC Ere wre T, X / 2 - 18 + 11) else (ccC Ero wro T, X / 2 - 18 + 12)
  match r.1 with
  | none => none
  | some T1 =>
    match genF (r.2 / 2 + 1) (r.2 / 2) T1 M with
    | none => none
    | some (T2, M2) =>
      match cEndF r.2 T2 with
      | none => none
      | some T3 => some (T3, M2)

theorem cPhaseF_spec (X : Nat) (T T' : SSide) (M M' : Memo) (h : cPhaseF X T M = some (T', M')) (K : Tape → Prop)
    (hK : K (tp T')) : Good X (tp T) K := by
  unfold cPhaseF at h
  unfold Good
  split
  · rename_i hp
    simp only [hp, ↓reduceIte] at h
    rw [Hre_eq]
    cases e1 : ccC Ere wre T with
    | none => rw [e1] at h; cases h
    | some T1 =>
      rw [e1] at h
      simp only at h
      cases e2 : genF ((X / 2 - 18 + 11) / 2 + 1) ((X / 2 - 18 + 11) / 2) T1 M with
      | none => rw [e2] at h; cases h
      | some p =>
        obtain ⟨T2, M2⟩ := p
        rw [e2] at h
        simp only at h
        cases e3 : cEndF (X / 2 - 18 + 11) T2 with
        | none => rw [e3] at h; cases h
        | some T3 =>
          rw [e3] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact ccC_spec _ _ _ _ e1 _ (genF_spec _ _ _ _ _ _ e2 _ (cEndF_spec _ _ _ K e3 hK))
  · rename_i hp
    simp only [hp, ↓reduceIte] at h
    rw [Hro_eq]
    cases e1 : ccC Ero wro T with
    | none => rw [e1] at h; cases h
    | some T1 =>
      rw [e1] at h
      simp only at h
      cases e2 : genF ((X / 2 - 18 + 12) / 2 + 1) ((X / 2 - 18 + 12) / 2) T1 M with
      | none => rw [e2] at h; cases h
      | some p =>
        obtain ⟨T2, M2⟩ := p
        rw [e2] at h
        simp only at h
        cases e3 : cEndF (X / 2 - 18 + 12) T2 with
        | none => rw [e3] at h; cases h
        | some T3 =>
          rw [e3] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact ccC_spec _ _ _ _ e1 _ (genF_spec _ _ _ _ _ _ e2 _ (cEndF_spec _ _ _ K e3 hK))

/-- `k` phases in a row from `Reset X`. -/
def cOrbitF : Nat → Nat → SSide → Memo → Bool
  | 0, _, _, _ => true
  | k + 1, X, T, M =>
    match cPhaseF X T M with
    | none => false
    | some (T', M') => cOrbitF k (f X) T' M'

theorem cOrbitF_spec : ∀ (k X : Nat) (T : SSide) (M : Memo), cOrbitF k X T M = true → GoodN k X (tp T)
  | 0, _, _, _, _ => trivial
  | k + 1, X, T, M, h => by
    simp only [cOrbitF] at h
    cases e : cPhaseF X T M with
    | none => rw [e] at h; cases h
    | some p =>
      obtain ⟨T', M'⟩ := p
      rw [e] at h
      exact cPhaseF_spec X T T' M M' e _ (cOrbitF_spec k (f X) T' M' h)

/-- From a reset reached after `N` steps, `k` checked phases reach the reset of `fit k X`. -/
theorem reach_of_checkF {c : Config} {N X : Nat} {T : SSide} (hX : 36 ≤ X) (h0 : steps N c = some (Reset X (tp T)))
    (k : Nat) (h : cOrbitF k X T {} = true) : ∃ n T', N + k ≤ n ∧ steps n c = some (Reset (fit k X) T') := by
  obtain ⟨m, T', hm, hs⟩ := orbit k X _ hX (cOrbitF_spec k X T {} h)
  exact ⟨N + m, T', by omega, steps_seq trans h0 hs⟩

theorem T0own_tp : T0own = tp (toS (EX.ofList ws L0own)) := by
  rw [T0own_eq]; unfold tp; rw [den_toS]

theorem T0twin_tp : T0twin = tp (toS (EX.ofList ws L0twin)) := by
  rw [T0twin_eq]; unfold tp; rw [den_toS]

/-- A run for measuring (not used in proofs): phases done, and `X` reached. -/
def progress : Nat → Nat → SSide → Memo → Nat → Nat × Nat
  | 0, X, _, _, d => (d, X)
  | k + 1, X, T, M, d =>
    match cPhaseF X T M with
    | none => (d, X)
    | some (T', M') => progress k (f X) T' M' (d + 1)

end H129771
