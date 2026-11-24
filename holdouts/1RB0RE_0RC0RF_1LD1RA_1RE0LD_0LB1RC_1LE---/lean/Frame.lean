import Advance

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: frames — what a stretch of the run does not read

A sub-round of the pass machine reads only the first two blocks on its left and the first two gaps of the zone at
each move; a step of the counter reads the zone only up to the first gap that is not 3; and the time left `T` of a
list `F ++ X` is `T F + 2^(σ F) T X`.  So a stretch of the run computed on a *prefix* — the blocks nearest the head
`F` and the first gaps `Z` — holds for every tape further out, as long as no move needed a cell beyond the prefix.
The checked versions here (`subsF`, `gfastF`) return `none` when they would; their soundness theorems
(`subsF_frame`, `gfastF_frame`, `T_append`) turn a computation on the prefix into a theorem for all `X` and `R`.
-/

namespace H4320

open TM

/-! ## The pass machine -/

def PS.app (s : PS) (X R : List Nat) : PS := ⟨s.lb ++ X, s.ph, s.k, s.us ++ R⟩

def Res.app (X R : List Nat) : Res → Res
  | .next s n => .next (s.app X R) n
  | .done bs l us n => .done (bs ++ X) l (us ++ R) n
  | .halt => .halt

def Out.app (X R : List Nat) : Out → Out
  | .moment bs l us n => .moment (bs ++ X) l (us ++ R) n
  | o => o

/-- At least two entries (checked in constant time). -/
def two : List Nat → Bool
  | _ :: _ :: _ => true
  | _ => false

theorem two_iff : ∀ l : List Nat, two l = true ↔ 2 ≤ l.length
  | [] => by simp [two]
  | [_] => by simp [two]
  | _ :: _ :: _ => by simp [two]

/-- A move reads no block or gap beyond the prefix: two blocks on the left, and two gaps when no 1 is left to read. -/
def safe (s : PS) : Bool := two s.lb && (s.k != 0 || two s.us)

theorem rd_app (u : Nat) (us R : List Nat) : rd ((u :: us) ++ R) = rd (u :: us) ++ R := by
  cases u <;> rfl

theorem pstep_frame (s : PS) (X R : List Nat) (h : safe s = true) : pstep (s.app X R) = (pstep s).app X R := by
  obtain ⟨lb, ph, k, us⟩ := s
  simp only [safe, Bool.and_eq_true, two_iff, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hl, hk⟩ := h
  match lb, hl with
  | a :: b :: lb, _ =>
  match ph, k, us, hk with
  | .A, k + 3, us, _ =>
    simp only [PS.app, pstep, Res.app, List.cons_append, List.append_assoc]
  | .A, 1, us, _ => simp only [PS.app, pstep, Res.app, List.cons_append]
  | .A, 2, us, _ => simp only [PS.app, pstep, Res.app, List.cons_append]
  | .E, k + 1, us, _ => simp only [PS.app, pstep, Res.app, List.cons_append, List.headD, List.tail]
  | .C, k + 1, us, _ => simp only [PS.app, pstep, Res.app, List.cons_append, List.headD, List.tail]
  | ph, 0, u :: v :: us, _ =>
    match ph, u, v with
    | .A, 0, v => simp only [PS.app, pstep, Res.app, List.cons_append]
    | .E, 0, v => simp only [PS.app, pstep, Res.app, List.cons_append]
    | .C, 0, v => simp only [PS.app, pstep, Res.app, List.cons_append]
    | .C, u + 1, v =>
      by_cases ha : a = 0 <;> simp [PS.app, pstep, Res.app, cMove, ha, rd]
    | .E, u + 1, v =>
      by_cases ha : a = 0 <;> simp [PS.app, pstep, Res.app, eMove, ha, rd]
    | .A, u + 3, v => simp only [PS.app, pstep, Res.app, List.cons_append, List.headD, List.tail]
    | .A, 2, v => simp only [PS.app, pstep, Res.app, List.cons_append, List.headD, List.tail]
    | .A, 1, 0 => simp only [PS.app, pstep, Res.app, List.cons_append]
    | .A, 1, v + 1 => simp only [PS.app, pstep, Res.app, List.cons_append, List.headD, List.tail, rd]
  | _, 0, [], hk => simp at hk
  | _, 0, [_], hk => simp at hk

/-- With nothing further out on the right (`top`), only the left side must stay in the prefix. -/
def safeT (top : Bool) (s : PS) : Bool := if top then two s.lb else safe s

theorem pstep_frameT (top : Bool) (s : PS) (X R : List Nat) (ht : top = true → R = [])
    (h : safeT top s = true) : pstep (s.app X R) = (pstep s).app X R := by
  cases top with
  | false => exact pstep_frame s X R (by simpa [safeT] using h)
  | true =>
    obtain rfl := ht rfl
    simp only [safeT, ite_true] at h
    by_cases hs : safe s = true
    · exact pstep_frame s X [] hs
    obtain ⟨lb, ph, k, us⟩ := s
    match lb, h with
    | a :: b :: lb, _ =>
    match k, us with
    | k + 1, _ => simp [safe, two] at hs
    | 0, _ :: _ :: _ => simp [safe, two] at hs
    | 0, [] => cases ph <;> by_cases ha : a = 0 <;> simp [PS.app, pstep, Res.app, cMove, eMove, ha, rd]
    | 0, [u] =>
      rcases u with _ | _ | _ | u <;> cases ph <;> by_cases ha : a = 0 <;>
        simp [PS.app, pstep, Res.app, cMove, eMove, ha, rd]

/-- `runPass` with every move checked to stay in the prefix (`none` otherwise). -/
def runPassF (top : Bool) : Nat → PS → Option Out
  | 0, _ => none
  | f + 1, s =>
    if safeT top s then
      match pstep s with
      | .next s' n => (runPassF top f s').map (Out.add n)
      | .done bs l us n => some (.moment bs l us n)
      | .halt => some .halt
    else none

theorem Out_add_app (n : Nat) (X R : List Nat) (o : Out) : (o.add n).app X R = (o.app X R).add n := by
  cases o <;> rfl

theorem runPassF_frame (top : Bool) : ∀ (f : Nat) (s : PS) (o : Out) (X R : List Nat), (top = true → R = []) →
    runPassF top f s = some o → runPass f (s.app X R) = o.app X R
  | 0, _, _, _, _, _, h => by simp [runPassF] at h
  | f + 1, s, o, X, R, ht, h => by
    simp only [runPassF] at h
    split at h
    · rename_i hs
      simp only [runPass]
      rw [pstep_frameT top s X R ht hs]
      cases e : pstep s with
      | next s' n =>
        rw [e] at h; try dsimp only at h
        simp only [Res.app]
        cases e2 : runPassF top f s' with
        | none => rw [e2] at h; simp at h
        | some o' =>
          rw [e2] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          rw [runPassF_frame top f s' o' X R ht e2, Out_add_app]
      | done bs l us n =>
        rw [e] at h; try dsimp only at h
        simp only [Option.some.injEq] at h
        subst h
        rfl
      | halt =>
        rw [e] at h; try dsimp only at h
        simp only [Option.some.injEq] at h
        subst h
        rfl
    · simp at h

theorem startPS_frame (bs X : List Nat) (l : Nat) (us R : List Nat) (h : 2 ≤ bs.length) :
    startPS (bs ++ X) l (us ++ R) = (startPS bs l us).map (fun p => (p.1.app X R, p.2)) := by
  match bs, l, h with
  | (p + 1) :: c :: rest, l + 1, _ => rfl
  | 0 :: c :: rest, l, _ => rfl
  | (p + 1) :: c :: rest, 0, _ => rfl

/-- One sub-round on a prefix. -/
def subF (top : Bool) (fuel : Nat) (bs : List Nat) (l : Nat) (us : List Nat) : Option Out :=
  if two bs then
    match startPS bs l us with
    | some (s, n) => (runPassF top fuel s).map (Out.add n)
    | none => some .stuck
  else none

theorem subF_frame (top : Bool) (fuel : Nat) (bs : List Nat) (l : Nat) (us : List Nat) (o : Out) (X R : List Nat)
    (ht : top = true → R = []) (h : subF top fuel bs l us = some o) : sub fuel (bs ++ X) l (us ++ R) = o.app X R := by
  unfold subF at h
  split at h
  · rename_i hb
    unfold sub
    rw [startPS_frame bs X l us R ((two_iff bs).1 hb)]
    cases e : startPS bs l us with
    | none =>
      rw [e] at h; try dsimp only at h
      simp only [Option.some.injEq] at h; subst h; rfl
    | some p =>
      obtain ⟨s, n⟩ := p
      rw [e] at h; try dsimp only at h
      simp only [Option.map_some]
      cases e2 : runPassF top fuel s with
      | none => rw [e2] at h; simp at h
      | some o' =>
        rw [e2] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rw [runPassF_frame top fuel s o' X R ht e2, Out_add_app]
  · simp at h

/-- `N` sub-rounds on a prefix. -/
def subsF (top : Bool) (fuel : Nat) : Nat → List Nat → Nat → List Nat → Option Out
  | 0, bs, l, us => some (.moment bs l us 0)
  | N + 1, bs, l, us =>
    match subF top fuel bs l us with
    | some (.moment bs' l' us' n) => (subsF top fuel N bs' l' us').map (Out.add n)
    | some o => some o
    | none => none

theorem subsF_frame (top : Bool) (fuel : Nat) : ∀ (N : Nat) (bs : List Nat) (l : Nat) (us : List Nat) (o : Out)
    (X R : List Nat), (top = true → R = []) →
    subsF top fuel N bs l us = some o → subs fuel N (bs ++ X) l (us ++ R) = o.app X R
  | 0, bs, l, us, o, X, R, _, h => by
    simp only [subsF, Option.some.injEq] at h
    subst h; rfl
  | N + 1, bs, l, us, o, X, R, ht, h => by
    simp only [subsF] at h
    simp only [subs]
    cases e : subF top fuel bs l us with
    | none => rw [e] at h; simp at h
    | some o₁ =>
      rw [e] at h; try dsimp only at h
      rw [subF_frame top fuel bs l us o₁ X R ht e]
      cases o₁ with
      | moment bs' l' us' n =>
        try dsimp only at h
        cases e2 : subsF top fuel N bs' l' us' with
        | none => rw [e2] at h; simp at h
        | some o₂ =>
          rw [e2] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          show (subs fuel N (bs' ++ X) l' (us' ++ R)).add n = _
          rw [subsF_frame top fuel N bs' l' us' o₂ X R ht e2, Out_add_app]
      | halt => try dsimp only at h
                simp only [Option.some.injEq] at h; subst h; rfl
      | stuck => try dsimp only at h
                 simp only [Option.some.injEq] at h; subst h; rfl

/-! ## The counter -/

/-- `gpop` on a prefix: `none` when it would read past it, `some r` with the result `r` of `gpop` otherwise. -/
def gpopF : List Nat → Nat → Option (Option (Nat × List Nat))
  | [], _ => none
  | 3 :: us, n => gpopF us (n + 1)
  | (u + 4) :: us, n => some (some (4 * n + 5, u :: us))
  | [0], _ => none
  | 0 :: (w + 2) :: us, n => some (some (4 * n + 4, w :: us))
  | _ :: _, _ => some none

def appZ (R : List Nat) (x : Nat × List Nat) : Nat × List Nat := (x.1, x.2 ++ R)

theorem gpopF_frame : ∀ (us : List Nat) (n : Nat) (r : Option (Nat × List Nat)) (R : List Nat),
    gpopF us n = some r → gpop (us ++ R) n = r.map (appZ R)
  | [], _, _, _, h => by simp [gpopF] at h
  | 3 :: us, n, r, R, h => by
    simp only [gpopF] at h
    simp only [List.cons_append, gpop]
    exact gpopF_frame us (n + 1) r R h
  | (u + 4) :: us, n, r, R, h => by
    simp only [gpopF, Option.some.injEq] at h
    subst h; rfl
  | [0], _, _, _, h => by simp [gpopF] at h
  | 0 :: (w + 2) :: us, n, r, R, h => by
    simp only [gpopF, Option.some.injEq] at h
    subst h; rfl
  | 0 :: 0 :: us, n, r, R, h => by
    simp only [gpopF, Option.some.injEq] at h
    subst h; rfl
  | 0 :: 1 :: us, n, r, R, h => by
    simp only [gpopF, Option.some.injEq] at h
    subst h; rfl
  | 1 :: us, n, r, R, h => by
    simp only [gpopF, Option.some.injEq] at h
    subst h; rfl
  | 2 :: us, n, r, R, h => by
    simp only [gpopF, Option.some.injEq] at h
    subst h; rfl

def gstepF : Nat × List Nat → Option (Option (Nat × List Nat))
  | (b + 2, us) => some (some (1, b :: us))
  | (1, us) => gpopF us 0
  | (0, _) => some none

theorem gstepF_frame (x : Nat × List Nat) (r : Option (Nat × List Nat)) (R : List Nat) (h : gstepF x = some r) :
    gstep (appZ R x) = r.map (appZ R) := by
  obtain ⟨l, us⟩ := x
  match l, h with
  | b + 2, h => simp only [gstepF, Option.some.injEq] at h; subst h; rfl
  | 1, h => exact gpopF_frame us 0 r R h
  | 0, h => simp only [gstepF, Option.some.injEq] at h; subst h; rfl

/-- `gfast` on a prefix of the zone. -/
def gfastF : Nat → Nat → Nat × List Nat → Option (Nat × List Nat)
  | 0, _, _ => none
  | f + 1, N, x =>
    if N = 0 then some x else
    match gstepF (x.1 - 4 * pick N ((x.1 - 1) / 4), x.2) with
    | some (some y) => gfastF f (N - 2 ^ pick N ((x.1 - 1) / 4)) (y.1 + 4 * pick N ((x.1 - 1) / 4), y.2)
    | _ => none

theorem gfastF_frame : ∀ (f N : Nat) (x y : Nat × List Nat) (R : List Nat), gfastF f N x = some y →
    gfast f N (appZ R x) = some (appZ R y)
  | 0, _, _, _, _, h => by simp [gfastF] at h
  | f + 1, N, x, y, R, h => by
    simp only [gfastF] at h
    simp only [gfast]
    split at h
    · rename_i hN; simp only [Option.some.injEq] at h; subst h; simp [hN]
    · rename_i hN
      simp only [hN, ite_false]
      cases e : gstepF (x.1 - 4 * pick N ((x.1 - 1) / 4), x.2) with
      | none => rw [e] at h; simp at h
      | some r =>
        cases r with
        | none => rw [e] at h; simp at h
        | some z =>
          rw [e] at h; try dsimp only at h
          have hz := gstepF_frame _ _ R e
          simp only [appZ] at hz ⊢
          rw [hz]
          simp only [Option.map_some]
          exact gfastF_frame f _ _ _ R h

/-! ## The time left of a list with a tail -/

/-- The digits plus their number: the bits of `T`. -/
def sig (F : List Nat) : Nat := (F.map (· + 1)).sum

theorem T_append : ∀ (F X : List Nat), T (F ++ X) = T F + 2 ^ sig F * T X
  | [], X => by simp [T, sig]
  | x :: F, X => by
    simp only [List.cons_append, T, sig, List.map_cons, List.sum_cons]
    rw [T_append F X]
    simp only [sig]
    rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
    grind

theorem mass_append (q : Nat) (F X : List Nat) : mass q (F ++ X) = q + sig F + (X.map (· + 1)).sum := by
  simp only [mass, sig, List.map_append, List.sum_append]; omega

theorem encBlocks_append (q : Nat) (F X : List Nat) :
    encBlocks q (F ++ X) = F.map (fun d => 3 * d + 2) ++ encBlocks q X := by
  simp [encBlocks]

/-! ## A stretch on a prefix -/

/-- A pass on the prefix: `N` sub-rounds of the pass machine, from blocks `F` and gaps `Z` to `F'` and `Z'`. -/
theorem pass_frame (top : Bool) (fuel N q : Nat) (F F' X : List Nat) (l l' : Nat) (Z Z' R : List Nat) (n : Nat)
    (ht : top = true → R = []) (h : subsF top fuel N (F.map (fun d => 3 * d + 2)) l Z = some (.moment (F'.map (fun d => 3 * d + 2)) l' Z' n)) :
    steps n (enc q (F ++ X) l (Z ++ R)) = some (enc q (F' ++ X) l' (Z' ++ R)) := by
  have h₁ := subsF_frame top fuel N _ l Z _ (encBlocks q X) R ht h
  simp only [Out.app] at h₁
  rw [enc_gcfg, enc_gcfg, encBlocks_append, encBlocks_append]
  exact subs_moment fuel N _ _ _ _ _ _ _ h₁

/-- An advance on the prefix: `M` sub-rounds of `W` with the counter, the digits `F` becoming `F'` with the same
number of bits and `T F' + M = T F`, the counter computed on the prefix `Z`. -/
theorem advance_frame (fuel M q : Nat) (F F' X : List Nat) (x y : Nat × List Nat) (R : List Nat)
    (hT : T F' + M = T F) (hs : sig F' = sig F) (hy : gfastF fuel M x = some y) :
    ∃ n, steps n (enc q (F ++ X) x.1 (x.2 ++ R)) = some (enc q (F' ++ X) y.1 (y.2 ++ R)) := by
  have hg := gfast_sound fuel M _ _ (gfastF_frame fuel M x y R hy)
  have h := advance_to M q q (F ++ X) (F' ++ X) (appZ R x) (appZ R y)
    (by rw [T_append, T_append, hs]; omega)
    (by rw [mass_append, mass_append, hs]) hg
  exact h

end H4320
