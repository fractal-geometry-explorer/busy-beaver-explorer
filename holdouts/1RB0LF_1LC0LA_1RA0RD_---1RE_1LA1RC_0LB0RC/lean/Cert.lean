import Tables

/-!
# 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC does not halt

The certificate: 62 *phase templates* `tplAt t` (the left-end configurations
`B> 00 (01)^(3k+4) 000 (01)^(3j+β) rest` of the four regimes, `rest` fixed), with

* a **round** for each template: `tplAt t` at `[k+1, j]` reaches `tplAt (nxt t)` at `[k, j + dj t]`;
* an **end of epoch** for each template: `tplAt t` at `[0, j+200]` reaches `tplAt (endT t)` at
  `[j + endC1 t, endC2 t]`;
* the **start**: from blank tape the machine reaches `tplAt 31` at `[38, 163]`.

Each is a run of the symbolic checker `TM.Sym.auto` (`SymCheck.lean`, proved sound against the machine's
semantics). The tables and the 62 rounds are evaluated by Lean's kernel (`decide +kernel`); the start (about 148,000
symbolic moves) and the 62 end cases (about 2.5 million) by compiled code (`native_decide`), since the kernel runs
out of memory on runs that long.
The potential `j + 2k + pot t` never drops below 215 (checked on the tables), so `j ≥ 200` whenever an epoch ends, and
the run from blank tape passes through these configurations forever.
-/

namespace H36670

open TM TM.Sym

def σR : List Lin := [⟨1, [1]⟩, ⟨0, [0, 1]⟩]
def σE : List Lin := [⟨0, []⟩, ⟨200, [0, 1]⟩]

def roundOK (t : Nat) : Bool :=
  auto trans .B (norm ((tplAt (nxt.getD t 0)).subst [⟨0, [1]⟩, ⟨dj.getD t 0, [0, 1]⟩]).r) 3000 false
    ((tplAt t).subst σR)

def endOK (t : Nat) : Bool :=
  auto trans .B (norm ((tplAt (endT.getD t 0)).subst [⟨endC1.getD t 0, [0, 1]⟩, ⟨endC2.getD t 0, []⟩]).r)
    200000 false ((tplAt t).subst σE)

/-- The table facts the glue needs. -/
def tablesOK (t : Nat) : Bool :=
  (tplAt t).l.isEmpty && decide ((tplAt t).st = .B) && decide (nxt.getD t 0 < nT) && decide (endT.getD t 0 < nT) &&
  decide (pot t + 2 ≤ pot (nxt.getD t 0) + dj.getD t 0) && decide (pot t ≤ 15) &&
  decide (215 ≤ endC2.getD t 0 + 2 * endC1.getD t 0 + pot (endT.getD t 0))

theorem tables_ok : (List.range nT).all tablesOK = true := by decide +kernel

theorem start_ok : auto trans .B (norm ((tplAt 31).subst [⟨38, []⟩, ⟨163, []⟩]).r) startFuel false ⟨[], [], .A⟩ = true := by
  native_decide

theorem tgt_den (c : MC St) (hl : c.l = []) (hs : c.st = .B) (σ : List Lin) (x : List Nat) :
    MC.den x ⟨[], norm (c.subst σ).r, .B⟩ = c.den (σ.map (·.eval x)) := by
  simp only [MC.den, norm_den, MC.subst, den_subst, hl, hs, List.map_nil, Sym.den]

theorem tablesAt {t : Nat} (ht : t < nT) : tablesOK t = true :=
  List.all_eq_true.mp tables_ok t (List.mem_range.mpr ht)

/-- The invariant: a phase template, with the potential at least 215. -/
def Good (c : Config) : Prop :=
  ∃ t k j, t < nT ∧ c = (tplAt t).den [k, j] ∧ 215 ≤ j + 2 * k + pot t

theorem good_step (rounds : ∀ t, t < nT → roundOK t = true) (ends : ∀ t, t < nT → endOK t = true)
    (c : Config) (hc : Good c) : ∃ n c', 1 ≤ n ∧ steps n c = some c' ∧ Good c' := by
  obtain ⟨t, k, j, ht, rfl, hp⟩ := hc
  have tb := tablesAt ht
  simp only [tablesOK, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at tb
  obtain ⟨⟨⟨⟨⟨⟨hl, hs⟩, hn⟩, he⟩, hpot⟩, h15⟩, hend⟩ := tb
  cases k with
  | succ k =>
    obtain ⟨n, hn1, hsteps⟩ := auto_reach trans _ _ _ _ (rounds t ht) [k, j]
    have tl := tablesAt hn
    simp only [tablesOK, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at tl
    rw [tgt_den _ tl.1.1.1.1.1.1 tl.1.1.1.1.1.2, MC.den_subst] at hsteps
    refine ⟨n, _, hn1, ?_, nxt.getD t 0, k, j + dj.getD t 0, hn, rfl, by omega⟩
    have e1 : σR.map (·.eval [k, j]) = [k + 1, j] := by simp [σR, Lin.eval, dot]; omega
    have e2 : ([⟨0, [1]⟩, ⟨dj.getD t 0, [0, 1]⟩] : List Lin).map (·.eval [k, j]) = [k, j + dj.getD t 0] := by
      simp [Lin.eval, dot]; omega
    rw [e1, e2] at hsteps
    exact hsteps
  | zero =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 200 := ⟨j - 200, by omega⟩
    obtain ⟨n, hn1, hsteps⟩ := auto_reach trans _ _ _ _ (ends t ht) [0, j']
    have tl := tablesAt he
    simp only [tablesOK, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at tl
    rw [tgt_den _ tl.1.1.1.1.1.1 tl.1.1.1.1.1.2, MC.den_subst] at hsteps
    refine ⟨n, _, hn1, ?_, endT.getD t 0, j' + endC1.getD t 0, endC2.getD t 0, he, rfl, by omega⟩
    have e1 : σE.map (·.eval [0, j']) = [0, j' + 200] := by simp [σE, Lin.eval, dot]; omega
    have e2 : ([⟨endC1.getD t 0, [0, 1]⟩, ⟨endC2.getD t 0, []⟩] : List Lin).map (·.eval [0, j']) =
        [j' + endC1.getD t 0, endC2.getD t 0] := by
      simp [Lin.eval, dot]; omega
    rw [e1, e2] at hsteps
    exact hsteps

theorem start_good : ∃ n c, steps n init = some c ∧ Good c := by
  obtain ⟨n, -, h⟩ := auto_reach trans _ _ _ _ start_ok []
  have tl := tablesAt (show 31 < nT by decide)
  simp only [tablesOK, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at tl
  rw [tgt_den _ tl.1.1.1.1.1.1 tl.1.1.1.1.1.2] at h
  have e : ([⟨38, []⟩, ⟨163, []⟩] : List Lin).map (·.eval []) = [38, 163] := rfl
  rw [e] at h
  exact ⟨n, _, h, 31, 38, 163, by decide, rfl, by decide⟩

/-- The 62 rounds, each evaluated by the kernel. -/
theorem round_0 : roundOK 0 = true := by decide +kernel
theorem round_1 : roundOK 1 = true := by decide +kernel
theorem round_2 : roundOK 2 = true := by decide +kernel
theorem round_3 : roundOK 3 = true := by decide +kernel
theorem round_4 : roundOK 4 = true := by decide +kernel
theorem round_5 : roundOK 5 = true := by decide +kernel
theorem round_6 : roundOK 6 = true := by decide +kernel
theorem round_7 : roundOK 7 = true := by decide +kernel
theorem round_8 : roundOK 8 = true := by decide +kernel
theorem round_9 : roundOK 9 = true := by decide +kernel
theorem round_10 : roundOK 10 = true := by decide +kernel
theorem round_11 : roundOK 11 = true := by decide +kernel
theorem round_12 : roundOK 12 = true := by decide +kernel
theorem round_13 : roundOK 13 = true := by decide +kernel
theorem round_14 : roundOK 14 = true := by decide +kernel
theorem round_15 : roundOK 15 = true := by decide +kernel
theorem round_16 : roundOK 16 = true := by decide +kernel
theorem round_17 : roundOK 17 = true := by decide +kernel
theorem round_18 : roundOK 18 = true := by decide +kernel
theorem round_19 : roundOK 19 = true := by decide +kernel
theorem round_20 : roundOK 20 = true := by decide +kernel
theorem round_21 : roundOK 21 = true := by decide +kernel
theorem round_22 : roundOK 22 = true := by decide +kernel
theorem round_23 : roundOK 23 = true := by decide +kernel
theorem round_24 : roundOK 24 = true := by decide +kernel
theorem round_25 : roundOK 25 = true := by decide +kernel
theorem round_26 : roundOK 26 = true := by decide +kernel
theorem round_27 : roundOK 27 = true := by decide +kernel
theorem round_28 : roundOK 28 = true := by decide +kernel
theorem round_29 : roundOK 29 = true := by decide +kernel
theorem round_30 : roundOK 30 = true := by decide +kernel
theorem round_31 : roundOK 31 = true := by decide +kernel
theorem round_32 : roundOK 32 = true := by decide +kernel
theorem round_33 : roundOK 33 = true := by decide +kernel
theorem round_34 : roundOK 34 = true := by decide +kernel
theorem round_35 : roundOK 35 = true := by decide +kernel
theorem round_36 : roundOK 36 = true := by decide +kernel
theorem round_37 : roundOK 37 = true := by decide +kernel
theorem round_38 : roundOK 38 = true := by decide +kernel
theorem round_39 : roundOK 39 = true := by decide +kernel
theorem round_40 : roundOK 40 = true := by decide +kernel
theorem round_41 : roundOK 41 = true := by decide +kernel
theorem round_42 : roundOK 42 = true := by decide +kernel
theorem round_43 : roundOK 43 = true := by decide +kernel
theorem round_44 : roundOK 44 = true := by decide +kernel
theorem round_45 : roundOK 45 = true := by decide +kernel
theorem round_46 : roundOK 46 = true := by decide +kernel
theorem round_47 : roundOK 47 = true := by decide +kernel
theorem round_48 : roundOK 48 = true := by decide +kernel
theorem round_49 : roundOK 49 = true := by decide +kernel
theorem round_50 : roundOK 50 = true := by decide +kernel
theorem round_51 : roundOK 51 = true := by decide +kernel
theorem round_52 : roundOK 52 = true := by decide +kernel
theorem round_53 : roundOK 53 = true := by decide +kernel
theorem round_54 : roundOK 54 = true := by decide +kernel
theorem round_55 : roundOK 55 = true := by decide +kernel
theorem round_56 : roundOK 56 = true := by decide +kernel
theorem round_57 : roundOK 57 = true := by decide +kernel
theorem round_58 : roundOK 58 = true := by decide +kernel
theorem round_59 : roundOK 59 = true := by decide +kernel
theorem round_60 : roundOK 60 = true := by decide +kernel
theorem round_61 : roundOK 61 = true := by decide +kernel

theorem rounds : ∀ t, t < nT → roundOK t = true := by
  intro t ht
  match t, ht with
  | 0, _ => exact round_0
  | 1, _ => exact round_1
  | 2, _ => exact round_2
  | 3, _ => exact round_3
  | 4, _ => exact round_4
  | 5, _ => exact round_5
  | 6, _ => exact round_6
  | 7, _ => exact round_7
  | 8, _ => exact round_8
  | 9, _ => exact round_9
  | 10, _ => exact round_10
  | 11, _ => exact round_11
  | 12, _ => exact round_12
  | 13, _ => exact round_13
  | 14, _ => exact round_14
  | 15, _ => exact round_15
  | 16, _ => exact round_16
  | 17, _ => exact round_17
  | 18, _ => exact round_18
  | 19, _ => exact round_19
  | 20, _ => exact round_20
  | 21, _ => exact round_21
  | 22, _ => exact round_22
  | 23, _ => exact round_23
  | 24, _ => exact round_24
  | 25, _ => exact round_25
  | 26, _ => exact round_26
  | 27, _ => exact round_27
  | 28, _ => exact round_28
  | 29, _ => exact round_29
  | 30, _ => exact round_30
  | 31, _ => exact round_31
  | 32, _ => exact round_32
  | 33, _ => exact round_33
  | 34, _ => exact round_34
  | 35, _ => exact round_35
  | 36, _ => exact round_36
  | 37, _ => exact round_37
  | 38, _ => exact round_38
  | 39, _ => exact round_39
  | 40, _ => exact round_40
  | 41, _ => exact round_41
  | 42, _ => exact round_42
  | 43, _ => exact round_43
  | 44, _ => exact round_44
  | 45, _ => exact round_45
  | 46, _ => exact round_46
  | 47, _ => exact round_47
  | 48, _ => exact round_48
  | 49, _ => exact round_49
  | 50, _ => exact round_50
  | 51, _ => exact round_51
  | 52, _ => exact round_52
  | 53, _ => exact round_53
  | 54, _ => exact round_54
  | 55, _ => exact round_55
  | 56, _ => exact round_56
  | 57, _ => exact round_57
  | 58, _ => exact round_58
  | 59, _ => exact round_59
  | 60, _ => exact round_60
  | 61, _ => exact round_61
  | _ + 62, h => exact absurd h (by simp [nT])

theorem nonhalting_of (ends : ∀ t, t < nT → endOK t = true) : ¬ HaltsFromBlank := by
  apply not_halts_of_forall
  apply forall_of_unbounded trans (fun m => ∃ c, steps m init = some c ∧ Good c)
  · intro N
    induction N with
    | zero =>
      obtain ⟨n, c, h1, h2⟩ := start_good
      exact ⟨n, Nat.zero_le _, c, h1, h2⟩
    | succ N ih =>
      obtain ⟨m, hm, c, h1, h2⟩ := ih
      obtain ⟨n, c', hn, h3, h4⟩ := good_step rounds ends c h2
      exact ⟨m + n, by omega, c', steps_seq trans h1 h3, h4⟩
  · rintro m ⟨c, h, -⟩
    exact ⟨c, h⟩

/-- The 62 end-of-epoch runs (about 2.5 million symbolic moves), checked by compiled evaluation. -/
theorem ends_ok : (List.range nT).all endOK = true := by native_decide

theorem nonhalting : ¬ HaltsFromBlank :=
  nonhalting_of (fun t ht => List.all_eq_true.mp ends_ok t (List.mem_range.mpr ht))

end H36670
