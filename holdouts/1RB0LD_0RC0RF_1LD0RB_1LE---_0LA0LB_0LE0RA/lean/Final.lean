import Replay
import Mirror

/-!
# 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA halts if and only if its run reaches one tape shape

For the mirror machine (`MachineM.lean`), from the checks of `Replay.lean`: it halts from blank tape (in state D) if
and only if its run reaches `Hn P = F> 00001101 (1000)^P 101110110100001101` for some odd P ≥ 21, the one halting
class of the certificate (`halts_iff_Hn`, with `isH_map` by `native_decide`).  Also: if and only if it reaches
`Xn P = F> 00001101 (1000)^P 10101101000010100001101` for some odd P ≥ 21, the one entry of `pre` (`halts_iff_Xn`).
With `Mirror.lean`:

**`halts_iff`**: 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA halts from blank tape if and only if its run reaches the
tape `101100001011011101 (0001)^P 1011000`, the rest blank, with the head in state F on the blank cell right of it
(`H P`), for some odd P ≥ 21.
-/

namespace H163738M

open TM

def bitsL (s : String) : List Bool := s.toList.map (· == '1')

def Htext : List Seg :=
  [.cells (bitsL "00001101"), .blk (bitsL "1000"), .cells (bitsL "101110110100001101")]

def Xtext : List Seg :=
  [.cells (bitsL "00001101"), .blk (bitsL "1000"), .cells (bitsL "10101101000010100001101")]

/-- `F> 00001101 (1000)^P 101110110100001101`, at the left end of the tape. -/
def Hn (P : Nat) : Config :=
  ⟨blank, app (bitsL "00001101") (rep P (bitsL "1000") (app (bitsL "101110110100001101") blank)), .F⟩

/-- `F> 00001101 (1000)^P 10101101000010100001101`, at the left end of the tape. -/
def Xn (P : Nat) : Config :=
  ⟨blank, app (bitsL "00001101") (rep P (bitsL "1000") (app (bitsL "10101101000010100001101") blank)), .F⟩

theorem dn_cells0 (ρ : Nat → Nat) (w : List Bool) : dn ρ (w.map .cell) = app w blank := by
  have := dn_cells ρ w []
  rwa [List.append_nil] at this

theorem nodeH (P : Nat) : nodeCfg Htext [P] = Hn P := by
  simp [nodeCfg, Htext, Hn, build, consts, dn, dn_cells, dn_cells0, Cnt.eval, dot]

theorem nodeX (P : Nat) : nodeCfg Xtext [P] = Xn P := by
  simp [nodeCfg, Xtext, Xn, build, consts, dn, dn_cells, dn_cells0, Cnt.eval, dot]

/-- The one halting class: text and residue. -/
theorem isH_map : (cls.filter (·.isH)).map (fun c => (c.text, c.res)) = [(Htext, [1])] := by native_decide

theorem validV_one {vs : List Nat} (h : ValidV vs [1]) : ∃ P, vs = [P] ∧ P % 2 = 1 ∧ 21 ≤ P := by
  match vs, h with
  | [P], h =>
    simp only [ValidV, BIG, MOD, and_true] at h
    exact ⟨P, rfl, by omega, by omega⟩

/-- **The mirror machine halts from blank tape in state D if and only if its run reaches `Hn P` for some odd
P ≥ 21.** -/
theorem halts_iff_Hn : HaltsFromBlank ↔ ∃ P, P % 2 = 1 ∧ 21 ≤ P ∧ Reach init (Hn P) := by
  rw [halts_iff_reach_H T_ok cls_ok (fun p hp => List.all_eq_true.1 pre_ok p hp) (arrives_sound T_ok arrive_ok)]
  constructor
  · rintro ⟨c, hc, hH, vs, hv, h⟩
    have hm := List.mem_map_of_mem (f := fun c : Cls => (c.text, c.res)) (List.mem_filter.2 ⟨hc, hH⟩)
    rw [isH_map] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rw [hm.2] at hv
    obtain ⟨P, rfl, hp, h21⟩ := validV_one hv
    rw [hm.1, nodeH] at h
    exact ⟨P, hp, h21, h⟩
  · rintro ⟨P, hp, h21, h⟩
    have hm : (Htext, [1]) ∈ (cls.filter (·.isH)).map (fun c => (c.text, c.res)) := by
      rw [isH_map]
      exact List.mem_singleton_self _
    obtain ⟨c, hc, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨hc, hH⟩ := List.mem_filter.1 hc
    refine ⟨c, hc, hH, [P], ?_, ?_⟩
    · rw [he.2]
      simp only [ValidV, BIG, MOD, and_true]
      omega
    · rw [he.1, nodeH]
      exact h

/-- The one entry of `pre`: text and count. -/
theorem pre_map : pre.map (fun p => (p.text, p.cs)) = [(Xtext, [⟨21, [2]⟩])] := by native_decide

/-- The mirror machine halts from blank tape in state D if and only if its run reaches `Xn P` for some odd
P ≥ 21 (the only way into the halting class). -/
theorem halts_iff_Xn : HaltsFromBlank ↔ ∃ P, P % 2 = 1 ∧ 21 ≤ P ∧ Reach init (Xn P) := by
  rw [halts_iff_pre]
  constructor
  · rintro ⟨p, hp, ρ, h⟩
    have hm := List.mem_map_of_mem (f := fun p : PreE => (p.text, p.cs)) hp
    rw [pre_map] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rw [hm.1, hm.2] at h
    simp only [evals, List.map, Cnt.eval, dot, Nat.add_zero] at h
    rw [nodeX] at h
    exact ⟨_, by omega, by omega, h⟩
  · rintro ⟨P, hp, h21, h⟩
    have hm : (Xtext, [(⟨21, [2]⟩ : Cnt)]) ∈ pre.map (fun p => (p.text, p.cs)) := by
      rw [pre_map]
      exact List.mem_singleton_self _
    obtain ⟨p, hp', he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    refine ⟨p, hp', fun _ => (P - 21) / 2, ?_⟩
    rw [he.1, he.2, ← nodeX] at *
    have e : evals (fun _ => (P - 21) / 2) [(⟨21, [2]⟩ : Cnt)] = [P] := by
      simp [evals, Cnt.eval, dot]
      omega
    rw [e]
    exact h

end H163738M

namespace H163738

open TM

/-- The tape `101100001011011101 (0001)^P 1011000`, the rest blank, the head in state F on the blank cell right of it
(the left side is stored nearest cell first). -/
def H (P : Nat) : Config :=
  ⟨app (H163738M.bitsL "0001101") (rep P (H163738M.bitsL "1000")
    (app (H163738M.bitsL "101110110100001101") blank)), blank, .F⟩

theorem phi_H (P : Nat) : φ (H P) = H163738M.Hn P := by
  have e : H163738M.bitsL "00001101" = false :: H163738M.bitsL "0001101" := by decide
  simp only [φ, H, H163738M.Hn, e, app_cons]
  rfl

/-- **1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA halts from blank tape if and only if its run reaches `H P` for some
odd P ≥ 21.** -/
theorem halts_iff : HaltsFromBlank ↔ ∃ P, P % 2 = 1 ∧ 21 ≤ P ∧ Reach init (H P) := by
  rw [halts_iff_mirror, H163738M.halts_iff_Hn]
  simp only [reach_iff_mirror, phi_H]
  rfl

end H163738
