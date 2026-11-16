import Replay

/-!
# 1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD halts if and only if its run hits one of two lines

`halts_iff_pre` (`Replay.lean`) with the fourteen entries of `pre` written out (`pre_map`, by `native_decide`):
seven are the tape `A P Q` on the line `Q = 3P − 16`, seven the tape `B P Q` on the line `Q = 3P − 24`, for P odd,
P ≥ 21 (P = 21, 23, 25, 27, and P = 29 + 6x, 31 + 6x, 33 + 6x).  So:

**`halts_iff_lines`**: the machine halts from blank tape if and only if its run reaches `A P (3P − 16)` or
`B P (3P − 24)` for some odd P ≥ 21.
-/

namespace H100726

open TM

def bitsL (s : String) : List Bool := s.toList.map (· == '1')

def Atext : List Seg :=
  [.cells (bitsL "00001"), .blk (bitsL "1000"), .cells (bitsL "10100001101000"), .blk (bitsL "0001"),
   .cells (bitsL "01000000101")]

def Btext : List Seg :=
  [.cells (bitsL "00001"), .blk (bitsL "1000"), .cells (bitsL "101000010000001011"), .blk (bitsL "1000"),
   .cells (bitsL "101000000101")]

/-- `F> 00001 (1000)^P 10100001101000 (0001)^Q 01000000101`, at the left end of the tape. -/
def A (P Q : Nat) : Config :=
  ⟨blank, app (bitsL "00001") (rep P (bitsL "1000") (app (bitsL "10100001101000") (rep Q (bitsL "0001")
    (app (bitsL "01000000101") blank)))), .F⟩

/-- `F> 00001 (1000)^P 101000010000001011 (1000)^Q 101000000101`, at the left end of the tape. -/
def B (P Q : Nat) : Config :=
  ⟨blank, app (bitsL "00001") (rep P (bitsL "1000") (app (bitsL "101000010000001011") (rep Q (bitsL "1000")
    (app (bitsL "101000000101") blank)))), .F⟩

theorem dn_cells0 (ρ : Nat → Nat) (w : List Bool) : dn ρ (w.map .cell) = app w blank := by
  have := dn_cells ρ w []
  rwa [List.append_nil] at this

theorem nodeA (P Q : Nat) : nodeCfg Atext [P, Q] = A P Q := by
  simp [nodeCfg, Atext, A, build, consts, dn, dn_cells, dn_cells0, Cnt.eval, dot]

theorem nodeB (P Q : Nat) : nodeCfg Btext [P, Q] = B P Q := by
  simp [nodeCfg, Btext, B, build, consts, dn, dn_cells, dn_cells0, Cnt.eval, dot]

/-- The entries of `pre`: text and counts. -/
def L : List (List Seg × List Cnt) :=
  [(Atext, [⟨21, []⟩, ⟨47, []⟩]), (Atext, [⟨23, []⟩, ⟨53, []⟩]), (Atext, [⟨25, []⟩, ⟨59, []⟩]),
   (Atext, [⟨31, [6]⟩, ⟨77, [18]⟩]), (Atext, [⟨27, []⟩, ⟨65, []⟩]), (Atext, [⟨33, [6]⟩, ⟨83, [18]⟩]),
   (Atext, [⟨29, [6]⟩, ⟨71, [18]⟩]),
   (Btext, [⟨21, []⟩, ⟨39, []⟩]), (Btext, [⟨23, []⟩, ⟨45, []⟩]), (Btext, [⟨25, []⟩, ⟨51, []⟩]),
   (Btext, [⟨27, []⟩, ⟨57, []⟩]), (Btext, [⟨33, [6]⟩, ⟨75, [18]⟩]), (Btext, [⟨29, [6]⟩, ⟨63, [18]⟩]),
   (Btext, [⟨31, [6]⟩, ⟨69, [18]⟩])]

theorem pre_map : pre.map (fun p => (p.text, p.cs)) = L := by native_decide

theorem halts_iff_L : HaltsFromBlank ↔ ∃ q ∈ L, ∃ ρ, Reach init (nodeCfg q.1 (evals ρ q.2)) := by
  rw [halts_iff_pre, ← pre_map]
  simp only [List.mem_map]
  constructor
  · rintro ⟨p, hp, ρ, h⟩
    exact ⟨_, ⟨p, hp, rfl⟩, ρ, h⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, ρ, h⟩
    exact ⟨p, hp, ρ, h⟩

/-- The right-hand side: the run reaches `A` on the first line or `B` on the second, at an odd P ≥ 21. -/
def OnLine : Prop :=
  ∃ P, P % 2 = 1 ∧ 21 ≤ P ∧ (Reach init (A P (3 * P - 16)) ∨ Reach init (B P (3 * P - 24)))

theorem onA {P Q : Nat} (h : Reach init (nodeCfg Atext [P, Q])) (hq : Q = 3 * P - 16) (hp : P % 2 = 1)
    (h21 : 21 ≤ P) : OnLine := ⟨P, hp, h21, Or.inl (by rw [← nodeA, ← hq]; exact h)⟩

theorem onB {P Q : Nat} (h : Reach init (nodeCfg Btext [P, Q])) (hq : Q = 3 * P - 24) (hp : P % 2 = 1)
    (h21 : 21 ≤ P) : OnLine := ⟨P, hp, h21, Or.inr (by rw [← nodeB, ← hq]; exact h)⟩

theorem inL {t : List Seg} {cs : List Cnt} (hm : (t, cs) ∈ L) (ρ : Nat → Nat) {vs : List Nat}
    (he : evals ρ cs = vs) (h : Reach init (nodeCfg t vs)) : ∃ q ∈ L, ∃ ρ, Reach init (nodeCfg q.1 (evals ρ q.2)) :=
  ⟨(t, cs), hm, ρ, by rw [he]; exact h⟩

/-- **The machine halts from blank tape if and only if its run reaches `A P (3P − 16)` or `B P (3P − 24)` for
some odd P ≥ 21.** -/
theorem halts_iff_lines : HaltsFromBlank ↔ OnLine := by
  rw [halts_iff_L]
  constructor
  · rintro ⟨q, hq, ρ, h⟩
    simp only [L, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [evals, List.map, Cnt.eval, dot, Nat.add_zero] at h
    · exact onA h (by omega) (by omega) (by omega)
    · exact onA h (by omega) (by omega) (by omega)
    · exact onA h (by omega) (by omega) (by omega)
    · exact onA h (by omega) (by omega) (by omega)
    · exact onA h (by omega) (by omega) (by omega)
    · exact onA h (by omega) (by omega) (by omega)
    · exact onA h (by omega) (by omega) (by omega)
    · exact onB h (by omega) (by omega) (by omega)
    · exact onB h (by omega) (by omega) (by omega)
    · exact onB h (by omega) (by omega) (by omega)
    · exact onB h (by omega) (by omega) (by omega)
    · exact onB h (by omega) (by omega) (by omega)
    · exact onB h (by omega) (by omega) (by omega)
    · exact onB h (by omega) (by omega) (by omega)
  · rintro ⟨P, hp, h21, hA | hB⟩
    · rw [← nodeA] at hA
      by_cases hs : P < 29
      · rcases (by omega : P = 21 ∨ P = 23 ∨ P = 25 ∨ P = 27) with e | e | e | e <;> subst e
        · exact inL (cs := [⟨21, []⟩, ⟨47, []⟩]) (by simp [L]) (fun _ => 0) (by simp [evals, Cnt.eval, dot]) hA
        · exact inL (cs := [⟨23, []⟩, ⟨53, []⟩]) (by simp [L]) (fun _ => 0) (by simp [evals, Cnt.eval, dot]) hA
        · exact inL (cs := [⟨25, []⟩, ⟨59, []⟩]) (by simp [L]) (fun _ => 0) (by simp [evals, Cnt.eval, dot]) hA
        · exact inL (cs := [⟨27, []⟩, ⟨65, []⟩]) (by simp [L]) (fun _ => 0) (by simp [evals, Cnt.eval, dot]) hA
      · rcases (by omega : (P - 29) % 6 = 0 ∨ (P - 29) % 6 = 2 ∨ (P - 29) % 6 = 4) with e | e | e
        · exact inL (cs := [⟨29, [6]⟩, ⟨71, [18]⟩]) (by simp [L]) (fun _ => (P - 29) / 6)
            (by simp [evals, Cnt.eval, dot]; omega) hA
        · exact inL (cs := [⟨31, [6]⟩, ⟨77, [18]⟩]) (by simp [L]) (fun _ => (P - 29) / 6)
            (by simp [evals, Cnt.eval, dot]; omega) hA
        · exact inL (cs := [⟨33, [6]⟩, ⟨83, [18]⟩]) (by simp [L]) (fun _ => (P - 29) / 6)
            (by simp [evals, Cnt.eval, dot]; omega) hA
    · rw [← nodeB] at hB
      by_cases hs : P < 29
      · rcases (by omega : P = 21 ∨ P = 23 ∨ P = 25 ∨ P = 27) with e | e | e | e <;> subst e
        · exact inL (cs := [⟨21, []⟩, ⟨39, []⟩]) (by simp [L]) (fun _ => 0) (by simp [evals, Cnt.eval, dot]) hB
        · exact inL (cs := [⟨23, []⟩, ⟨45, []⟩]) (by simp [L]) (fun _ => 0) (by simp [evals, Cnt.eval, dot]) hB
        · exact inL (cs := [⟨25, []⟩, ⟨51, []⟩]) (by simp [L]) (fun _ => 0) (by simp [evals, Cnt.eval, dot]) hB
        · exact inL (cs := [⟨27, []⟩, ⟨57, []⟩]) (by simp [L]) (fun _ => 0) (by simp [evals, Cnt.eval, dot]) hB
      · rcases (by omega : (P - 29) % 6 = 0 ∨ (P - 29) % 6 = 2 ∨ (P - 29) % 6 = 4) with e | e | e
        · exact inL (cs := [⟨29, [6]⟩, ⟨63, [18]⟩]) (by simp [L]) (fun _ => (P - 29) / 6)
            (by simp [evals, Cnt.eval, dot]; omega) hB
        · exact inL (cs := [⟨31, [6]⟩, ⟨69, [18]⟩]) (by simp [L]) (fun _ => (P - 29) / 6)
            (by simp [evals, Cnt.eval, dot]; omega) hB
        · exact inL (cs := [⟨33, [6]⟩, ⟨75, [18]⟩]) (by simp [L]) (fun _ => (P - 29) / 6)
            (by simp [evals, Cnt.eval, dot]; omega) hB

end H100726
