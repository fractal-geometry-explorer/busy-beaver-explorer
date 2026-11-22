import Visit

/-!
# No invariant on run parities (or on runs mod 4, 8, 16) can exclude the halt

`halts_iff` (in `Visit.lean`) reduces halting to the orbit of `l0 = [12, 1^9]` under `visit` reaching `none`.
The natural hope is an invariant that looks only at the parities of the runs: a set `S` of *parity words*
(the list of `r % 2` over the runs, which also fixes the number of runs) that contains the word of `l0`, is closed
under the map (for every list of the domain whose word is in `S`, the word of the next list is in `S`), and contains
no word of a list where the map says halt.

`no_residue_invariant` shows that **no such set exists**, for residues mod 2, and also mod 4, 8 and 16: there is a
chain of lists of the domain, the first with the same residue word as `l0`, each mapped to a list with the residue
word of the next, the last mapped to `none` (a halt). The chains (14, 18, 20 and 56 lists, found by
`py/residue_chain.py`) are checked by `decide` in the kernel.

So an invariant that decides the machine has to use the exact sizes of the runs (the arithmetic of the 3/2 counter),
not their residues mod 16 or less.
-/

namespace H175628

/-- The residue word of a run list. -/
def resW (M : Nat) (l : List Nat) : List Nat := l.map (· % M)

/-- A Boolean test for the domain `D`. -/
def Db (l : List Nat) : Bool :=
  l.all (fun r => decide (1 ≤ r) && decide (r ≠ 2)) &&
  match l with
  | x :: _ => decide (x % 2 = 0) && (decide (12 ≤ x) || decide (l.take 4 = [6, 4, 1, 1]))
  | [] => false

theorem Db_sound (l : List Nat) (h : Db l = true) : D l := by
  unfold Db at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hall, hhd⟩ := h
  refine ⟨fun r hr => ?_, ?_⟩
  · have := List.all_eq_true.1 hall r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1, this.2⟩
  · cases l with
    | nil => cases hhd
    | cons x tl =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hhd
      refine ⟨x, tl, rfl, hhd.1, ?_⟩
      rcases hhd.2 with h12 | h4
      · exact Or.inl h12
      · right
        refine ⟨(x :: tl).drop 4, ?_⟩
        have e := List.take_append_drop 4 (x :: tl)
        rw [h4] at e
        exact e.symm

/-- A chain: every list in `D`, each mapped by `visit` to a list with the residue word of the next one, the last
mapped to `none`. -/
def chainOk (M : Nat) : List (List Nat) → Bool
  | [] => false
  | [a] => Db a && (visit a).isNone
  | a :: b :: rest => Db a && (match visit a with
      | some a' => decide (resW M a' = resW M b)
      | none => false) && chainOk M (b :: rest)

theorem chain_halt (M : Nat) (S : List Nat → Prop)
    (hc : ∀ l l', D l → S (resW M l) → visit l = some l' → S (resW M l')) :
    ∀ (ch : List (List Nat)) (a : List Nat), chainOk M (a :: ch) = true → S (resW M a) →
      ∃ l, D l ∧ S (resW M l) ∧ visit l = none
  | [], a, h, hs => by
    simp only [chainOk, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    exact ⟨a, Db_sound a h.1, hs, h.2⟩
  | b :: rest, a, h, hs => by
    simp only [chainOk, Bool.and_eq_true] at h
    obtain ⟨⟨hD, hv⟩, hrest⟩ := h
    cases e : visit a with
    | none => rw [e] at hv; cases hv
    | some a' =>
      rw [e] at hv
      simp only [decide_eq_true_eq] at hv
      have hb : S (resW M b) := hv ▸ hc a a' (Db_sound a hD) hs e
      exact chain_halt M S hc rest b hrest hb

/-- The chain for residues mod 2 (14 lists). -/
def chain2 : List (List Nat) := [
  [12, 19, 3, 9, 3, 15, 15, 15, 13, 7],
  [6, 4, 1, 1, 18, 15, 5, 13, 1, 3, 19, 7],
  [12, 6, 4, 5, 15, 19, 7, 15, 9, 13],
  [6, 4, 1, 1, 9, 14, 11, 11, 9, 1, 11],
  [14, 4, 7, 6, 19, 13, 19, 11, 15],
  [12, 19, 13, 3, 11, 13, 1],
  [6, 4, 1, 1, 8, 17, 17, 11, 15],
  [14, 18, 4, 3, 17, 9, 15],
  [6, 4, 1, 1, 17, 5, 12, 1, 5],
  [6, 4, 1, 1, 8, 13, 17],
  [12, 8, 6, 13, 11],
  [6, 4, 1, 1, 15, 11, 12],
  [6, 4, 1, 1, 12],
  [16, 16, 12]]

theorem chain2_ok : chainOk 2 chain2 = true := by decide

theorem chain2_head : chain2.head? = some [12, 19, 3, 9, 3, 15, 15, 15, 13, 7] ∧ resW 2 [12, 19, 3, 9, 3, 15, 15, 15, 13, 7] = resW 2 l0 := ⟨rfl, by decide⟩

/-- The chain for residues mod 4 (18 lists). -/
def chain4 : List (List Nat) := [
  [12, 25, 25, 1, 29, 17, 13, 5, 21, 1],
  [6, 4, 1, 1, 20, 29, 21, 1, 17, 17, 5, 13],
  [12, 4, 4, 13, 1, 17, 9, 1, 9, 29],
  [6, 4, 1, 1, 9, 28, 25, 1, 25, 1, 29],
  [24, 4, 29, 28, 13, 17, 9, 9, 5],
  [18, 27, 17, 9, 17, 17, 17],
  [6, 4, 1, 1, 9, 29, 13, 6, 9, 1, 1, 5],
  [12, 4, 5, 21, 1, 6, 1, 5, 13, 29],
  [26, 4, 21, 10, 17, 25, 9, 5],
  [12, 29, 17, 29, 29, 29],
  [6, 4, 1, 1, 28, 21, 9, 13],
  [12, 8, 8, 25, 5, 17],
  [22, 4, 9, 1, 13, 29, 9, 4, 5],
  [24, 4, 25, 29, 1, 8, 5],
  [14, 4, 21, 12, 1],
  [12, 15, 1],
  [6, 4, 1, 1, 26],
  [20, 12, 26]]

theorem chain4_ok : chainOk 4 chain4 = true := by decide

theorem chain4_head : chain4.head? = some [12, 25, 25, 1, 29, 17, 13, 5, 21, 1] ∧ resW 4 [12, 25, 25, 1, 29, 17, 13, 5, 21, 1] = resW 4 l0 := ⟨rfl, by decide⟩

/-- The chain for residues mod 8 (20 lists). -/
def chain8 : List (List Nat) := [
  [12, 49, 9, 1, 25, 1, 49, 25, 25, 33],
  [6, 4, 1, 1, 52, 41, 1, 9, 9, 1, 33, 1],
  [12, 52, 4, 17, 25, 25, 41, 49, 9, 49],
  [6, 4, 1, 1, 33, 28, 41, 17, 9, 9, 49],
  [36, 4, 49, 52, 33, 17, 25, 9, 17],
  [18, 31, 1, 33, 17, 9, 9],
  [6, 4, 1, 1, 25, 25, 41, 42, 33, 33, 41, 1],
  [12, 4, 41, 9, 25, 18, 33, 33, 17, 49],
  [42, 4, 49, 42, 1, 25, 9, 25],
  [16, 13, 25, 33, 1, 33],
  [14, 4, 1, 25, 9, 49, 48, 9, 49, 1],
  [20, 4, 1, 17, 24, 33, 33, 49],
  [18, 28, 8, 33, 9, 33],
  [6, 4, 1, 1, 33, 41, 49, 1, 33, 41, 44, 33],
  [28, 4, 33, 25, 41, 1, 9, 33, 4, 25],
  [34, 4, 9, 33, 9, 33, 44, 25],
  [24, 4, 49, 49, 44, 9],
  [22, 4, 52, 1],
  [20, 1],
  [42]]

theorem chain8_ok : chainOk 8 chain8 = true := by decide

theorem chain8_head : chain8.head? = some [12, 49, 9, 1, 25, 1, 49, 25, 25, 33] ∧ resW 8 [12, 49, 9, 1, 25, 1, 49, 25, 25, 33] = resW 8 l0 := ⟨rfl, by decide⟩

/-- The chain for residues mod 16 (56 lists). -/
def chain16 : List (List Nat) := [
  [12, 97, 17, 1, 49, 1, 97, 49, 49, 65],
  [22, 4, 33, 97, 4, 49, 17, 97, 33, 65, 17, 17],
  [12, 68, 4, 97, 81, 17, 81, 17, 1, 65],
  [70, 4, 49, 1, 57, 100, 49, 1, 1, 97, 17],
  [12, 4, 73, 100, 49, 1, 81, 33, 1],
  [18, 31, 97, 81, 49, 97, 17],
  [22, 4, 17, 97, 65, 1, 81, 66, 17, 65, 1, 33],
  [44, 4, 17, 81, 49, 18, 49, 1, 97, 17],
  [66, 4, 33, 18, 65, 65, 49, 81],
  [24, 21, 17, 81, 17, 17],
  [6, 4, 1, 1, 49, 33, 49, 65, 49, 65, 24, 65, 65, 1],
  [28, 4, 33, 1, 33, 81, 49, 49, 40, 1, 65, 1],
  [66, 4, 81, 17, 49, 97, 40, 1, 49, 81],
  [72, 4, 97, 1, 8, 97, 1, 49],
  [14, 68, 8, 17, 81, 97],
  [6, 4, 1, 1, 17, 41, 33, 1, 68, 65],
  [44, 4, 65, 73, 49, 97, 68, 81],
  [50, 12, 65, 17, 52, 49],
  [24, 33, 97, 17, 17, 36, 100, 1],
  [6, 4, 1, 1, 49, 17, 1, 17, 33, 49, 68, 33, 33, 4, 100, 81],
  [28, 4, 17, 1, 81, 49, 1, 17, 100, 81, 49, 20, 68, 17],
  [66, 4, 33, 33, 97, 1, 36, 33, 49, 20, 4, 33],
  [40, 4, 49, 65, 52, 97, 97, 4, 52, 97],
  [30, 100, 4, 33, 49, 20, 4, 1],
  [6, 4, 1, 1, 17, 81, 1, 65, 97, 17, 65, 81, 97, 25, 4, 20, 36, 33],
  [60, 4, 1, 1, 17, 17, 33, 33, 17, 81, 81, 57, 4, 36, 20, 81],
  [66, 4, 17, 81, 81, 81, 49, 49, 81, 89, 68, 84, 100, 81],
  [40, 4, 1, 65, 33, 33, 33, 41, 100, 36, 20, 33],
  [30, 4, 17, 49, 1, 89, 20, 20, 36, 97],
  [52, 4, 17, 25, 36, 52, 84, 65],
  [26, 12, 68, 4, 52, 1],
  [16, 1, 33, 17, 81, 9, 73],
  [54, 4, 17, 97, 49, 97, 68, 97, 17, 9, 57],
  [28, 4, 17, 1, 68, 97, 17, 9, 41],
  [18, 52, 4, 33, 65, 73, 41],
  [6, 4, 1, 1, 17, 33, 17, 25, 4, 57, 9],
  [12, 4, 65, 81, 97, 25, 4, 89, 57],
  [50, 4, 1, 89, 68, 57, 9],
  [24, 28, 4, 25, 25],
  [6, 4, 1, 1, 33, 97, 1, 1, 65, 1, 65, 4],
  [60, 4, 65, 1, 17, 33, 97, 97, 81, 36],
  [50, 4, 1, 49, 81, 17, 1, 68],
  [56, 4, 65, 65, 97, 68],
  [46, 4, 49, 100],
  [68, 7],
  [26, 49, 97, 33],
  [6, 4, 1, 1, 33, 97, 33, 65, 33, 1, 33, 4, 49],
  [12, 4, 17, 97, 81, 17, 33, 81, 49, 68, 1],
  [50, 4, 49, 17, 1, 33, 81, 100, 33],
  [56, 4, 97, 65, 81, 4, 81],
  [46, 4, 65, 52, 97],
  [20, 7, 17],
  [6, 4, 1, 1, 65, 49, 65, 33, 26],
  [28, 4, 1, 33, 97, 33, 42],
  [34, 4, 17, 1, 10],
  [40, 20, 74]]

theorem chain16_ok : chainOk 16 chain16 = true := by decide

theorem chain16_head : chain16.head? = some [12, 97, 17, 1, 49, 1, 97, 49, 49, 65] ∧ resW 16 [12, 97, 17, 1, 49, 1, 97, 49, 49, 65] = resW 16 l0 := ⟨rfl, by decide⟩

theorem no_residue_invariant (M : Nat) (hM : M = 2 ∨ M = 4 ∨ M = 8 ∨ M = 16) (S : List Nat → Prop)
    (h0 : S (resW M l0))
    (hc : ∀ l l', D l → S (resW M l) → visit l = some l' → S (resW M l')) :
    ∃ l, D l ∧ S (resW M l) ∧ visit l = none := by
  rcases hM with hM | hM | hM | hM
  · subst hM
    have hh : resW 2 [12, 19, 3, 9, 3, 15, 15, 15, 13, 7] = resW 2 l0 := chain2_head.2
    have ok : chainOk 2 ([12, 19, 3, 9, 3, 15, 15, 15, 13, 7] :: chain2.tail) = true := chain2_ok
    exact chain_halt 2 S hc _ _ ok (hh ▸ h0)
  · subst hM
    have hh : resW 4 [12, 25, 25, 1, 29, 17, 13, 5, 21, 1] = resW 4 l0 := chain4_head.2
    have ok : chainOk 4 ([12, 25, 25, 1, 29, 17, 13, 5, 21, 1] :: chain4.tail) = true := chain4_ok
    exact chain_halt 4 S hc _ _ ok (hh ▸ h0)
  · subst hM
    have hh : resW 8 [12, 49, 9, 1, 25, 1, 49, 25, 25, 33] = resW 8 l0 := chain8_head.2
    have ok : chainOk 8 ([12, 49, 9, 1, 25, 1, 49, 25, 25, 33] :: chain8.tail) = true := chain8_ok
    exact chain_halt 8 S hc _ _ ok (hh ▸ h0)
  · subst hM
    have hh : resW 16 [12, 97, 17, 1, 49, 1, 97, 49, 49, 65] = resW 16 l0 := chain16_head.2
    have ok : chainOk 16 ([12, 97, 17, 1, 49, 1, 97, 49, 49, 65] :: chain16.tail) = true := chain16_ok
    exact chain_halt 16 S hc _ _ ok (hh ▸ h0)

/-- The parity case on its own: **no set of parity words is an invariant of the visit map that contains the word of
`l0` and excludes the halt.** -/
theorem no_parity_invariant (S : List Nat → Prop) (h0 : S (resW 2 l0))
    (hc : ∀ l l', D l → S (resW 2 l) → visit l = some l' → S (resW 2 l')) :
    ∃ l, D l ∧ S (resW 2 l) ∧ visit l = none :=
  no_residue_invariant 2 (Or.inl rfl) S h0 hc

end H175628
