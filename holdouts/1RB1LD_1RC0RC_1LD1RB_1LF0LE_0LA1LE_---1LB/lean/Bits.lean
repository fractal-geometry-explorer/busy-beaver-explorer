import Reduce
import Xor

/-!
# 1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB: the pass machine is the XOR sweep

At a turn at the right end of the tape (`RT out []`) the reversed word is `true :: out` (the head pair, then the
pairs to its left).  `mstep_ok`: when that word has a `00`, one macro step of `Sweep.lean` is exactly one XOR
sweep `XS.swr` (`Xor.lean`), in `4 d + 12` steps, `d` being where the `00` was found; `mstep_halt`: a `00` only at
the very left end halts the machine.  Everything is checked by Lean's kernel.
-/

namespace H117020

open TM XS

theorem apass_cells : ∀ (cs q : List Bool),
    apass cs (cells q) = .go (2 * q.length + 2) ((q.map (!·)).reverse ++ cs) []
  | cs, [] => rfl
  | cs, a :: q => by
    show (apass ((!a) :: cs) (cells q)).add 2 = _
    rw [apass_cells]
    simp only [MR.add, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, MR.go.injEq, and_true]
    omega

/-- The left pass against the sweep, for any pairs `m` already passed. -/
theorem scan_ok : ∀ (l : List Bool) (b : Bool) (m X : List Bool) (d : Nat), swr (true :: l) = .ok d X →
    ∃ cs c mn, scanF l b m = .turn (2 * mn.length + 5) cs (c :: true :: false :: (mn ++ b :: m)) ∧
      X = (mn.map (!·)).reverse ++ true :: false :: (!c) :: cs ∧ d = mn.length + 1
  | [], _, _, _, _, h => by simp [swr] at h
  | [false], _, _, _, _, h => by simp [swr, SW.pre] at h
  | [false, false], _, _, _, _, h => by simp [swr, SW.pre] at h
  | false :: false :: c :: cs, b, m, X, d, h => by
    simp only [swr, SW.pre, SW.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨cs, c, [], rfl, rfl, rfl⟩
  | true :: bs, b, m, X, d, h => by
    rw [swr_cons _ _ _ (by simp)] at h
    obtain ⟨d', X', h1, rfl, rfl⟩ := SW.pre_eq_ok h
    obtain ⟨cs, c, mn, h2, rfl, rfl⟩ := scan_ok bs true (b :: m) X' d' h1
    refine ⟨cs, c, mn ++ [true], ?_, ?_, ?_⟩
    · show (scanF bs true (b :: m)).add 2 = _
      rw [h2]; simp only [SR.add, List.append_assoc, List.singleton_append, List.length_append,
        List.length_singleton, SR.turn.injEq, and_true]; omega
    · simp
    · simp
  | false :: true :: cs, b, m, X, d, h => by
    rw [swr_cons _ _ _ (by simp), swr_cons _ _ _ (by simp)] at h
    obtain ⟨d', X', h1, rfl, rfl⟩ := SW.pre_eq_ok h
    obtain ⟨d'', X'', h1', rfl, rfl⟩ := SW.pre_eq_ok h1
    obtain ⟨cs', c, mn, h2, rfl, rfl⟩ := scan_ok cs false (false :: b :: m) X'' d'' h1'
    refine ⟨cs', c, mn ++ [false, false], ?_, ?_, ?_⟩
    · show (scanF cs false (false :: b :: m)).add 4 = _
      rw [h2]; simp only [SR.add, List.append_assoc, List.cons_append, List.nil_append, List.length_append,
        List.length_cons, List.length_nil, SR.turn.injEq, and_true]; omega
    · simp
    · simp only [List.length_append, List.length_cons, List.length_nil]

theorem scan_halt : ∀ (l : List Bool) (b : Bool) (m : List Bool), swr (true :: l) = .halt → ∃ n, scanF l b m = .halt n
  | [], _, _, h => by simp [swr] at h
  | [false], _, _, h => by simp [swr, SW.pre] at h
  | [false, false], _, _, _ => ⟨4, rfl⟩
  | false :: false :: c :: cs, _, _, h => by simp [swr, SW.pre] at h
  | true :: bs, b, m, h => by
    rw [swr_cons _ _ _ (by simp)] at h
    obtain ⟨n, hn⟩ := scan_halt bs true (b :: m) (SW.pre_eq_halt h)
    exact ⟨n + 2, by show (scanF bs true (b :: m)).add 2 = _; rw [hn]; rfl⟩
  | false :: true :: cs, b, m, h => by
    rw [swr_cons _ _ _ (by simp), swr_cons _ _ _ (by simp)] at h
    obtain ⟨n, hn⟩ := scan_halt cs false (false :: b :: m) (SW.pre_eq_halt (SW.pre_eq_halt h))
    exact ⟨n + 4, by show (scanF cs false (false :: b :: m)).add 4 = _; rw [hn]; rfl⟩

/-- **One macro step at the right end is one XOR sweep.** -/
theorem mstep_ok (out X : List Bool) (d : Nat) (h : swr (true :: out) = .ok d X) :
    mstep out [] = .go (4 * d + 12) (true :: X) [] := by
  obtain ⟨cs, c, mn, h1, rfl, rfl⟩ := scan_ok out false [] X d h
  unfold mstep
  rw [h1]
  simp only [List.append_nil]
  rw [apass_cells]
  simp only [MR.add, List.map_cons, List.map_append, List.reverse_cons, List.reverse_append, List.length_cons,
    List.length_append, List.map_nil, List.reverse_nil, List.length_nil, MR.go.injEq, and_true]
  constructor
  · omega
  · simp

/-- A `00` only at the very left end: the macro step halts. -/
theorem mstep_halt (out : List Bool) (h : swr (true :: out) = .halt) : ∃ n, mstep out [] = .halt n := by
  obtain ⟨n, hn⟩ := scan_halt out false [] h
  exact ⟨n + 1, by unfold mstep; rw [hn]⟩

end H117020
