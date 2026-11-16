import Reduce
import Xor

/-!
# 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA: the macro machine is the XOR sweep

At a turn configuration (`RT out`, at the right end of the tape) the reversed word is `true :: out` (the head pair,
then the pairs to its left).  `mstep_ok`: when that word has a `00`, one macro step of `Sweep.lean` is exactly one
XOR sweep `XS.swr` (`Xor.lean`), in `4 d + 14` steps, `d` being where the `00` was found; `mstep_halt`: a `00` only
at the very left end halts the machine.  Everything is checked by Lean's kernel.
-/

namespace H25821

open TM XS

theorem apass_eq : ∀ (cs q : List Bool), apass cs q = ((q.map (!·)).reverse ++ cs, 2 * q.length + 3)
  | cs, [] => rfl
  | cs, a :: q => by
    show ((apass ((!a) :: cs) q).1, (apass ((!a) :: cs) q).2 + 2) = _
    rw [apass_eq]
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      Prod.mk.injEq, true_and]
    omega

/-- The left pass against the sweep, for any pairs `m` already passed. -/
theorem scan_ok : ∀ (l m X : List Bool) (d : Nat), swr (true :: l) = .ok d X →
    ∃ cs c mn, scan true l m = .turn (2 * mn.length + 5) cs (c :: true :: false :: (mn ++ m)) ∧
      X = (mn.map (!·)).reverse ++ true :: false :: (!c) :: cs ∧ d = mn.length + 1
  | [], _, _, _, h => by simp [swr] at h
  | [false], _, _, _, h => by simp [swr, SW.pre] at h
  | [false, false], _, _, _, h => by simp [swr, SW.pre] at h
  | false :: false :: c :: cs, m, X, d, h => by
    simp only [swr, SW.pre, SW.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨cs, c, [], rfl, rfl, rfl⟩
  | true :: bs, m, X, d, h => by
    rw [swr_cons _ _ _ (by simp)] at h
    obtain ⟨d', X', h1, rfl, rfl⟩ := SW.pre_eq_ok h
    obtain ⟨cs, c, mn, h2, rfl, rfl⟩ := scan_ok bs (true :: m) X' d' h1
    refine ⟨cs, c, mn ++ [true], ?_, ?_, ?_⟩
    · show (scan true bs (true :: m)).add 2 = _
      rw [h2]; simp only [SR.add, List.append_assoc, List.singleton_append, List.length_append,
        List.length_singleton, SR.turn.injEq, and_true]; omega
    · simp
    · simp
  | false :: true :: cs, m, X, d, h => by
    rw [swr_cons _ _ _ (by simp), swr_cons _ _ _ (by simp)] at h
    obtain ⟨d', X', h1, rfl, rfl⟩ := SW.pre_eq_ok h
    obtain ⟨d'', X'', h1', rfl, rfl⟩ := SW.pre_eq_ok h1
    obtain ⟨cs', c, mn, h2, rfl, rfl⟩ := scan_ok cs (false :: false :: m) X'' d'' h1'
    refine ⟨cs', c, mn ++ [false, false], ?_, ?_, ?_⟩
    · show ((scan true cs (false :: false :: m)).add 2).add 2 = _
      rw [h2]; simp only [SR.add, List.append_assoc, List.cons_append, List.nil_append, List.length_append,
        List.length_cons, List.length_nil, SR.turn.injEq, and_true]; omega
    · simp
    · simp only [List.length_append, List.length_cons, List.length_nil]

theorem scan_halt : ∀ (l m : List Bool), swr (true :: l) = .halt → ∃ n, scan true l m = .halt n
  | [], _, h => by simp [swr] at h
  | [false], _, h => by simp [swr, SW.pre] at h
  | [false, false], _, _ => ⟨4, rfl⟩
  | false :: false :: c :: cs, _, h => by simp [swr, SW.pre] at h
  | true :: bs, m, h => by
    rw [swr_cons _ _ _ (by simp)] at h
    obtain ⟨n, hn⟩ := scan_halt bs (true :: m) (SW.pre_eq_halt h)
    exact ⟨n + 2, by show (scan true bs (true :: m)).add 2 = _; rw [hn]; rfl⟩
  | false :: true :: cs, m, h => by
    rw [swr_cons _ _ _ (by simp), swr_cons _ _ _ (by simp)] at h
    obtain ⟨n, hn⟩ := scan_halt cs (false :: false :: m) (SW.pre_eq_halt (SW.pre_eq_halt h))
    exact ⟨n + 4, by show ((scan true cs (false :: false :: m)).add 2).add 2 = _; rw [hn]; rfl⟩

/-- **One macro step is one XOR sweep.** -/
theorem mstep_ok (out X : List Bool) (d : Nat) (h : swr (true :: out) = .ok d X) :
    mstep (.rt out) = .go (4 * d + 14) (.rt (true :: X)) := by
  obtain ⟨cs, c, mn, h1, rfl, rfl⟩ := scan_ok out [false] X d h
  simp only [mstep]
  rw [h1]
  simp only [apass_eq, List.map_cons, List.map_append, List.reverse_cons, List.reverse_append, List.length_cons,
    List.length_append, List.map_nil, List.reverse_nil, List.length_nil, MR.go.injEq]
  constructor
  · omega
  · simp

/-- A `00` only at the very left end: the macro step halts. -/
theorem mstep_halt (out : List Bool) (h : swr (true :: out) = .halt) : ∃ n, mstep (.rt out) = .halt n := by
  obtain ⟨n, hn⟩ := scan_halt out [false] h
  exact ⟨n + 2, by simp only [mstep]; rw [hn]⟩

end H25821
