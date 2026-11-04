import Pass

/-!
# An excursion with seven blocks

The reduction of 1 November (`notes/LAB_NOTES.md`) needs every list along the blank-tape orbit to have at most 6
blocks. On every excursion class of the return map down to a mod 2^66 that holds, and only 6 blocks with ψ = 24
occur. This file shows that the bound fails for excursions in general: from the two-block pass start `[a, 2a+1]`
with

    a = 2^203 + 2^221 + 1     (a = 5 mod 12, the residue of every two-block state of the blank orbit)

the machine reaches, 204 passes later, a pass start with **7 blocks**, and after 216 passes it is back at
`[a + 288, 2(a + 288) + 1]` (an ordinary excursion, k = 24, no stop at a block of 1 on the way).

The lists are computed by the kernel (`decide`, no `native_decide`), and `run_reach` turns them into runs of the
machine with `pass`. Whether the blank-tape orbit itself passes through `[a, 2a+1]` for this a is not proved:
the orbit's states `[a, 2a+1]` run through about 95% of the a = 5 mod 12 in increasing order (computed), and every a
that agrees with this one mod 2^222 has the same first 216 passes, so it is expected but far out of reach.
-/

namespace BB6d

open TM

/-- `n` passes of the closed form from `zs` (stops at a halt or a stop block of 1). -/
def run : Nat → List Nat → Next
  | 0, zs => .ok zs
  | n + 1, zs =>
    match next zs with
    | .ok out => run n out
    | e => e

/-- The machine follows `run`: from the pass start of `zs` it reaches the pass start of `run n zs`. -/
theorem run_reach : ∀ (n : Nat) (zs out : List Nat), run n zs = .ok out →
    Reach ⟨enc zs, blank, .A⟩ ⟨enc out, blank, .A⟩
  | 0, zs, out, h => by
    simp only [run, Next.ok.injEq] at h
    subst h; exact Reach.refl _
  | n + 1, zs, out, h => by
    simp only [run] at h
    cases hn : next zs with
    | ok ys =>
      rw [hn] at h
      obtain ⟨k, hk⟩ := pass zs ys hn
      exact Reach.trans (Reach.of hk) (run_reach n ys out h)
    | halt => rw [hn] at h; cases h
    | one => rw [hn] at h; cases h

/-- The start of the excursion. -/
def a7 : Nat := 2 ^ 203 + 2 ^ 221 + 1

theorem a7_mod12 : a7 % 12 = 5 := by decide

/-- The number of blocks after `n` passes from `[a7, 2·a7 + 1]` (0 if the run stopped). -/
def blocks7 (n : Nat) : Nat :=
  match run n [2 * a7 + 1, a7] with
  | .ok zs => zs.length
  | _ => 0

/-- 204 passes after `[a7, 2·a7 + 1]` the pass start has 7 blocks (kernel). -/
theorem blocks7_204 : blocks7 204 = 7 := by decide

/-- The excursion returns to `[a7 + 288, 2(a7 + 288) + 1]` after 216 passes (kernel). -/
theorem return7 : run 216 [2 * a7 + 1, a7] = .ok [2 * (a7 + 288) + 1, a7 + 288] := by decide

/-- **The block count is not bounded by 6 on excursions.** From the pass start `[a, 2a+1]`, a = 2^203 + 2^221 + 1
(a = 5 mod 12), the machine reaches a pass start with 7 blocks. -/
theorem seven_blocks : ∃ zs : List Nat, zs.length = 7 ∧
    Reach ⟨enc [2 * a7 + 1, a7], blank, .A⟩ ⟨enc zs, blank, .A⟩ := by
  have h := blocks7_204
  unfold blocks7 at h
  cases hr : run 204 [2 * a7 + 1, a7] with
  | ok zs =>
    rw [hr] at h
    exact ⟨zs, h, run_reach 204 _ zs hr⟩
  | halt => rw [hr] at h; cases h
  | one => rw [hr] at h; cases h

end BB6d
