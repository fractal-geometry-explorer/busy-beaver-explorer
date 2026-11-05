# The 4-wall family against where the run's last pass start can come from (November 4)

This note picks up the open step after PR #114 (`notes/FOUR_WALL_ALL_N.md` on that branch): find an idea other than
the 2-adic handle that keeps the run from blank tape off the 4-wall loop's halting family, for every number of passes.

**Verdict.** No such idea was found, and the family is not ruled out. One new restriction is proved, about where the
chain's last pass start can come from. It removes six of the eight far families that the theorems had exhibited as
meeting every condition, but the untrusted far-shape searches have members that pass it too.

## 1. What was tried and why it does not close

**The 4-wall loop's own lock.** Λ = 3,969τ − 1,890E − 6,615σ + 19,404ρ − 5,391 (PR #90) is 9Λ̃ with Λ̃ ≡ 3 (mod 7) on
every state. That is the same lock as the 3-wall loop's L₁ ≡ 3 (mod 7). A pass divides Λ by 64 ≡ 1 (mod 7), so Λ is
never 0 and n passes need 64ⁿ ≤ |Λ| at the entry. From the pass start, by the prefix forms of
`routes/loop4/build_fam.py` (checked on three members against the mark model):

- r₀ = ρ − 1 = (Q − 4)/16 at the 4-wall entry in round 5, with Q = W − b + 2R + 22. So the number of passes is read off
  v₂(Q − 4) alone, which is why the lane with k = 4n + 7 is the one with n passes.
- Λ₀ = 3(−994W + 23,912R − 31L₁ + 78,816)/32, and 147(Q − 4) = 35W + 686R − L₁ + 2,460, with
  L₁ = 147b − 112W + 392R − 186.

The lock bounds n only by about log₆₄ W. Its congruence is an identity of every state, so like the count mod 3 it
cannot separate anything. The invariant r³/Λ² does not help either. The route after the exit closes once R′ at the re-entry counts
down to the closing set, which asks nothing of Λ's size, so r³/Λ² at the entry can be anything a pass start allows.

**Other moduli.** Every mod-7 and mod-9 relation found (the two locks, and 147(Q − 4) ≡ 0 giving L₁ ≡ 35W + 10
(mod 49)) is an identity of the forms, true at every state, and so excludes nothing. This matches
`integ/INTEGRALITY.md`: the count mod 3 is the only conserved congruence.

**Size against the 2-adic class.** On a lane, Q is fixed. A halt needs b in a class mod about 2^(1.5j), and (W, R, L₁)
are tied by the identity above. Counting lattice points in the region the far shape and the σ-type bounds allow gives
far more than one expected member per lane value. So no size bound alone excludes the lanes, which the far-shape
searches confirm.

**Where the pass start comes from (this is what works, in part).** The chain's last pass start is the loop entry
itself, or the landing of the chain's last step. Each kind of step lands in a narrower shape than the one the theorems
kept:

| last pass start | shape |
|---|---|
| the loop entry (no step) | W ≤ 32R (`EntryWide`) |
| a round-7 landing | 32R ≥ 3E + 5R + 559, so W ≤ 32R |
| a half-pass landing (only from the entry) | W ≤ 64R + 6 and 2(W − b) + 900 ≤ W + 2R |
| a full-pass landing | 15W + 144R + 375 ≤ 64(W − b) ≤ 16W + 128R − 994 |

The upper side of the full pass's window comes from the start's first two gaps: b ≥ 896 there, and
b′ = (b + 48E − 8R + 1,250)/64. So a full pass leaves the middle wall about three quarters of the width from the
start, or further. `thm/FarHalt.lean` kept only 15W ≤ 64(W − b). The window was in the untrusted shape check
(`shape.py` in the halting-classes project files) but in no theorem.

## 2. In Lean: `thm/WindowHalt.lean`

- `step_window`, `LoopChain.window_end`: from a loop entry with W ≤ 32R, every pass start of the chain has
  `WindowShape`, that is W ≤ 32R, or W ≤ 64R + 6 with 2(W − b) + 900 ≤ W + 2R, or the full pass's window.
- `entry_window_halt`, `WindowQ`, `blank_halt_open_window`: `blank_halt_open_wide` with that shape at the pass start.
- `windowOutFams_out` (`decide +kernel`) and `blank_halt_not_window_family`: the run from blank tape halts through none
  of six far families. These are the families of `loop2_far_wide`, the first of `loop3_far_wide`, `loop3_far_66`,
  `loop4_far_66` and `loop5_far_66` (`thm/LoopFarHalt.lean`), and `loop4_far_66c` (PR #114's
  `thm/LoopFarCount.lean`). Each has its base member below the window and its next member (width + 2^k) far above
  it, and R < W/64.

Of the eight far families, two are left:

- The second of `loop3_far_wide` (R/W = 0.052) is ruled out by the count instead: W ≡ 0 (mod 6), PR #114.
- `loop5_far_66c` (R/W = 0.0445, (W − b)/W = 0.667, W ≡ 2 mod 6) has W ≤ 32R. It is no round-7 landing (32R < 3W),
  no half-pass landing (2(W − b) > W + 2R) and outside the window. So the run reaches it only as **a loop entry
  itself**, with a chain of no steps. Whether some clean tape enters the loop there is the open clean-tape question
  again.

So PR #114's sentence "the count does not keep the family off" now rests on `loop5_far_66c` alone among the proved
members. It still stands: `far_shape.md` counts, at 2⁶⁶, 258 of the 319 four-pass far members and 16 of the 19
five-pass ones with W ≤ 64R + 6, and 57 and 5 inside the region of the run's own loop entries (untrusted). Those
members can be loop entries, which this argument cannot exclude.

## 3. What this leaves

A halting pass start of the 4-wall family that the run reaches must, beyond the earlier conditions, be a loop entry
(W ≤ 32R), a half-pass landing from one, a round-7 landing, or a full-pass landing in the two-sided window. For the
first case the question is the clean tape before the entry. That is the same open question as before, now narrowed:
the entry has to be the halting pass start itself, not something many steps before it. The other three cases are
landings whose predecessor pass start is fixed by the step's map, so they can be pulled back. A full-pass landing pulls
back to a pass start with R′ = 16R and L₁′ = 64L₁, and that one must again be a root or a landing, so the chain must
end at a root. One consequence (not in Lean): (W + 2R)·L₁² ≤ 2³⁷·R³ at every pass start of the chain, because it
holds at every pass start with W ≤ 64R + 6 and a full pass keeps it.

Next steps that could still help, in order of cost:

1. Re-run the far-shape census at 2⁶⁶ for n = 4 and 5 (`tools/routes/far/loop/`, a few minutes per census once
   `check_end.sh` has built the native library). Count the members with `WindowShape` and W ≡ 2 (mod 6), and split
   them by which root they would need. Members that can only be loop entries could then be checked against the entry
   classes of the 40-digit clean-tape tree. That check is untrusted and finite, and only covers entries the tree
   settles.
2. Pull the window's full-pass landings back step by step to their root, as above. It is exact and cheap, and it turns
   a member in the window into a single root to test.

Neither gives a proof for every number of passes. As PR #114 found, what remains is the clean tapes that no tree
settles.

## Checks

- `thm/WindowHalt.lean` compiles in about 2 s with Lean 4.34.0 after `check.sh` and `check_end.sh` through
  `thm/WideHalt.lean` and `thm/LoopFarHalt.lean`. It is added to `check_end.sh` beside `thm/FarHalt.lean`.
- No `sorry`. `step_window` and `LoopChain.window_end` depend on propext and Quot.sound, `windowOutFams_out` on no
  axioms, and `blank_halt_open_window` and `blank_halt_not_window_family` on the axioms of `blank_halt_open_wide`
  (with its two `native_decide` axioms).
- The identities of section 1 (r₀ = (Q − 4)/16, the forms for Λ₀ and 147(Q − 4), and Λ ≡ 6 mod 7) were checked against
  the mark model on members of the n = 1 and n = 2 families and on `loop2_far_wide` (untrusted, Python).
