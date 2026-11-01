import Seven

/-!
# The blank-tape orbit and the seven-block excursion: a window below `a7`

`Seven.lean` shows that the excursion from the two-block pass start `[a7, 2·a7 + 1]`, a7 = 2^203 + 2^221 + 1, reaches
7 blocks. This file shows that the blank-tape orbit cannot step around it: **if the orbit returns to a two-block state
`[a, 2a+1]` with a = a7 − 12j for any j ≤ 200, it reaches `[a7, 2·a7 + 1]` exactly, and then a pass start with 7
blocks** (`window_seven`, kernel).

Read the other way (`six_blocks_long_excursion`): if every pass start of the orbit has at most 6 blocks, then the
orbit misses all 201 states `[a7 − 12j, 2(a7 − 12j) + 1]`, j ≤ 200. Those are the only states `[a, 2a+1]` with
a = 5 mod 12 that can occur in passes `n₂₀₀ .. n₀` (a pass start has 4n ones, so `[a, 2a+1]` can only be pass
(3a+1)/4), so the orbit would spend 1,800 passes in a row without a return of the return map (its returns are
`[a, 2a+1]` with a = 5 mod 12, computed). Along the 10⁶ returns computed from blank tape an excursion lasts at most 36
passes, and the 7-block excursion itself 216 (`notes/LAB_NOTES.md`, 1 November).

Each step of the window is one excursion, `run (9k)` with k = 1 or 2, computed by the kernel (`decide`, no
`native_decide`).
-/

namespace BB6d

/-- `m` more passes from a pass start of the orbit. -/
theorem orbit_run : ∀ (m n : Nat) (zs out : List Nat), orbit n = .ok zs → run m zs = .ok out →
    orbit (n + m) = .ok out
  | 0, n, zs, out, h, hr => by
    simp only [run, Next.ok.injEq] at hr
    subst hr; exact h
  | m + 1, n, zs, out, h, hr => by
    simp only [run] at hr
    cases hn : next zs with
    | ok ys =>
      rw [hn] at hr
      have h1 : orbit (n + 1) = .ok ys := by simp only [orbit, h, hn]
      have := orbit_run m (n + 1) ys out h1 hr
      rwa [show n + 1 + m = n + (m + 1) by omega] at this
    | halt => rw [hn] at hr; cases hr
    | one => rw [hn] at hr; cases hr

/-- The two-block pass start `[a, 2a+1]`, nearest block first. -/
def two (a : Nat) : List Nat := [2 * a + 1, a]

/-- The window: a7 − 12j. -/
def aw (j : Nat) : Nat := a7 - 12 * j

/-- The width of the window. -/
def W : Nat := 200

/-- The excursion from `[aw j, …]` returns to `[aw (j−1), …]` after 9 passes or to `[aw (j−2), …]` after 18. -/
def stepOK (j : Nat) : Bool :=
  decide (run 9 (two (aw j)) = .ok (two (aw (j - 1)))) ||
    (decide (2 ≤ j) && decide (run 18 (two (aw j)) = .ok (two (aw (j - 2)))))

/-- `stepOK` for 1 ≤ j ≤ n. -/
def allOK : Nat → Bool
  | 0 => true
  | j + 1 => stepOK (j + 1) && allOK j

/-- Every step of the window, computed by the kernel (1,881 passes on numbers of 223 bits). -/
theorem allOK_W : allOK W = true := by decide

theorem allOK_le : ∀ (n j : Nat), allOK n = true → 1 ≤ j → j ≤ n → stepOK j = true
  | 0, j, _, h1, h2 => by omega
  | n + 1, j, h, h1, h2 => by
    simp only [allOK, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge j (n + 1) with hl | hl
    · exact allOK_le n j h.2 h1 (by omega)
    · rw [show j = n + 1 by omega]; exact h.1

/-- From any state of the window the orbit reaches `[a7, 2·a7 + 1]`. -/
theorem window_reach : ∀ (j n : Nat), j ≤ W → orbit n = .ok (two (aw j)) → ∃ m, orbit m = .ok (two a7)
  | j, n, hj, h => by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; exact ⟨n, by simpa [aw] using h⟩
    · have hs := allOK_le W j allOK_W hpos hj
      simp only [stepOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
      rcases hs with h9 | ⟨h2, h18⟩
      · exact window_reach (j - 1) (n + 9) (by omega) (orbit_run 9 n _ _ h h9)
      · exact window_reach (j - 2) (n + 18) (by omega) (orbit_run 18 n _ _ h h18)
termination_by j => j

/-- **If the blank-tape orbit returns to `[a, 2a+1]` with a = a7 − 12j, j ≤ 200, it reaches a pass start with 7
blocks.** -/
theorem window_seven (j n : Nat) (hj : j ≤ W) (h : orbit n = .ok (two (aw j))) :
    ∃ m zs, orbit m = .ok zs ∧ zs.length = 7 := by
  obtain ⟨m, hm⟩ := window_reach j n hj h
  have h7 := blocks7_204
  unfold blocks7 at h7
  cases hr : run 204 [2 * a7 + 1, a7] with
  | ok zs =>
    rw [hr] at h7
    exact ⟨m + 204, zs, orbit_run 204 m _ zs hm hr, h7⟩
  | halt => rw [hr] at h7; cases h7
  | one => rw [hr] at h7; cases h7

/-- A two-block state `[a, 2a+1]` of the orbit can only be pass (3a+1)/4 (pass n has 4n ones). -/
theorem two_pass (n a : Nat) (h : orbit n = .ok (two a)) : 4 * n = 3 * a + 1 := by
  have := (orbit_ok n _ h).1
  simp [two] at this
  omega

/-- **Read the other way.** If no pass start of the orbit has 7 blocks (in particular, if every one has at most 6),
then none of the passes (3(a7 − 12j) + 1)/4, j ≤ 200, is the state `[a7 − 12j, 2(a7 − 12j) + 1]`: 1,800 passes in a
row with no state `[a, 2a+1]`, a = 5 mod 12. -/
theorem six_blocks_long_excursion (h6 : ∀ m zs, orbit m = .ok zs → zs.length ≤ 6) :
    ∀ n a, orbit n = .ok (two a) → a % 12 = 5 → a7 - 12 * W ≤ a → a ≤ a7 → False := by
  intro n a h h5 hlo hhi
  have h12 : a7 % 12 = 5 := a7_mod12
  have hj : a = aw ((a7 - a) / 12) := by simp only [aw]; omega
  rw [hj] at h
  obtain ⟨m, zs, hm, hl⟩ := window_seven _ n (by simp only [W] at hlo ⊢; omega) h
  have := h6 m zs hm
  omega

end BB6d
