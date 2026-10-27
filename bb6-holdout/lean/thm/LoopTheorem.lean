import EndgameTheorem
import LoopPass
open BB6 BB6.Sym

/-! # The loop's end, for every width

`loop_pass` (R ≥ 4097, R free) and `endgame_no_close` (R ≤ 4096, one tree per R) combined by strong induction on
the right end R: a pass divides R by 16 (or a short branch by 2), so after finitely many passes the run is in the
range of the endgame trees.  `loop_pass` is checked by Lean's kernel; `endgame_no_close` is evaluated with
`native_decide`, so this theorem trusts Lean's compiler as well as its kernel. -/

theorem not_closing {R : Nat} (h : 176 < R) : closingSet.contains R = false := by
  rw [Bool.eq_false_iff]
  intro hc
  simp [closingSet] at hc
  omega

/-- **The loop's end, for every width.**  For every even R ≥ 2 outside the closing set
{2, 4, 8, 16, 24, 32, 48, 64, 176}, and every phase-0 pass start — walls at a, b and c = E − R − 1, width E, with a
odd, b even, E even and every gap at least 448 — the machine runs a number of rounds without halting, reaching a round
start, and every end meeting on the way is at distance at least 3: the run does not close.  The rounds go through
every pass the run completes (each a phase-0 pass start with R divided by 16, or by 2) and stop, per the trees, when
the run leaves the loop or reaches R ≤ 4096 and the endgame tree for that R ends.  So a run through the loop can
close only from a pass start whose R is in the closing set. -/
theorem loop_no_close : ∀ (R : Nat), R % 2 = 0 → 2 ≤ R → closingSet.contains R = false →
    ∀ (a b E : Nat), a % 2 = 1 → b % 2 = 0 → E % 2 = 0 → 448 ≤ a → a + 448 ≤ b → b + 448 + R + 1 ≤ E →
    ∃ n kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = some (roundStart ms' W') ∧
      ∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d := by
  intro R
  induction R using Nat.strongRecOn with
  | ind R ih =>
    intro hR hR2 hS a b E ha hb hE h1 h2 h3
    by_cases hR4 : R ≤ 4096
    · obtain ⟨n, kk, ms', W', hk, -, hm⟩ := endgame_no_close R hR hR2 hR4 hS a b E ha hb hE h1 h2 h3
      exact ⟨n, kk, ms', W', hk, hm⟩
    · obtain ⟨n₁, k₁, ms₁, W₁, hk₁, hr₁, hm₁, hout⟩ :=
        loop_pass R a b E hR (by omega) ha hb hE h1 h2 h3
      rcases hout with hn | ⟨a', b', R', rfl, ha', hb', hW', hR', g1, g2, g3, g176, hlt, -⟩
      · exact ⟨n₁, k₁, ms₁, W₁, hk₁, hm₁⟩
      · obtain ⟨n₂, k₂, ms₂, W₂, hk₂, hm₂⟩ :=
          ih R' hlt hR' (by omega) (not_closing g176) a' b' W₁ ha' hb' hW' g1 g2 g3
        refine ⟨n₁ + n₂, k₁ + k₂, ms₂, W₂, steps_seq hk₁ hk₂, ?_⟩
        rw [meetsRounds_append 1000 n₁ n₂ _ _ _ _ hr₁]
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact hm₁ d hd
        · exact hm₂ d hd
