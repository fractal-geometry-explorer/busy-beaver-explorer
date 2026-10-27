import BB6.Ends
import BB6.BlockHalt

/-!
# Pass starts that halt: an eighth of R = 6

The pass-start trees (`thm/PassHalt.lean`) cut a path where a round is decided as something other than a new round
start, and for R = 6 that happens on an eighth of the class, at every depth.  Those pass starts halt.  From a phase-0
pass start with R = 6, b ≡ 2 (mod 8), W ≡ 2 (mod 4) and every gap at least 448, the round model runs six rounds, to
round starts with the marks B W, M W (meeting the end at distances 4 and 6 on the way), W W, a block five cells before
the width, W W (meeting the end at distance 2) and a block three cells before the width, decided on the whole class
(`r6Check`, evaluated by the kernel).  In the seventh round the gap meets the end at distance 0, which the model
leaves uncovered, and the machine halts (`block_end_halt'`).  So the cut classes of `pass_halt_chain` contain pass
starts that really halt, at every width (`pass_r6_halt`).
-/

namespace BB6
open BB6.Sym

/-- The class, in the coordinates z = ((a − 1)/2, (b − 2)/8, (W − 2)/4): walls at a = 2 z₀ + 1, b = 8 z₁ + 2 and
c = W − 7 = 4 z₂ − 5, width W = 4 z₂ + 2, with the cone gaps a, b − a and c − b. -/
def r6Start : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0, 0]⟩
  let b : YForm := ⟨2, [0, 8, 0]⟩
  let W : YForm := ⟨2, [0, 0, 4]⟩
  let c := W.addc (-7)
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], W, [a, b.sub a, c.sub b])

/-- Six rounds on the class end at a round start whose only mark is a block three cells before the width, which is
odd and above 8. -/
def r6Check : Bool :=
  match symRoundsZ r6Start.2.2 448 1000 6 r6Start.1 r6Start.2.1 with
  | some (.newRound [⟨.B, p⟩] w) =>
    decide (p = w.addc (-3)) && w.modDec 2 == some 1 && ltDec (YForm.const 8) w r6Start.2.2 448 == some true
  | _ => false

theorem r6Check_ok : r6Check = true := by decide +kernel

/-- **An eighth of the pass starts with R = 6 halt.**  From every phase-0 pass start with right end 6, every gap at
least 448, b ≡ 2 (mod 8) and W ≡ 2 (mod 4), the machine halts: six rounds to a block three cells before the width,
then the seventh round. -/
theorem pass_r6_halt (a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - 6 - 1⟩] W 6) (hb : b % 8 = 2)
    (hW : W % 4 = 2) : ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - 6 - 1⟩] W) = none := by
  obtain ⟨a₀, b₀, hms, ha, hb2, hE, -, -, h1, h2, h3⟩ := hP
  simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
  obtain ⟨rfl, rfl⟩ := hms
  let z : List Int := [((a : Int) - 1) / 2, ((b : Int) - 2) / 8, ((W : Int) - 2) / 4]
  have hz : inCone r6Start.2.2 448 z := by
    intro f hf
    simp only [r6Start, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl <;>
      simp only [z, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
  have hs : agL z r6Start.1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - 6 - 1⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, z, YForm.eval, YForm.addc, dot] <;> omega
  have hWz : agN z r6Start.2.1 W := by simp only [agN, z, r6Start, YForm.eval, dot]; omega
  have hwf : roundWF [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - 6 - 1⟩] W := by
    simp only [roundWF, rightOK, mval, mlen, iff_true]
    omega
  have hc := r6Check_ok
  unfold r6Check at hc
  generalize hr : symRoundsZ r6Start.2.2 448 1000 6 r6Start.1 r6Start.2.1 = r at hc
  rcases r with _ | ⟨_ | _⟩ <;> try (simp at hc; done)
  rename_i ss₆ w
  rcases ss₆ with _ | ⟨⟨t, p⟩, _ | _⟩ <;> try (simp at hc; done)
  cases t <;> try (simp at hc; done)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨hp, hodd⟩, h8⟩ := hc
  have hag := symRoundsZ_sound r6Start.2.2 448 hz 1000 6 _ _ _ _ _ hs hWz hr
  generalize hcr : roundsZ 1000 6 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - 6 - 1⟩] W = cr at hag
  cases cr with
  | newRound ms₆ W₆ =>
    rcases ms₆ with _ | ⟨⟨t, q⟩, _ | ⟨m₂, ms⟩⟩
    · exact absurd hag.1 id
    · obtain ⟨⟨ht, hq⟩, -⟩ := hag.1
      have hw := hag.2
      cases ht
      have hw2 := eval_mod w 2 1 hodd z
      have hw8 := (ltDec_sound _ _ _ 448 z hz true h8).mpr rfl
      simp only [eval_const] at hw8
      unfold agN at hq hw
      rw [hp, eval_addc] at hq
      have hq₂ : (q : Int) = w.eval z + -3 := hq
      have hq' : q = W₆ - 3 := by omega
      subst hq'
      obtain ⟨kk, hk, -⟩ := rounds_run 1000 6 _ W hwf (by rw [hcr]; intro h; cases h)
      rw [hcr] at hk
      exact ⟨kk + (W₆ + 65), steps_seq_none hk (block_end_halt' W₆ (by omega) (by omega))⟩
    · exact absurd hag.1.2 id
  | _ => exact absurd hag id

/-- For example the pass start with walls at 743, 1,802 and 3,319 and width 3,326 (the machine halts after 11,362,209
steps from it, by the simulators). -/
theorem pass_r6_halt_example : ∃ T, steps T (roundStart [⟨.W, 743⟩, ⟨.W, 1802⟩, ⟨.W, 3319⟩] 3326) = none :=
  pass_r6_halt 743 1802 3326 ⟨743, 1802, rfl, by decide⟩ (by decide) (by decide)

#print axioms pass_r6_halt

end BB6
