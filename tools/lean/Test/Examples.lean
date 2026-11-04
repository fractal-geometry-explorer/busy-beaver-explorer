import Test.BB2
import Test.BB4
import Test.Loop2Cert

/-! Tests of the shared library on machines whose behaviour is known. -/

open TM

namespace Test

/-- BB(2)'s champion halts from blank tape after 6 steps (5 ordinary ones, then the halting transition),
checked by the kernel. -/
theorem bb2_halts : BB2.HaltsFromBlank :=
  blank_halts BB2.trans (n := 5) (c := ⟨[true], [true, true, true], .B⟩) (by decide) (by decide)

/-- BB(4)'s champion halts after 107 steps, by the kernel. -/
theorem bb4_halts_107 : ∃ c, BB4.fsteps 106 (FCfg.blank .A) = some c ∧ BB4.fstep c = none := by
  refine ⟨_, rfl, ?_⟩
  decide

theorem bb4_halts : BB4.HaltsFromBlank := by
  obtain ⟨c, h, hc⟩ := bb4_halts_107
  exact blank_halts BB4.trans h hc

/-- ... and not before: the first 106 steps are ordinary ones. -/
theorem bb4_runs_106 : ∃ c, BB4.steps 106 BB4.init = some c :=
  blank_runs BB4.trans (by decide)

/-- The same run by `native_decide` (trusts the compiler as well as the kernel). -/
theorem bb4_halts_native : (BB4.fsteps 107 (FCfg.blank .A)).isNone := by native_decide

/-- A shift rule: in BB(4)'s state D, `D> 0^k` writes `1^k` and moves right (one step a cell), for every k and any
surrounding tape. -/
theorem bb4_d_sweep (k : Nat) (L R : Tape) :
    BB4.steps (k * 1) ⟨app [] L, rep k [false] R, .D⟩ = some ⟨app [] (rep k [true] L), R, .D⟩ :=
  cross_r BB4.trans (u := []) (w := [false]) (v := [true]) (fun _ _ => rfl) k L R

/-- A leftward shift rule with a carried word, on a two-state table made for the test: state `false` moves
left writing `1` on `0` and `0` on `1`, so the `0` under the head travels left across `(0 1)^k`, turning it into
`(0 1)^k` written the other way round. -/
def sweepL : Bool → Bool → Option (Bool × Dir × Bool)
  | false, false => some (true, .L, false)
  | false, true => some (false, .L, false)
  | true, _ => none

/-- In `sweepL`, state `false` sweeps left inverting each cell; the head carries no word. -/
theorem sweepL_cross (k : Nat) (L R : Tape) :
    steps sweepL (k * 2) ⟨rep k [true, false] L, app [false] R, false⟩
      = some ⟨L, app [false] (rep k [false, true] R), false⟩ :=
  cross_l sweepL (u := [false]) (w := [true, false]) (v := [false, true]) (fun _ _ => rfl) k L R

/-- A closed tape language (`Loop2Cert.lean`, windows of two cells) proves that 1RB0LB_0LA--- never halts from
blank tape: the language allows no halt. -/
theorem loop2_never_halts : ¬ Loop2.HaltsFromBlank :=
  CTL.not_halts Loop2.trans (ML := Loop2.certL) (MR := Loop2.certR) (S := Loop2.certS) (by decide) (by decide)
    (by decide)

end Test
