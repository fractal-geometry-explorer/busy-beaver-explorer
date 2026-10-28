import PassHalt

/-!
# Pass starts that reach a clean tape at once: the clean classes

A phase-0 pass start whose right end R is a multiple of 4, at least 8, and whose middle wall b is 2 mod 8, so that its
left countdown L₁ = 147b − 112W + 392R − 186 is 4 mod 8, reaches a one-marker clean tape wider than the start after five
rounds, whatever its first wall and width (`pass_clean_l4`).  So do those with b ≡ 14 (mod 32), L₁ ≡ 16 (mod 32), when R
is a multiple of 8, at least 16, after seven rounds (`pass_clean_l16`).  `pass_clean8`, `pass_clean16` and
`pass_clean24` are the cases R ≡ 0 (mod 8), R ≡ 0 (mod 16) and R ≡ 24 (mod 32).  Each class is one branch of the
pass-start tree with every coordinate free: the explorer's round steps to a clean leaf, with no split (`cleanTree`),
checked by the kernel (`decide +kernel`) and read through `PTree.sound` with the landing flag off, so a clean tape is
the only way out.  (Scanning R mod 32 from 34 and b mod 64, these two are the only classes that go straight to a clean
tape within 15 rounds, and neither floor can be lowered: from R = 4 the first class, and from R = 8 the second, reach no
clean leaf on a straight branch within 13 rounds.)

What it is for: at a phase-0 pass start L₁ is even and 3 mod 7, so L₁ ≡ 10 (mod 14), and the only such value with
|L₁| < 10 is −4, which is 4 mod 8.  So a pass start with R ≡ 0 (mod 4), R ≥ 8 and |L₁| < 10 reaches a clean tape at
once (`pass_clean_small4`; `pass_clean_small` for R ≡ 0 mod 8), and the last pass start before a halt, if its right
end r is a multiple of 4 from 8 up, has |L₁| ≥ 10 and R³/L₁² ≤ r³/100.  The right ends below 178 that a lane value
2^j or 3·2^j allows are 2^i and 3·2^i; from 8 up they are all multiples of 4 (2, 4 and 6 are the others).  The census
of the lines (r, L₁) that the routes' open paths need (`halting-classes/routes/small_ends.txt` in the project files,
untrusted) finds these classes as the lines that go wholly to clean tapes.
-/

namespace BB6
open BB6.Sym

/-- The class of phase-0 pass starts with walls at a = 1 + 2z₀, b = `b₀` + `bm`·z₁ and W − R − 1, width W = 4z₂ and
right end R = `R₀` + `Rm`·z₃, every gap at least 448 and R ≥ `R₀`: the round start's marks, width and cone, and the
start's forms (width, right end, left countdown). -/
def cleanStart (bm b₀ Rm R₀ : Int) : SState × SForms :=
  let a : YForm := ⟨1, [2, 0, 0, 0]⟩
  let b : YForm := ⟨b₀, [0, bm, 0, 0]⟩
  let E : YForm := ⟨0, [0, 0, 4, 0]⟩
  let R : YForm := ⟨R₀, [0, 0, 0, Rm]⟩
  let c := (E.sub R).addc (-1)
  (([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b, R.addc (448 - R₀)]), ⟨E, R, L1Form b c E⟩)

/-- n rounds, then a clean leaf. -/
def cleanTree : Nat → PTree
  | 0 => .clean
  | n + 1 => .adv (cleanTree n)

theorem cleanTree_cutMem (n : Nat) (y : List Int) : (cleanTree n).cutMem y = false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [cleanTree, PTree.cutMem] using ih

/-- R ≡ 0 (mod 4) with R ≥ 8, b ≡ 2 (mod 8): a clean tape after five rounds. -/
theorem cleanTree_ok4 : (cleanTree 5).ok 448 1000 4 none false false 0 (cleanStart 8 2 4 8).1.1
    (cleanStart 8 2 4 8).1.2.1 (cleanStart 8 2 4 8).1.2.2 (cleanStart 8 2 4 8).2 = true := by decide +kernel

/-- R ≡ 0 (mod 8) with R ≥ 16, b ≡ 14 (mod 32): a clean tape after seven rounds. -/
theorem cleanTree_ok16 : (cleanTree 7).ok 448 1000 4 none false false 0 (cleanStart 32 14 8 16).1.1
    (cleanStart 32 14 8 16).1.2.1 (cleanStart 32 14 8 16).1.2.2 (cleanStart 32 14 8 16).2 = true := by
  decide +kernel

/-- **A checked clean branch reaches a clean tape.**  At every point of the class inside the cone, the machine runs
r ≥ 1 rounds of the mark model without halting, from the round start to a one-marker clean tape wider than it. -/
theorem pass_clean_of {st : SState} {f : SForms} {n : Nat}
    (hok : (cleanTree n).ok 448 1000 4 none false false 0 st.1 st.2.1 st.2.2 f = true) {y : List Int}
    (hlen : y.length = 4) (hy : inCone st.2.2 448 y) {ms : List Mark} {W R : Nat} {L : Int} (hs : agL y st.1 ms)
    (hW : agN y st.2.1 W) (hf : f.Ag y W R L) :
    ∃ r kk ms' W', steps kk (roundStart ms W) = some (roundStart ms' W') ∧ roundsZ 1000 r ms W = .newRound ms' W' ∧
      0 < r ∧ CleanTape ms' W' ∧ W < W' := by
  rcases PTree.sound 448 1000 4 none (cleanTree n) false false 0 st.1 st.2.1 st.2.2 f hok y hlen hy ms W W R L hs hW hf
      (fun h => by cases h) with hc | ⟨_, _, hm, -⟩ | ⟨r, kk, ms', W', hk, hr, hev⟩
  · rw [cleanTree_cutMem] at hc; cases hc
  · cases hm
  · rcases hev with ⟨h, -⟩ | ⟨h0, hc, hlt⟩
    · cases h
    · exact ⟨r, kk, ms', W', hk, hr, by omega, hc, hlt⟩

/-- **R ≡ 0 (mod 4), R ≥ 8 and b ≡ 2 (mod 8): a clean tape at once.**  Every phase-0 pass start with every gap at
least 448, W ≡ 0 (mod 4), right end a multiple of 4 from 8 up and middle wall 2 mod 8 (L₁ ≡ 4 mod 8) reaches, without
halting and after five rounds, a one-marker clean tape wider than the start. -/
theorem pass_clean_l4 (R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R)
    (hW4 : W % 4 = 0) (hR4 : R % 4 = 0) (hR8 : 8 ≤ R) (hb8 : b % 8 = 2) :
    ∃ r kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart ms' W') ∧
      roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms' W' ∧ 0 < r ∧ CleanTape ms' W' ∧
      W < W' := by
  obtain ⟨a₀, b₀, hms, ha, -, -, -, hR2, h1, h2, h3⟩ := hP
  simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
  obtain ⟨rfl, rfl⟩ := hms
  let y : List Int := [((a : Int) - 1) / 2, ((b : Int) - 2) / 8, (W : Int) / 4, ((R : Int) - 8) / 4]
  have hy : inCone (cleanStart 8 2 4 8).1.2.2 448 y := by
    intro f hf
    simp only [cleanStart, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;>
      simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
  have hs : agL y (cleanStart 8 2 4 8).1.1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;>
      omega
  have hW : agN y (cleanStart 8 2 4 8).1.2.1 W := by simp only [agN, y, cleanStart, YForm.eval, dot]; omega
  have hf : (cleanStart 8 2 4 8).2.Ag y W R ((cleanStart 8 2 4 8).2.L.eval y) := by
    refine ⟨?_, ?_, rfl⟩
    · simp only [agN, y, cleanStart, YForm.eval, dot]; omega
    · simp only [agN, y, cleanStart, YForm.eval, dot]; omega
  exact pass_clean_of cleanTree_ok4 rfl hy hs hW hf

/-- **R ≡ 0 (mod 8), R ≥ 16 and b ≡ 14 (mod 32): a clean tape at once**, after seven rounds (L₁ ≡ 16 mod 32). -/
theorem pass_clean_l16 (R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R)
    (hW4 : W % 4 = 0) (hR8 : R % 8 = 0) (hR16 : 16 ≤ R) (hb32 : b % 32 = 14) :
    ∃ r kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart ms' W') ∧
      roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms' W' ∧ 0 < r ∧ CleanTape ms' W' ∧
      W < W' := by
  obtain ⟨a₀, b₀, hms, ha, -, -, -, hR2, h1, h2, h3⟩ := hP
  simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
  obtain ⟨rfl, rfl⟩ := hms
  let y : List Int := [((a : Int) - 1) / 2, ((b : Int) - 14) / 32, (W : Int) / 4, ((R : Int) - 16) / 8]
  have hy : inCone (cleanStart 32 14 8 16).1.2.2 448 y := by
    intro f hf
    simp only [cleanStart, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;>
      simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
  have hs : agL y (cleanStart 32 14 8 16).1.1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;>
      omega
  have hW : agN y (cleanStart 32 14 8 16).1.2.1 W := by simp only [agN, y, cleanStart, YForm.eval, dot]; omega
  have hf : (cleanStart 32 14 8 16).2.Ag y W R ((cleanStart 32 14 8 16).2.L.eval y) := by
    refine ⟨?_, ?_, rfl⟩
    · simp only [agN, y, cleanStart, YForm.eval, dot]; omega
    · simp only [agN, y, cleanStart, YForm.eval, dot]; omega
  exact pass_clean_of cleanTree_ok16 rfl hy hs hW hf

/-- **R ≡ 0 (mod 8) and b ≡ 2 (mod 8): a clean tape at once**, after five rounds (`pass_clean_l4`). -/
theorem pass_clean8 (R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R) (hW4 : W % 4 = 0)
    (hR8 : R % 8 = 0) (hb8 : b % 8 = 2) :
    ∃ r kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart ms' W') ∧
      roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms' W' ∧ 0 < r ∧ CleanTape ms' W' ∧
      W < W' := by
  have hR2 : 2 ≤ R := by obtain ⟨_, _, -, -, -, -, -, h, -⟩ := hP; exact h
  exact pass_clean_l4 R a b W hP hW4 (by omega) (by omega) hb8

/-- **R ≡ 0 (mod 16) and b ≡ 14 (mod 32): a clean tape at once**, after seven rounds (`pass_clean_l16`). -/
theorem pass_clean16 (R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R) (hW4 : W % 4 = 0)
    (hR16 : R % 16 = 0) (hb32 : b % 32 = 14) :
    ∃ r kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart ms' W') ∧
      roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms' W' ∧ 0 < r ∧ CleanTape ms' W' ∧
      W < W' := by
  have hR2 : 2 ≤ R := by obtain ⟨_, _, -, -, -, -, -, h, -⟩ := hP; exact h
  exact pass_clean_l16 R a b W hP hW4 (by omega) (by omega) hb32

/-- **R ≡ 24 (mod 32) and b ≡ 14 (mod 32): a clean tape at once**, after seven rounds (`pass_clean_l16`). -/
theorem pass_clean24 (R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R) (hW4 : W % 4 = 0)
    (hR32 : R % 32 = 24) (hb32 : b % 32 = 14) :
    ∃ r kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart ms' W') ∧
      roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms' W' ∧ 0 < r ∧ CleanTape ms' W' ∧
      W < W' :=
  pass_clean_l16 R a b W hP hW4 (by omega) (by omega) hb32

/-- **A small left countdown at a right end that is a multiple of 4 from 8 up means a clean tape at once.**  At a
phase-0 pass start (gaps at least 448, W ≡ 0 mod 4) the left countdown L₁ is even and 3 mod 7; with |L₁| < 10 it is
−4, so the middle wall is 2 mod 8, and with R ≡ 0 (mod 4), R ≥ 8, the start reaches a wider clean tape after five
rounds (`pass_clean_l4`).  So where the last pass start before a halt has such a right end r, |L₁| ≥ 10 there, and
R³/L₁² ≤ r³/100. -/
theorem pass_clean_small4 (R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R)
    (hW4 : W % 4 = 0) (hR4 : R % 4 = 0) (hR8 : 8 ≤ R)
    (hL : -10 < passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W ∧ passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W < 10) :
    ∃ r kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart ms' W') ∧
      roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms' W' ∧ 0 < r ∧ CleanTape ms' W' ∧
      W < W' := by
  have hP' := hP
  obtain ⟨a₀, b₀, hms, -, hb, -, -, -, -, -, h3⟩ := hP'
  simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
  obtain ⟨rfl, rfl⟩ := hms
  have e : passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = 147 * (b : Int) - 112 * W + 392 * R - 186 := by
    show loopL1 b (W - R - 1) W = _
    unfold loopL1
    omega
  rw [e] at hL
  exact pass_clean_l4 R a b W hP hW4 hR4 hR8 (by omega)

/-- **A small left countdown at a right end that is a multiple of 8 means a clean tape at once**
(`pass_clean_small4`). -/
theorem pass_clean_small (R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R)
    (hW4 : W % 4 = 0) (hR8 : R % 8 = 0)
    (hL : -10 < passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W ∧ passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W < 10) :
    ∃ r kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart ms' W') ∧
      roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms' W' ∧ 0 < r ∧ CleanTape ms' W' ∧
      W < W' := by
  have hR2 : 2 ≤ R := by obtain ⟨_, _, -, -, -, -, -, h, -⟩ := hP; exact h
  exact pass_clean_small4 R a b W hP hW4 (by omega) (by omega) hL

#print axioms pass_clean_l4
#print axioms pass_clean_l16
#print axioms pass_clean8
#print axioms pass_clean16
#print axioms pass_clean24
#print axioms pass_clean_small4
#print axioms pass_clean_small

end BB6
