import PassOpenHalt
import FourWallPass
open BB6 BB6.Sym

/-! # Halting routes of every length: the 4-wall loop

The route census (the project's `halting-classes/routes` files) follows each halting class from its pass start to the
re-entry P′, the first three-wall round start with the phase-0 parities, and finds it in round 2, 5, 7, 11, 13 or 17.
That list is not finite.  Between the loop's chain breaking and the re-entry the run can sit in a loop of its own on
four marks, the 4-wall pass of `thm/FourWallPass.lean` (eight rounds, an exact affine map on a residue class), and the
number of passes it makes there before it leaves has no bound: the lane Q + 5 · 2^k − 4 = 2^j (Q = W − b + 2R + 22)
with k = 4n + 7 gives n passes.

`loopFams` holds one family for each n from 0 to 9, on Q = 4 + 123 · 2^(4n+7) (k = 4n + 7, j = 4n + 14), as
`Fam` in `thm/PassOpenHalt.lean`: first wall free, b ≡ b₀ (mod 2^(20+6n)), D = W − b and R fixed.  On each, by the
kernel on the class:

* the family passes `Fam.ok`, so every member is a pass start with R ≥ 769 and every gap at least 448 that lies in a
  cut leaf of `passTreeSym` at every depth and halts;
* the round starts in rounds 5, 13, ..., 8n − 3 are in the 4-wall pass's class with every gap at least 448, so
  `four_wall_pass` gives each of the n passes;
* no round start in rounds 1 to 8n + 16 has three walls, round 8n + 17 does (width ≡ 2 mod 4), and round 8n + 19 is
  the re-entry, three walls with the phase-0 parities.

So the re-entry rounds 19, 27, ..., 91 are ten different routes, and n = 0 is δ at R = 998 (`delta998`).  The families
were found by an untrusted search (the prefix's class, the classes of the n passes and the exit's class, solved for b
and R on the lane); for n ≥ 1 their b is close to W, so they do not have 15W ≤ 64(W − b).

Every lane with a constant that the censuses have found is of this kind, Q + 5 · 2^k − 4 = 2^j or 3 · 2^j: k = 3
(Q + 36), 6 (Q + 316), 7 (Q + 636, δ), 10 (Q + 5,116, γ) and 11 (Q + 10,236).  On the end meetings, u = d + 2 starts
at (Q − 4)/4 = 2^(k−2)(2^(j−k) − 5), halves k − 3 times, takes one swap to 2^(j−k) and halves from there to the close.
On the lanes with k ≡ 2 (mod 4) the run makes its 4-wall passes of this kind or of variants with a pair of markers in
their third round (untrusted); γ's lane has members of the far shape at 3 · 2^39 (`gammaWide`). -/

namespace BB6.Sym
open BB6

/-- The four positions of a round start with a marker and three walls. -/
def mwwwOf : List SMark → Option (YForm × YForm × YForm × YForm)
  | [m0, m1, m2, m3] =>
    if m0.t = .M ∧ m1.t = .W ∧ m2.t = .W ∧ m3.t = .W then some (m0.p, m1.p, m2.p, m3.p) else none
  | _ => none

theorem mwwwOf_agree {y : List Int} {ss : List SMark} {ms : List Mark} (h : agL y ss ms) {m a b c : YForm}
    (he : mwwwOf ss = some (m, a, b, c)) :
    ∃ μ w₁ w₂ w₃, ms = [⟨.M, μ⟩, ⟨.W, w₁⟩, ⟨.W, w₂⟩, ⟨.W, w₃⟩] ∧ agN y m μ ∧ agN y a w₁ ∧ agN y b w₂ ∧
      agN y c w₃ := by
  match ss, ms, h with
  | [s0, s1, s2, s3], [m0, m1, m2, m3], h =>
    obtain ⟨⟨t0, p0⟩, ⟨t1, p1⟩, ⟨t2, p2⟩, ⟨t3, p3⟩, -⟩ := h
    simp only [mwwwOf] at he
    split at he
    · rename_i hc
      obtain ⟨c0, c1, c2, c3⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨mt0, mp0⟩ := m0
      obtain ⟨mt1, mp1⟩ := m1
      obtain ⟨mt2, mp2⟩ := m2
      obtain ⟨mt3, mp3⟩ := m3
      simp only at t0 t1 t2 t3
      exact ⟨mp0, mp1, mp2, mp3, by rw [← t0, ← t1, ← t2, ← t3, c0, c1, c2, c3], p0, p1, p2, p3⟩
    · cases he
  | [], [], _ | [_], [_], _ | [_, _], [_, _], _ | [_, _, _], [_, _, _], _ => simp [mwwwOf] at he
  | _ :: _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _ :: _, _ => simp [mwwwOf] at he
  | [], _ :: _, h | _ :: _, [], h => exact absurd h id
  | [_], _ :: _ :: _, h | _ :: _ :: _, [_], h => exact absurd h.2 id
  | [_, _], _ :: _ :: _ :: _, h | _ :: _ :: _ :: _, [_, _], h => exact absurd h.2.2 id
  | [_, _, _], _ :: _ :: _ :: _ :: _, h | _ :: _ :: _ :: _ :: _, [_, _, _], h => exact absurd h.2.2.2 id
  | [_, _, _, _], _ :: _ :: _ :: _ :: _ :: _, h | _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _], h =>
    exact absurd h.2.2.2.2 id

section
variable (ts : List YForm) (Γ : Int)

/-- A gap of a family's round start that is at least 448 at every member: free of the first wall, nondecreasing in
t, and at least 448 at t = 0. -/
def gapT (f : YForm) : Bool := f.c.getD 0 0 == 0 && decide (0 ≤ f.c.getD 1 0) && decide (448 ≤ f.k)

theorem gapT_sound {f : YForm} (h : gapT f = true) (y₀ t : Int) (ht : 0 ≤ t) : 448 ≤ f.eval [y₀, t] := by
  obtain ⟨k, c⟩ := f
  simp only [gapT, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  simp only [YForm.eval]
  match c, h0, h1 with
  | [], _, _ => simp only [dot]; omega
  | [c0], h0, _ =>
    simp only [List.getD_cons_zero] at h0
    subst h0; simp only [dot]; omega
  | c0 :: c1 :: rest, h0, h1 =>
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
    subst h0
    have := Int.mul_nonneg h1 ht
    simp only [dot, dot_nil_right]; omega

/-- The round start of a family (y = [y₀, t]) is in the 4-wall pass's class with every gap at least 448 at every
member with t ≥ 0 (`four_wall_pass`'s hypotheses). -/
def pass4CheckT (ss : List SMark) (sW : YForm) : Bool :=
  match mwwwOf ss with
  | some (m, a, b, c) =>
    m.modDec 4 == some 2 && a.modDec 4 == some 2 && (a.add b).modDec 128 == some 45 &&
    (c.sub b).modDec 32 == some 1 && (sW.sub c).modDec 32 == some 1 &&
    gapT m && gapT (a.sub m) && gapT (b.sub a) && gapT (c.sub b) && gapT (sW.sub c)
  | none => false

/-- The round start has three walls with the phase-0 parities: first wall odd, second even, width ≡ 0 (mod 4). -/
def p0Check (ss : List SMark) (sW : YForm) : Bool :=
  match swwwOf ss with
  | some (a, b, _) => a.modDec 2 == some 1 && b.modDec 2 == some 0 && sW.modDec 4 == some 0
  | none => false

/-- `k` rounds on the class from round `r`, with `P` holding at each round start on the way (rounds r to r + k). -/
def symRoundsAll (P : Nat → List SMark → YForm → Bool) : Nat → Nat → List SMark → YForm → Bool
  | r, 0, ss, sW => P r ss sW
  | r, k + 1, ss, sW => P r ss sW &&
    match symRoundZ ts Γ 1000 [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => symRoundsAll P (r + 1) k ss' sW'
    | _ => false

theorem symRoundsAll_spec {P : Nat → List SMark → YForm → Bool} :
    ∀ k r ss sW, symRoundsAll ts Γ P r k ss sW = true → ∀ i ≤ k, ∃ ss' sW',
      symRoundsZ ts Γ 1000 i ss sW = some (.newRound ss' sW') ∧ P (r + i) ss' sW' = true := by
  intro k
  induction k with
  | zero =>
    intro r ss sW h i hi
    have : i = 0 := by omega
    subst this
    exact ⟨ss, sW, rfl, by simpa [symRoundsAll] using h⟩
  | succ k ih =>
    intro r ss sW h i hi
    simp only [symRoundsAll, Bool.and_eq_true] at h
    obtain ⟨hP, hn⟩ := h
    cases i with
    | zero => exact ⟨ss, sW, rfl, by simpa using hP⟩
    | succ j =>
      cases e : symRoundZ ts Γ 1000 [] (YForm.const 1) ss sW with
      | none => rw [e] at hn; cases hn
      | some sr =>
        rw [e] at hn
        cases sr with
        | newRound ss₁ sW₁ =>
          obtain ⟨ss', sW', h1, h2⟩ := ih (r + 1) ss₁ sW₁ hn j (by omega)
          refine ⟨ss', sW', ?_, ?_⟩
          · simp only [symRoundsZ, e]; exact h1
          · rw [show r + (j + 1) = r + 1 + j by omega]; exact h2
        | _ => cases hn

theorem pass4CheckT_sound {y₀ t : Int} (ht : 0 ≤ t) {ss : List SMark} {sW : YForm} {ms : List Mark} {E : Nat}
    (hs : agL [y₀, t] ss ms) (hW : agN [y₀, t] sW E) (h : pass4CheckT ss sW = true) :
    ∃ μ w₁ w₂ w₃, ms = [⟨.M, μ⟩, ⟨.W, w₁⟩, ⟨.W, w₂⟩, ⟨.W, w₃⟩] ∧
      448 ≤ μ ∧ μ + 448 ≤ w₁ ∧ w₁ + 448 ≤ w₂ ∧ w₂ + 448 ≤ w₃ ∧ w₃ + 448 ≤ E ∧ μ % 4 = 2 ∧ w₁ % 4 = 2 ∧
      (w₁ + w₂) % 128 = 45 ∧ (w₃ - w₂) % 32 = 1 ∧ (E - w₃) % 32 = 1 := by
  unfold pass4CheckT at h
  cases hm : mwwwOf ss with
  | none => rw [hm] at h; cases h
  | some f =>
    obtain ⟨m, a, b, c⟩ := f
    rw [hm] at h
    obtain ⟨μ, w₁, w₂, w₃, rfl, hμ, h1, h2, h3⟩ := mwwwOf_agree hs hm
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨d0, d1⟩, d2⟩, d3⟩, d4⟩, l0⟩, l1⟩, l2⟩, l3⟩, l4⟩ := h
    have e0 := eval_mod _ _ _ d0 [y₀, t]
    have e1 := eval_mod _ _ _ d1 [y₀, t]
    have e2 := eval_mod _ _ _ d2 [y₀, t]
    have e3 := eval_mod _ _ _ d3 [y₀, t]
    have e4 := eval_mod _ _ _ d4 [y₀, t]
    have g0 := gapT_sound l0 y₀ t ht
    have g1 := gapT_sound l1 y₀ t ht
    have g2 := gapT_sound l2 y₀ t ht
    have g3 := gapT_sound l3 y₀ t ht
    have g4 := gapT_sound l4 y₀ t ht
    simp only [eval_add, eval_sub] at e2 e3 e4 g1 g2 g3 g4
    unfold agN at hμ h1 h2 h3 hW
    refine ⟨μ, w₁, w₂, w₃, rfl, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega

theorem p0Check_sound {y : List Int} {ss : List SMark} {sW : YForm} {ms : List Mark} {W : Nat}
    (hs : agL y ss ms) (hW : agN y sW W) (h : p0Check ss sW = true) :
    ∃ a b c, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] ∧ a % 2 = 1 ∧ b % 2 = 0 ∧ W % 4 = 0 := by
  unfold p0Check at h
  cases hsw : swwwOf ss with
  | none => rw [hsw] at h; cases h
  | some f =>
    obtain ⟨fa, fb, fc⟩ := f
    rw [hsw] at h
    obtain ⟨a, b, c, rfl, h1, h2, -⟩ := (wwwOf_agree hs).2 fa fb fc hsw
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨pa, pb⟩, pW⟩ := h
    have e1 := eval_mod _ _ _ pa y
    have e2 := eval_mod _ _ _ pb y
    have e3 := eval_mod _ _ _ pW y
    unfold agN at h1 h2 hW
    exact ⟨a, b, c, rfl, by omega, by omega, by omega⟩

theorem wwwSome_sound {y : List Int} {ss : List SMark} {ms : List Mark} (hs : agL y ss ms)
    (h : (swwwOf ss).isSome = true) : ∃ a b c, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] := by
  cases hsw : swwwOf ss with
  | none => rw [hsw] at h; cases h
  | some f =>
    obtain ⟨fa, fb, fc⟩ := f
    obtain ⟨a, b, c, rfl, -⟩ := (wwwOf_agree hs).2 fa fb fc hsw
    exact ⟨a, b, c, rfl⟩

end

end BB6.Sym

namespace BB6
open BB6.Sym

/-- What the run on a family with `n` passes shows at round start `r`: no three walls in rounds 1 to 8n + 16, three
walls in round 8n + 17, the phase-0 parities in round 8n + 19, and the 4-wall pass's class in rounds 8i + 5, i < n. -/
def loopPred (n r : Nat) (ss : List SMark) (sW : YForm) : Bool :=
  (if 0 < r ∧ r < 8 * n + 17 then (swwwOf ss).isNone else true) &&
  (if r = 8 * n + 17 then (swwwOf ss).isSome else true) &&
  (if r = 8 * n + 19 then p0Check ss sW else true) &&
  (if r % 8 = 5 ∧ r < 8 * n then pass4CheckT ss sW else true)

theorem loopPred_www {n r : Nat} {ss : List SMark} {sW : YForm}
    (h : loopPred n r ss sW = true) (h0 : 0 < r) (h1 : r < 8 * n + 17) : (swwwOf ss).isNone = true := by
  unfold loopPred at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hp, -⟩, -⟩, -⟩ := h
  rwa [ite_eq_left ⟨h0, h1⟩] at hp

theorem loopPred_17 {n r : Nat} {ss : List SMark} {sW : YForm}
    (h : loopPred n r ss sW = true) (hr : r = 8 * n + 17) : (swwwOf ss).isSome = true := by
  unfold loopPred at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, hp⟩, -⟩, -⟩ := h
  rwa [ite_eq_left hr] at hp

theorem loopPred_19 {n r : Nat} {ss : List SMark} {sW : YForm}
    (h : loopPred n r ss sW = true) (hr : r = 8 * n + 19) : p0Check ss sW = true := by
  unfold loopPred at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hp⟩, -⟩ := h
  rwa [ite_eq_left hr] at hp

theorem loopPred_pass {n r : Nat} {ss : List SMark} {sW : YForm}
    (h : loopPred n r ss sW = true) (h5 : r % 8 = 5) (hr : r < 8 * n) : pass4CheckT ss sW = true := by
  unfold loopPred at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hp⟩ := h
  rwa [ite_eq_left ⟨h5, hr⟩] at hp

/-- The checks on a family with `n` passes: `Fam.ok`, R₀ ≥ 769, and `loopPred` at every round start to round 8n + 19,
on the class. -/
def Fam.loopOK (F : Fam) (n : Nat) : Bool :=
  F.ok && decide (769 ≤ F.R0) &&
  symRoundsAll F.start.2.2 448 (loopPred n) 0 (8 * n + 19) F.start.1 F.start.2.1

/-- One family for each n from 0 to 9 on Q = 4 + 123 · 2^(4n+7), as (W₀, R₀, b₀, k, N), with k = 20 + 6n. -/
def loopFams : List Fam :=
  [⟨16192, 998, 2462, 20, 24⟩, ⟨17277120, 82662, 17190558, 26, 32⟩, ⟨9124032, 955110, 7003806, 32, 40⟩,
   ⟨51825391808, 6656742, 51774217886, 38, 48⟩, ⟨36266096832, 246780646, 35727859358, 44, 56⟩,
   ⟨182917475121344, 4222980838, 182909412302494, 50, 64⟩,
   ⟨2799843598710976, 39924896486, 2799659308015262, 56, 72⟩,
   ⟨103827616965900480, 1263990575846, 103825918699232926, 62, 80⟩,
   ⟨35362654613141502144, 6417951331046, 35362599829079056030, 68, 88⟩,
   ⟨478899190574969043136, 139458858291942, 478898387573243895454, 74, 96⟩]

/-- Each family's lane: Q = W₀ − b₀ + 2R₀ + 22 = 4 + 123 · 2^(4n+7), so Q + 5 · 2^(4n+7) − 4 = 2^(4n+14). -/
theorem loopFams_shape :
    loopFams.map (fun F => F.W0 - F.b0 + 2 * F.R0 + 22) = (List.range 10).map (fun n => 4 + 123 * 2 ^ (4 * n + 7)) ∧
    loopFams.map (fun F => F.k) = (List.range 10).map (fun n => 20 + 6 * n) := by
  decide +kernel

/-- All ten pass the checks (the close run, the model's run and the round starts to the re-entry on each, by the
kernel). -/
theorem loopFams_ok : ((List.range 10).zip loopFams).all (fun p => p.2.loopOK p.1) = true := by
  decide +kernel

/-- **Halting pass starts with n passes of the 4-wall loop, for each n from 0 to 9.**  Every member of the n-th
family is a pass start with R ≥ 769 and every gap at least 448, in a cut leaf of `passTreeSym` at every depth, from
which the machine halts; its round starts in rounds 8i + 5 (i < n) are in the 4-wall pass's class
(`four_wall_pass`); none in rounds 1 to 8n + 16 has three walls, the one in round 8n + 17 does, and the one in round
8n + 19 has three walls with the phase-0 parities, the re-entry. -/
theorem loop_open_halt {n : Nat} (hn : n < 10) {a t : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ (loopFams.getD n ⟨0, 0, 0, 0, 0⟩).b0 + 2 ^ (loopFams.getD n ⟨0, 0, 0, 0, 0⟩).k * t) :
    let F := loopFams.getD n ⟨0, 0, 0, 0, 0⟩
    let ms : List Mark := [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
    let W := F.W0 + 2 ^ F.k * t
    769 ≤ F.R0 ∧ PassStart448 ms W F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    (∃ T, steps T (roundStart ms W) = none) ∧
    (∀ i < n, ∃ μ w₁ w₂ w₃ E, roundsZ 1000 (8 * i + 5) ms W = .newRound [⟨.M, μ⟩, ⟨.W, w₁⟩, ⟨.W, w₂⟩, ⟨.W, w₃⟩] E ∧
      448 ≤ μ ∧ μ + 448 ≤ w₁ ∧ w₁ + 448 ≤ w₂ ∧ w₂ + 448 ≤ w₃ ∧ w₃ + 448 ≤ E ∧ μ % 4 = 2 ∧ w₁ % 4 = 2 ∧
      (w₁ + w₂) % 128 = 45 ∧ (w₃ - w₂) % 32 = 1 ∧ (E - w₃) % 32 = 1) ∧
    (∀ r, 0 < r → r < 8 * n + 17 → ∃ ms' W', roundsZ 1000 r ms W = .newRound ms' W' ∧ NotWWW ms') ∧
    (∃ a' b' c' W', roundsZ 1000 (8 * n + 17) ms W = .newRound [⟨.W, a'⟩, ⟨.W, b'⟩, ⟨.W, c'⟩] W') ∧
    (∃ a' b' c' W', roundsZ 1000 (8 * n + 19) ms W = .newRound [⟨.W, a'⟩, ⟨.W, b'⟩, ⟨.W, c'⟩] W' ∧
      a' % 2 = 1 ∧ b' % 2 = 0 ∧ W' % 4 = 0) := by
  intro F ms W
  have hmem : (n, F) ∈ (List.range 10).zip loopFams := by
    have hlen : loopFams.length = 10 := by decide
    rw [List.mem_iff_getElem]
    refine ⟨n, by simp [hlen]; omega, ?_⟩
    simp only [List.getElem_zip, List.getElem_range]
    simp only [F, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < loopFams.length by omega),
      Option.getD_some]
  have hok := List.all_eq_true.1 loopFams_ok _ hmem
  simp only [Fam.loopOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hF, hR⟩, hrun⟩ := hok
  obtain ⟨hP, hcut, hT⟩ := Fam.open_halt hF ha h1 h2
  have hg : F.b0 + 448 + F.R0 + 1 ≤ F.W0 := by
    simp only [Fam.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hF
    obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hg⟩, -⟩, -⟩ := hF
    exact hg
  obtain ⟨hy, hs, hWa⟩ := Fam.ag hg ha h1 h2
  have spec := symRoundsAll_spec F.start.2.2 448 _ 0 F.start.1 F.start.2.1 hrun
  -- the round start in round r, on the class and for the member
  have at_r : ∀ r ≤ 8 * n + 19, ∃ ss' sW' ms' W', roundsZ 1000 r ms W = .newRound ms' W' ∧
      agL [((a : Int) - 1) / 2, (t : Int)] ss' ms' ∧ agN [((a : Int) - 1) / 2, (t : Int)] sW' W' ∧
      loopPred n r ss' sW' = true := by
    intro r hr
    obtain ⟨ss', sW', he, hp⟩ := spec r hr
    have hag := symRoundsZ_sound F.start.2.2 448 hy 1000 r _ _ _ _ _ hs hWa he
    generalize roundsZ 1000 r ms W = cr at hag ⊢
    cases cr with
    | newRound ms' W' => exact ⟨ss', sW', ms', W', rfl, hag.1, hag.2, by simpa using hp⟩
    | _ => exact absurd hag id
  refine ⟨hR, hP, hcut, hT, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨ss', sW', ms', W', he, hl, hw, hp⟩ := at_r (8 * i + 5) (by omega)
    obtain ⟨μ, w₁, w₂, w₃, rfl, hc⟩ :=
      pass4CheckT_sound (Int.natCast_nonneg t) hl hw (loopPred_pass hp (by omega) (by omega))
    exact ⟨μ, w₁, w₂, w₃, W', he, hc⟩
  · intro r hr0 hr
    obtain ⟨ss', sW', ms', W', he, hl, hw, hp⟩ := at_r r (by omega)
    exact ⟨ms', W', he, notWWW_of_none hl (Option.isNone_iff_eq_none.1 (loopPred_www hp hr0 hr))⟩
  · obtain ⟨ss', sW', ms', W', he, hl, hw, hp⟩ := at_r (8 * n + 17) (by omega)
    obtain ⟨a', b', c', rfl⟩ := wwwSome_sound hl (loopPred_17 hp rfl)
    exact ⟨a', b', c', W', he⟩
  · obtain ⟨ss', sW', ms', W', he, hl, hw, hp⟩ := at_r (8 * n + 19) (by omega)
    obtain ⟨a', b', c', rfl, h1', h2', h3'⟩ := p0Check_sound hl hw (loopPred_19 hp rfl)
    exact ⟨a', b', c', W', he, h1', h2', h3'⟩

/-- **No finite list of routes**: for each n from 0 to 9 a pass start with R ≥ 769 and every gap at least 448, from
which the machine halts, whose first three-wall round start after round 0 is in round 8n + 17 (walls at 449,
b₀ and W₀ − R₀ − 1 of the n-th family).  The rounds differ for every n, and `four_wall_pass` is what repeats. -/
theorem loop_routes : ∀ n < 10, ∃ a b W R, 769 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none) ∧
    (∀ r, 0 < r → r < 8 * n + 17 → ∃ ms' W', roundsZ 1000 r [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W =
      .newRound ms' W' ∧ NotWWW ms') ∧
    ∃ a' b' c' W', roundsZ 1000 (8 * n + 17) [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W =
      .newRound [⟨.W, a'⟩, ⟨.W, b'⟩, ⟨.W, c'⟩] W' := by
  intro n hn
  have hb : loopFams.all (fun F => decide (897 ≤ F.b0)) = true := by decide
  have h2 : 449 + 448 ≤ (loopFams.getD n ⟨0, 0, 0, 0, 0⟩).b0 + 2 ^ (loopFams.getD n ⟨0, 0, 0, 0, 0⟩).k * 0 := by
    have hlen : loopFams.length = 10 := by decide
    have hm : loopFams.getD n ⟨0, 0, 0, 0, 0⟩ ∈ loopFams := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < loopFams.length by omega),
        Option.getD_some]
      exact List.getElem_mem _
    have := of_decide_eq_true (List.all_eq_true.1 hb _ hm)
    omega
  obtain ⟨hR, hP, -, hT, -, hw, h17, -⟩ := loop_open_halt hn (a := 449) (t := 0) rfl (by omega) h2
  simp only [Nat.mul_zero, Nat.add_zero] at hR hP hT hw h17
  exact ⟨449, _, _, _, hR, hP, hT, hw, h17⟩

#print axioms loopFams_shape
#print axioms loop_open_halt
#print axioms loop_routes

end BB6
