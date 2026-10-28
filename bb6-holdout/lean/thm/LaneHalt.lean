import PassOpenHalt
open BB6 BB6.Sym

/-! # Pass starts with R ≥ 769 that halt, open at every depth, on every lane found there

`blank_halt_open_big` (`thm/BigEndHalt.lean`) puts the pass start a halt from blank tape needs at a right end
R ≥ 769.  This file shows that the right end alone cannot rule it out: pass starts with R ≥ 769 that halt and that
`passTreeSym` leaves open at every depth exist on every lane that the census at R = 770 to 1,004 finds, and on one of
them at every scale tried; and (last section) on the routes that census does not find.

The lanes, with Q = W − b + 2R + 22 (untrusted: a census at every even R from 770 to 1,004, W − b up to 4,096, finds
236 closing classes, and following one point of each with W − b and R left free puts them on 91 paths).  On each the
run reaches three-wall round starts whose right ends are N/2^m for one linear form N in b, W and R, halves down
through them, and closes; at every class N is a power of 2 or 3 times one:

* Q = 2^j or 3 · 2^j,
* 3Q + 76 = 2^j,
* 2Q − R + 6 = 2^j or 3 · 2^j,
* Q + 36 = 2^j or 3 · 2^j,
* 2Q − R + 26 = 2^j,
* Q + 316 = 2^j,
* Q + 636 = 2^j or 3 · 2^j (on δ, whose first three-wall round start after the first is in round 17, with width
  ≡ 2 (mod 4) and right end (Q + 636)/1,024).

The other 25 paths begin with a half pass (round 2, from width ≡ 2 mod 4, to R/2), so their starts are never the last
pass start of a chain, and their conditions are these lanes at R/2.  `lanes769` holds one family on each lane above,
four at successive scales for 2Q − R + 26 and for Q + 316, and two for Q + 636 = 3 · 2^j; `delta998` holds δ at
R = 998 at each scale from W − b = 2¹³ − 2,654 to 2³⁰ − 2,654, as `lane486a` does at R = 486.  As there, a family is
the class of b modulo 2^k that the untrusted search finds, with the first wall free. -/

namespace BB6

/-- One family on each lane, as (W₀, R₀, b₀, k, N): Q = 2¹² (R = 1,002), Q = 3 · 2¹⁰ (R = 866), 3Q + 76 = 2¹⁴
(R = 998), 2Q − R + 6 = 2¹³ and 3 · 2¹¹ (R = 994), Q + 36 = 2¹² and 3 · 2¹¹ (R = 998), 2Q − R + 26 = 2¹³ (R = 978)
and 2¹³ to 2¹⁶ (R = 786), Q + 316 = 2¹² to 2¹⁵ (R = 934), Q + 636 = 3 · 2¹¹ and 3 · 2¹³ (R = 998). -/
def lanes769 : List Fam :=
  [⟨64808, 1002, 62738, 17, 22⟩, ⟨41904, 866, 40586, 16, 24⟩, ⟨56716, 998, 53298, 16, 23⟩,
   ⟨46132, 994, 43552, 16, 22⟩, ⟨25140, 994, 23584, 15, 24⟩, ⟨38648, 998, 36606, 16, 21⟩,
   ⟨122616, 998, 118526, 17, 24⟩, ⟨17154, 978, 14560, 15, 23⟩, ⟨16902, 786, 14020, 15, 23⟩,
   ⟨23558, 786, 16580, 17, 24⟩, ⟨233478, 786, 218308, 19, 26⟩, ⟨915462, 786, 883908, 20, 29⟩,
   ⟨23168, 934, 21278, 16, 20⟩, ⟨100992, 934, 95006, 17, 23⟩, ⟨125568, 934, 111390, 18, 25⟩,
   ⟨174720, 934, 144158, 20, 26⟩, ⟨34624, 998, 31134, 17, 24⟩, ⟨334880, 998, 312958, 19, 28⟩]

/-- δ at R = 998 (R ≡ 486 mod 512), one family at each scale Q + 636 = 2^(13+i), i = 0 to 17, so
W − b = 2^(13+i) − 2,654 (at 2¹² − 2,654 the third gap is below 448). -/
def delta998 : List Fam :=
  [⟨188224, 998, 182686, 18, 22⟩, ⟨16192, 998, 2462, 20, 24⟩, ⟨1244992, 998, 1214878, 21, 27⟩,
   ⟨1605440, 998, 1542558, 22, 29⟩, ⟨2326336, 998, 2197918, 24, 30⟩, ⟨12156736, 998, 11897246, 26, 32⟩,
   ⟨132480832, 998, 131959198, 27, 35⟩, ⟨238911296, 998, 237865374, 28, 37⟩,
   ⟨183336768, 998, 181242270, 30, 38⟩, ⟨3293413184, 998, 3289221534, 32, 40⟩,
   ⟨7366082368, 998, 7357696414, 33, 43⟩, ⟨15511420736, 998, 15494646174, 34, 45⟩,
   ⟨48981966656, 998, 48948414878, 36, 46⟩, ⟨150282796864, 998, 150215690654, 38, 48⟩,
   ⟨490323410752, 998, 490189195678, 39, 51⟩, ⟨70893010752, 998, 70624577950, 40, 53⟩,
   ⟨3630078721856, 998, 3629541853598, 42, 54⟩, ⟨4151380377408, 998, 4150306638238, 44, 56⟩]

/-- Each family's R and Q = W − b + 2R + 22, which put it on its lane, and δ's scales. -/
theorem lanes769_shape :
    lanes769.map (fun F => (F.R0, F.W0 - F.b0 + 2 * F.R0 + 22)) =
      [(1002, 4096), (866, 3072), (998, 5436), (994, 4590), (994, 3566), (998, 4060), (998, 6108), (978, 4572),
       (786, 4476), (786, 8572), (786, 16764), (786, 33148), (934, 3780), (934, 7876), (934, 16068), (934, 32452),
       (998, 5508), (998, 23940)] ∧
    delta998.map (fun F => (F.R0, F.W0 - F.b0)) = (List.range 18).map (fun i => (998, 2 ^ (i + 13) - 2654)) := by
  decide +kernel

/-- All 36 pass the checks (the close run and the model's run on each, by the kernel). -/
theorem lanes769_ok : (lanes769 ++ delta998).all Fam.ok = true := by decide +kernel

/-- **Pass starts with R ≥ 769 that halt, open at every depth, at every width: a family on each lane of the census
at R = 770 to 1,004, and on δ at each scale W − b = 2^(13+i) − 2,654 with R = 998.** -/
theorem lane769_open_halt {F : Fam} (hF : F ∈ lanes769 ++ delta998) {a t : Nat} (ha : a % 2 = 1) (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    769 ≤ F.R0 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)
      F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t)) = none := by
  have hR : (lanes769 ++ delta998).all (fun F => decide (769 ≤ F.R0)) = true := by decide +kernel
  exact ⟨of_decide_eq_true (List.all_eq_true.1 hR F hF),
    Fam.open_halt (List.all_eq_true.1 lanes769_ok F hF) ha h1 h2⟩

/-- **Every condition `blank_halt_open_big` puts on the pass start but its width**: a pass start with R ≥ 769 and
15W ≤ 64(W − b), every gap at least 448, in a cut leaf of `passTreeSym` at every depth, from which the machine halts
(walls 449, 2,462 and 15,193, width 16,192: δ at R = 998 and W − b = 2¹⁴ − 2,654).  The pass start that lemma names
is also wider than 2⁴¹, and on δ the class of b at scales from 2³⁹ to 2⁴⁹ stays far from the small b that shape needs
there (untrusted). -/
theorem lane769_far : ∃ R a b W, 769 ≤ R ∧ 15 * W ≤ 64 * (W - b) ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  have hF : (⟨16192, 998, 2462, 20, 24⟩ : Fam) ∈ lanes769 ++ delta998 := by simp [lanes769, delta998]
  obtain ⟨hR, hP, hcut, hT⟩ := lane769_open_halt hF (a := 449) (t := 0) rfl (by omega) (by decide)
  exact ⟨998, 449, 2462, 16192, hR, by omega, hP, hcut, hT⟩

/-! ## Routes the census at R = 770 to 1,004 does not find

A lane can carry several routes (paths with their own class of (R, W − b, b) and forms), and some close only at
scales above the census's W − b ≤ 4,096.  ζ, at R ≡ 998 (mod 1,024) on Q + 636, closes at Q + 636 = 2^14 to 2^22 at
R = 998, 2,022 and 3,046 but not at 2^12, the census's scale there; the census at R = 5,002 to 5,862 (W − b up to about
22,000) finds it at R = 5,094, and the census with b free at Q + 636 = 3 · 2^39 and 3 · 2^43 finds it at R = 998 and
2,022 beside δ.  The census at R = 5,002 to 5,862 also finds ε′ at R ≡ 998 (mod 2,048) on Q + 636, two routes at
R ≡ 230 (mod 512) and two at R ≡ 230 (mod 1,024) on Q + 316, and ε at R = 5,606 (untrusted, as above; their forms are
in the project's `halting-classes/routes` files).  `zeta998` holds ζ at R = 998 at each scale it closes at from 2^14 to
2^22, and `routes5000` one or two families on each of the others.  The census with b free at Q + 316 = 2^16, 3 · 2^15
and 2^17 at every R ≡ 38 (mod 64) up to 43,000 finds one more route there, at every R ≡ 1,702 (mod 2,048): its least R
is 1,702, so neither census has an R in its class.  `routesSweep` holds it at R = 1,702 at those three scales and at
R = 3,750 and 5,798 at 2^16. -/

/-- ζ at R = 998, one family at each scale Q + 636 = 2^14, 2^15, 2^16, 3 · 2^15, 2^17, ..., 2^20, 3 · 2^19, 2^21 and
2^22 (W − b = Q + 636 − 2,654). -/
def zeta998 : List Fam :=
  [⟨406560, 998, 392830, 21, 24⟩, ⟨3437600, 998, 3407486, 22, 27⟩, ⟨5305376, 998, 5242494, 23, 29⟩,
   ⟨2978848, 998, 2883198, 24, 32⟩, ⟨652320, 998, 523902, 25, 30⟩, ⟨125563936, 998, 125304446, 27, 32⟩,
   ⟨241169440, 998, 240647806, 28, 35⟩, ⟨472380448, 998, 471334526, 29, 37⟩, ⟨166720544, 998, 165150334, 30, 40⟩,
   ⟨397931552, 998, 395837054, 31, 38⟩, ⟨7765226528, 998, 7761034878, 33, 40⟩]

/-- The census at R = 5,002 to 5,862: ε′ at R = 5,094 (Q + 636 = 3 · 2^13 and 2^15), the routes at R ≡ 230 (mod 512)
on Q + 316 at R = 5,350 (2^15 and 3 · 2^13 on each), the two at R ≡ 230 (mod 1,024) (2^15), and ε at R = 5,606
(Q + 636 = 3 · 2^13 and 2^15). -/
def routes5000 : List Fam :=
  [⟨506912, 5094, 493182, 19, 28⟩, ⟨482336, 5094, 460414, 20, 26⟩, ⟨1246656, 5350, 1224926, 21, 26⟩,
   ⟨255424, 5350, 241886, 20, 28⟩, ⟨657248, 5350, 635518, 21, 26⟩, ⟨583520, 5350, 569982, 20, 28⟩,
   ⟨781664, 5350, 759934, 20, 27⟩, ⟨895936, 5350, 874206, 20, 27⟩, ⟨165696, 5606, 152990, 18, 28⟩,
   ⟨354112, 5606, 333214, 19, 26⟩]

/-- The sweep's route on Q + 316 at R ≡ 1,702 (mod 2,048): R = 1,702 at Q + 316 = 2^16, 3 · 2^15 and 2^17, and
R = 3,750 and 5,798 at 2^16. -/
def routesSweep : List Fam :=
  [⟨204672, 1702, 142878, 18, 29⟩, ⟨368512, 1702, 273950, 19, 32⟩, ⟨532352, 1702, 405022, 20, 30⟩,
   ⟨231808, 3750, 174110, 18, 29⟩, ⟨258944, 5798, 205342, 18, 29⟩]

/-- Each family's R and Q = W − b + 2R + 22, which put it on its lane. -/
theorem routes_shape :
    zeta998.map (fun F => (F.R0, F.W0 - F.b0 + 2 * F.R0 + 22 + 636)) =
      [(998, 2 ^ 14), (998, 2 ^ 15), (998, 2 ^ 16), (998, 3 * 2 ^ 15), (998, 2 ^ 17), (998, 2 ^ 18), (998, 2 ^ 19),
       (998, 2 ^ 20), (998, 3 * 2 ^ 19), (998, 2 ^ 21), (998, 2 ^ 22)] ∧
    routes5000.map (fun F => (F.R0, F.W0 - F.b0 + 2 * F.R0 + 22)) =
      [(5094, 3 * 2 ^ 13 - 636), (5094, 2 ^ 15 - 636), (5350, 2 ^ 15 - 316), (5350, 3 * 2 ^ 13 - 316),
       (5350, 2 ^ 15 - 316), (5350, 3 * 2 ^ 13 - 316), (5350, 2 ^ 15 - 316), (5350, 2 ^ 15 - 316),
       (5606, 3 * 2 ^ 13 - 636), (5606, 2 ^ 15 - 636)] ∧
    routesSweep.map (fun F => (F.R0, F.W0 - F.b0 + 2 * F.R0 + 22)) =
      [(1702, 2 ^ 16 - 316), (1702, 3 * 2 ^ 15 - 316), (1702, 2 ^ 17 - 316), (3750, 2 ^ 16 - 316),
       (5798, 2 ^ 16 - 316)] := by
  decide +kernel

/-- All 26 pass the checks (the close run and the model's run on each, by the kernel). -/
theorem routes_ok : (zeta998 ++ routes5000 ++ routesSweep).all Fam.ok = true := by decide +kernel

/-- **Pass starts with R ≥ 769 that halt, open at every depth, on the routes the census at R = 770 to 1,004 does not
find: ζ at R = 998 at eleven scales from 2^14 to 2^22, ε′, the four Q + 316 routes at R ≡ 230 and ε at R = 5,094 to
5,606, and the Q + 316 route at R ≡ 1,702 (mod 2,048).** -/
theorem route769_open_halt {F : Fam} (hF : F ∈ zeta998 ++ routes5000 ++ routesSweep) {a t : Nat} (ha : a % 2 = 1)
    (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    769 ≤ F.R0 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)
      F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t)) = none := by
  have hR : (zeta998 ++ routes5000 ++ routesSweep).all (fun F => decide (769 ≤ F.R0)) = true := by decide +kernel
  exact ⟨of_decide_eq_true (List.all_eq_true.1 hR F hF),
    Fam.open_halt (List.all_eq_true.1 routes_ok F hF) ha h1 h2⟩

/-! ## γ's lane, and the far shape with its width

γ, the class at R = 294 and Q + 5,116 = 2^16, is not alone on its lane.  The census with b free at Q + 5,116 = 2^16
at every R ≡ 38 (mod 64) up to 19,750 finds 29 classes at 16 R, and each of the first nine of those R has the same
number of classes again at 2^17 to 2^21 (untrusted).  Following one member of each with b, W and R free puts them on
16 paths, nine of them routes that recur with R (γ at R ≡ 294 mod 8,192, the others at R ≡ 3,814 mod 4,096,
R ≡ 3,302, 3,814, 6,374 and 7,910 mod 8,192 and R ≡ 294, 294 and 3,366 mod 16,384), each with b in one class mod
2^14; their forms are in the project's `halting-classes/routes` files.  `routesGamma` holds the 24 classes at 2^16
with R ≥ 769.

On two of these routes the class of b moves with R so that some members have the far shape.  At
Q + 5,116 = 3 · 2^39 the classes at three R of each route, the step from the first to the second predicting the class
at the third, and a lattice search over every R of the route put 212 members with 15b ≤ 49(W − b), W > 2⁴¹ and R ≥ 769
on the route at R ≡ 294 (mod 16,384) and 77 on the route at R ≡ 7,910 (mod 8,192) (untrusted; a census at the R of six
of them finds the predicted class each time).  `gammaWide` holds the first of each, and `lane769_far_wide` is a
member: a pass start that meets every condition `blank_halt_open_big` puts on it, its width included, and halts. -/

/-- The 24 classes at Q + 5,116 = 2^16 with R ≥ 769 (W − b = 2^16 − 5,138 − 2R), in order of R: R = 3,302, 3,366,
3,814 (two), 6,374, 7,910 (two), 8,422, 8,486 (γ), 11,494 (four), 12,006 (two), 14,566, 16,102 (two), 16,678 (three, γ
among them), 19,686 and 19,750 (two). -/
def routesGamma : List Fam :=
  [⟨7000736, 3302, 6946942, 23, 28⟩, ⟨16262912, 3366, 16209246, 24, 28⟩, ⟨2626752, 3814, 2573982, 22, 28⟩,
   ⟨3523776, 3814, 3471006, 23, 28⟩, ⟨7090368, 6374, 7042718, 23, 28⟩, ⟨914624, 7910, 870046, 20, 29⟩,
   ⟨1750208, 7910, 1705630, 22, 28⟩, ⟨15979168, 8422, 15935614, 24, 28⟩, ⟨2012928, 8486, 1969502, 23, 28⟩,
   ⟨1954464, 11494, 1917054, 21, 29⟩, ⟨1979040, 11494, 1941630, 21, 29⟩, ⟨5722784, 11494, 5685374, 23, 28⟩,
   ⟨16331424, 11494, 16294014, 24, 28⟩, ⟨873664, 12006, 837278, 22, 28⟩, ⟨4195520, 12006, 4159134, 23, 28⟩,
   ⟨1339584, 14566, 1308318, 23, 28⟩, ⟨177344, 16102, 149150, 20, 29⟩, ⟨4191424, 16102, 4163230, 22, 28⟩,
   ⟨1849088, 16678, 1822046, 21, 29⟩, ⟨4568832, 16678, 4541790, 23, 28⟩, ⟨13752064, 16678, 13725022, 24, 28⟩,
   ⟨4444832, 19686, 4423806, 23, 28⟩, ⟨337664, 19750, 316766, 20, 29⟩, ⟨2893568, 19750, 2872670, 24, 28⟩]

/-- Two members of the far shape at Q + 5,116 = 3 · 2^39: R = 55,918,886 on the route at R ≡ 294 (mod 16,384),
b ≡ 3,422 (mod 2^14), and R = 59,244,262 on the route at R ≡ 7,910 (mod 8,192), b ≡ 1,694 (mod 2^14). -/
def gammaWide : List Fam :=
  [⟨5213842519808, 55918886, 3564686921054, 58, 80⟩, ⟨6911455278272, 59244262, 5262306330270, 57, 80⟩]

/-- Each family's R and Q + 5,116, with Q = W − b + 2R + 22, which put it on the lane. -/
theorem gamma_shape :
    routesGamma.map (fun F => F.W0 - F.b0 + 2 * F.R0 + 22 + 5116) = List.replicate 24 (2 ^ 16) ∧
    gammaWide.map (fun F => (F.R0, F.W0 - F.b0 + 2 * F.R0 + 22 + 5116)) =
      [(55918886, 3 * 2 ^ 39), (59244262, 3 * 2 ^ 39)] := by
  decide +kernel

/-- All 26 pass the checks (the close run and the model's run on each, by the kernel). -/
theorem gamma_ok : (routesGamma ++ gammaWide).all Fam.ok = true := by decide +kernel

/-- **Pass starts with R ≥ 769 that halt, open at every depth, on γ's lane: nine routes and five more classes at
Q + 5,116 = 2^16, and two of the routes at 3 · 2^39.** -/
theorem gamma769_open_halt {F : Fam} (hF : F ∈ routesGamma ++ gammaWide) {a t : Nat} (ha : a % 2 = 1)
    (h1 : 448 ≤ a)
    (h2 : a + 448 ≤ F.b0 + 2 ^ F.k * t) :
    769 ≤ F.R0 ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩] (F.W0 + 2 ^ F.k * t)
      F.R0 ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, ((F.b0 + 2 ^ F.k * t : Nat) : Int) / 2,
      ((F.W0 + 2 ^ F.k * t : Nat) : Int) / 2, (F.R0 : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, F.b0 + 2 ^ F.k * t⟩, ⟨.W, F.W0 + 2 ^ F.k * t - F.R0 - 1⟩]
      (F.W0 + 2 ^ F.k * t)) = none := by
  have hR : (routesGamma ++ gammaWide).all (fun F => decide (769 ≤ F.R0)) = true := by decide +kernel
  exact ⟨of_decide_eq_true (List.all_eq_true.1 hR F hF),
    Fam.open_halt (List.all_eq_true.1 gamma_ok F hF) ha h1 h2⟩

/-- **Every condition `blank_halt_open_big` puts on the pass start, its width included**: a pass start with R ≥ 769,
width above 2⁴¹ and 15W ≤ 64(W − b), every gap at least 448, in a cut leaf of `passTreeSym` at every depth, from which
the machine halts (walls 449, 3,564,686,921,054 and 5,213,786,600,921, width 5,213,842,519,808, R = 55,918,886:
`gammaWide`'s first family, at Q + 5,116 = 3 · 2^39).  So the shape alone does not rule that pass start out. -/
theorem lane769_far_wide : ∃ R a b W, 769 ≤ R ∧ 2 ^ 41 < W ∧ 15 * W ≤ 64 * (W - b) ∧
    PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
    (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
    ∃ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none := by
  have hF : (⟨5213842519808, 55918886, 3564686921054, 58, 80⟩ : Fam) ∈ routesGamma ++ gammaWide := by
    simp [routesGamma, gammaWide]
  obtain ⟨hR, hP, hcut, hT⟩ := gamma769_open_halt hF (a := 449) (t := 0) rfl (by omega) (by decide)
  exact ⟨55918886, 449, 3564686921054, 5213842519808, hR, by decide, by decide, hP, hcut, hT⟩

#print axioms lanes769_shape
#print axioms lane769_open_halt
#print axioms lane769_far
#print axioms routes_shape
#print axioms route769_open_halt
#print axioms gamma_shape
#print axioms gamma769_open_halt
#print axioms lane769_far_wide

end BB6
