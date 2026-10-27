import BB6.Ends

/-!
# Pass-start trees: from a pass start to the next checkpoint

The endgame trees (`Tree.okEnd`) follow the run from a phase-0 pass start to where the loop's chain ends: a landing of
the chain, or a round start that is not three walls after the run left phase 0 or the halving chain.  A pass-start
tree follows the run further, to the next *checkpoint*: a landing of the loop's chain (`Landing`: the chain's next
pass start), reached with every end meeting on the way at distance at least 3, or a one-marker clean tape wider than
the start (`CleanTape`).  Past the chain's end the run goes on for a varying number of rounds (3 to 58, median 6, from
100,000 random pass starts of width about 2²⁰), and each round may need another binary digit of the start, so these
trees have leaves that are not followed further (`cut`), as the route trees do.

An end meeting at distance below 3 is where a halt could come from (`halt_needs_close`), but the round model decides
it: where the round goes on to a new round start (an end meeting at distance 2, as in the closing classes of the
loop), the tree goes on with it, and only a landing reached with every end meeting at distance at least 3 so far is a
`land` leaf (a step of the loop's chain); past a landing that is not, the tree runs on to a clean tape.

`PTree` holds one round per `adv` node.  `PTree.ok` checks a tree: every round on the way is decided on its class as a
new round start, and the flag `cf` records whether every end meeting so far is decidedly at distance at least 3; a
`land` leaf is a landing after the rounds on the way with `cf` set (`landingCheck`, with the start's width, right end
and left countdown carried along as forms); a `clean` leaf is a one-marker clean tape after at least one round,
decidedly wider than the start; a `close` leaf shows the start's left countdown in the closing class `cls`; a `cut`
leaf claims nothing.  A `cleave` node splits a class in two along a coordinate's bound on the cone (below).
`PTree.sound` is the statement for the machine, and `PTree.cutMem` follows a point down the tree, so the statement
names exactly the starts it makes no claim for.

`PTree.explore` builds the tree from a start class one step at a time (`passAct`: stop at a checkpoint, split on a
parity a landing needs, run a round, split on the first residue a round needs, or, where the cone's edge leaves a
round undecided with no residue to split on, cleave the class at the bound of the first mark's position), and
`PTree.explore_ok` proves that every tree it builds passes the check.  So the statement holds for the explored tree at
**every** depth with nothing evaluated; only the measure of its cut leaves (`passMass`) is evaluated, for the record.
-/

namespace BB6.Sym
open BB6

/-- A pass-start tree. -/
inductive PTree where
  /-- not followed further: no claim -/
  | cut
  /-- the round start reached is a landing of the loop's chain, with every end meeting on the way at distance at
  least 3 -/
  | land
  /-- the round start reached is a one-marker clean tape, wider than the start -/
  | clean
  /-- the round is not decided as a new round start, and the start's left countdown is in the closing class: no
  claim about the run -/
  | close
  /-- run one round (decided on the class as a new round start), then continue -/
  | adv (t : PTree)
  /-- split on coordinate `i`: yᵢ = 2 zᵢ + ε -/
  | split (i : Nat) (t0 t1 : PTree)
  /-- change coordinates: yᵢ = zᵢ + s·zⱼ -/
  | skew (i j : Nat) (s : Int) (t : PTree)
  /-- cleave on coordinate `i` at `c`, where every point of the class has σ(yᵢ − c) ≥ 0: the slice yᵢ = c goes on
  with yᵢ fixed and cone form `j0` dropped (`t0`, one coordinate less), the rest with cone form `j1` replaced by
  σ(yᵢ − c) ≥ 1 (`t1`) -/
  | cleave (i : Nat) (c σ : Int) (j0 j1 : Nat) (t0 t1 : PTree)
  deriving Repr, Inhabited

/-! ## Cleaving a class at the cone's edge

The cone is a condition over the rationals.  At its edge a round can be undecided on a class although only the members
with the smallest (or largest) value of some coordinate take another branch, and no residue split separates them (the
first mark next to the gap at a round start, at 6 for the smallest members and beyond for the others).  A `cleave` node
splits such a class into the slice where the coordinate takes that value, a class with one coordinate less, and the
rest, whose cone has the next value as a bound in place of one of its forms. -/

/-- The form with coordinate `i` fixed at `c`. -/
def YForm.pin (f : YForm) (i : Nat) (c : Int) : YForm := ⟨f.k + c * f.c.getD i 0, f.c.set i 0⟩
def SMark.pin (m : SMark) (i : Nat) (c : Int) : SMark := ⟨m.t, m.p.pin i c⟩
def pinL (ss : List SMark) (i : Nat) (c : Int) : List SMark := ss.map (·.pin i c)
def pinT (ts : List YForm) (i : Nat) (c : Int) : List YForm := ts.map (·.pin i c)
def SForms.pin (f : SForms) (i : Nat) (c : Int) : SForms := ⟨f.E.pin i c, f.R.pin i c, f.L.pin i c⟩

/-- The form σ(yᵢ − c). -/
def cleaveBnd (i : Nat) (c σ : Int) : YForm := ⟨-(σ * c), unitL i σ⟩

theorem dot_pin : ∀ (a y : List Int) (i : Nat), dot (a.set i 0) y = dot a y - a.getD i 0 * y.getD i 0
  | [], y, i => by simp
  | x :: xs, [], i => by cases i <;> simp [dot]
  | x :: xs, w :: ws, 0 => by simp only [List.set, dot, List.getD_cons_zero]; omega
  | x :: xs, w :: ws, i + 1 => by
    simp only [List.set, dot, List.getD_cons_succ]
    rw [dot_pin xs ws i]; omega

theorem eval_pin {y : List Int} {i : Nat} {c : Int} (hc : y.getD i 0 = c) (f : YForm) :
    (f.pin i c).eval y = f.eval y := by
  simp only [YForm.pin, YForm.eval, dot_pin, hc, Int.mul_comm c]; omega

theorem eval_cleaveBnd (i : Nat) (c σ : Int) (y : List Int) :
    (cleaveBnd i c σ).eval y = σ * (y.getD i 0 - c) := by
  simp only [cleaveBnd, YForm.eval, dot_unitL, Int.mul_sub]; omega

theorem agN_pin {y : List Int} {i : Nat} {c : Int} (hc : y.getD i 0 = c) {f : YForm} {n : Nat} (h : agN y f n) :
    agN y (f.pin i c) n := by
  unfold agN at *; rw [eval_pin hc]; exact h

theorem agL_pin {y : List Int} {i : Nat} {c : Int} (hc : y.getD i 0 = c) :
    ∀ {ss : List SMark} {ms : List Mark}, agL y ss ms → agL y (pinL ss i c) ms
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨⟨h.1.1, agN_pin hc h.1.2⟩, agL_pin hc h.2⟩
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

theorem SForms.ag_pin {y : List Int} {i : Nat} {c : Int} (hc : y.getD i 0 = c) {f : SForms} {E R : Nat} {L : Int}
    (h : f.Ag y E R L) : (f.pin i c).Ag y E R L :=
  ⟨agN_pin hc h.1, agN_pin hc h.2.1, by rw [h.2.2]; exact (eval_pin hc f.L).symm⟩

theorem inCone_pin {ts : List YForm} {Γ : Int} {y : List Int} {i : Nat} {c : Int} (hc : y.getD i 0 = c) (j : Nat)
    (h : inCone ts Γ y) : inCone ((pinT ts i c).eraseIdx j) Γ y := by
  intro t ht
  have ht' := List.mem_of_mem_eraseIdx ht
  simp only [pinT, List.mem_map] at ht'
  obtain ⟨t', ht', rfl⟩ := ht'
  rw [eval_pin hc]; exact h t' ht'

theorem inCone_set {ts : List YForm} {Γ : Int} {y : List Int} (h : inCone ts Γ y) (j : Nat) {g : YForm}
    (hg : Γ ≤ g.eval y) : inCone (ts.set j g) Γ y := by
  intro t ht
  rcases List.mem_or_eq_of_mem_set ht with ht | rfl
  · exact h t ht
  · exact hg

variable (Γ : Int) (fuel : Nat)

/-- The round start is a one-marker clean tape after at least one round, decidedly wider than the start (whose width
is `f.E`). -/
def cleanOK (ts : List YForm) (n : Nat) (ss : List SMark) (sW : YForm) (f : SForms) : Bool :=
  decide (0 < n) && cleanCheck ts Γ ss sW && ltDec f.E sW ts Γ == some true

/-- Every end meeting of the next round is decidedly at distance at least 3. -/
def meetsGe3 (ts : List YForm) (ss : List SMark) (sW : YForm) : Bool :=
  match symMeetsRounds ts Γ fuel 1 ss sW with
  | some ds => allGe3 ts Γ ds
  | none => false

/-- The check (`k` coordinates; `cls` the class of the left countdown a close leaf shows; `wf`: the round start is
known to be well formed; `cf`: every end meeting so far is decidedly at distance at least 3; `n` rounds run from the
start so far; `f` the start's forms, substituted along with it). -/
def PTree.ok (k : Nat) (cls : Option (Int × Int)) :
    PTree → Bool → Bool → Nat → List SMark → YForm → List YForm → SForms → Bool
  | .cut, _, _, _, _, _, _, _ => true
  | .close, _, _, _, _, _, _, f => clsCheck cls f.L
  | .land, _, cf, n, ss, sW, ts, f => cf && landingCheck ts Γ f n ss sW
  | .clean, _, _, n, ss, sW, ts, f => cleanOK Γ ts n ss sW f
  | .adv t, wf, cf, n, ss, sW, ts, f =>
    (wf || symRightOK ts Γ (YForm.const 4) false sW ss) &&
    (match symRoundsZ ts Γ fuel 1 ss sW with
     | some (.newRound ss' sW') => t.ok k cls true (cf && meetsGe3 Γ fuel ts ss sW) (n + 1) ss' sW' ts f
     | _ => false)
  | .split i t0 t1, wf, cf, n, ss, sW, ts, f =>
    decide (i < k) &&
      t0.ok k cls wf cf n (substL ss i 0) (sW.subst i 0) (substT ts i 0) (f.subst i 0) &&
      t1.ok k cls wf cf n (substL ss i 1) (sW.subst i 1) (substT ts i 1) (f.subst i 1)
  | .skew i j s t, wf, cf, n, ss, sW, ts, f =>
    decide (i < k) && decide (j < k) && decide (i ≠ j) &&
      t.ok k cls wf cf n (skewL ss i j s) (sW.skew i j s) (skewT ts i j s) (f.skew i j s)
  | .cleave i c σ j0 j1 t0 t1, wf, cf, n, ss, sW, ts, f =>
    decide (i < k) && σ != 0 && ltDec (cleaveBnd i c σ) (YForm.const 0) ts Γ == some false &&
      t0.ok k cls wf cf n (pinL ss i c) (sW.pin i c) ((pinT ts i c).eraseIdx j0) (f.pin i c) &&
      t1.ok k cls wf cf n ss sW (ts.set j1 ((cleaveBnd i c σ).addc (Γ - 1))) f

/-- Follow a point down the tree: `true` when it ends in a `cut` leaf. -/
def PTree.cutMem : PTree → List Int → Bool
  | .cut, _ => true
  | .land, _ => false
  | .clean, _ => false
  | .close, _ => false
  | .adv t, y => t.cutMem y
  | .split i t0 t1, y =>
    if y.getD i 0 % 2 = 0 then t0.cutMem (y.set i (y.getD i 0 / 2)) else t1.cutMem (y.set i (y.getD i 0 / 2))
  | .skew i j s t, y => t.cutMem (y.set i (y.getD i 0 - s * y.getD j 0))
  | .cleave i c _ _ _ t0 t1, y => if y.getD i 0 = c then t0.cutMem y else t1.cutMem y

/-- The measure of the cut leaves, as a numerator over 2^D (each split halves a class, a skew keeps it, and the
slice of a cleave, of one dimension less, has measure 0). -/
def PTree.cutMass : Nat → PTree → Nat
  | D, .cut => 2 ^ D
  | _, .land => 0
  | _, .clean => 0
  | _, .close => 0
  | D, .adv t => t.cutMass D
  | D, .split _ t0 t1 => t0.cutMass (D - 1) + t1.cutMass (D - 1)
  | D, .skew _ _ _ t => t.cutMass D
  | D, .cleave _ _ _ _ _ _ t1 => t1.cutMass D

/-! ## The statement for the machine -/

theorem pt_mod_two (x : Int) : x % 2 = 0 ∨ x % 2 = 1 := by omega

/-- The child of a coordinate split that contains `y`. -/
theorem pt_lift_half (y : List Int) (i : Nat) (_hi : i < y.length) :
    y = lift (y.set i (y.getD i 0 / 2)) i (y.getD i 0 % 2) := by
  simp only [lift]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_set]
    split
    · rename_i hn
      subst hn
      have hg : y.getD i 0 = y[i] := by simp [List.getD, List.getElem?_eq_getElem h1]
      have hs : (y.set i (y.getD i 0 / 2)).getD i 0 = y.getD i 0 / 2 := by
        simp [List.getD, List.getElem?_set_self (by omega : i < y.length)]
      rw [hs, ← hg]
      omega
    · rfl

/-- The point of a skew's child that is sent to `y`. -/
theorem pt_skew_down (y : List Int) (i j : Nat) (s : Int) (hij : i ≠ j) (hi : i < y.length) :
    y = skewLift (y.set i (y.getD i 0 - s * y.getD j 0)) i j s := by
  have hzj : (y.set i (y.getD i 0 - s * y.getD j 0)).getD j 0 = y.getD j 0 := by
    simp [List.getD, List.getElem?_set_ne hij]
  have hzi : (y.set i (y.getD i 0 - s * y.getD j 0)).getD i 0 = y.getD i 0 - s * y.getD j 0 := by
    simp [List.getD, List.getElem?_set_self hi]
  simp only [skewLift, hzj, hzi, List.set_set]
  rw [show y.getD i 0 - s * y.getD j 0 + s * y.getD j 0 = y.getD i 0 by omega]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_set]
    split
    · rename_i hn
      subst hn
      simp [List.getD, List.getElem?_eq_getElem h1]
    · rfl

theorem meetsGe3_sound {ts : List YForm} {y : List Int} (hy : inCone ts Γ y) {ss : List SMark} {ms : List Mark}
    {sW : YForm} {Wn : Nat} (hs : agL y ss ms) (hW : agN y sW Wn) (h : meetsGe3 Γ fuel ts ss sW = true) :
    ∀ d ∈ meetsRounds fuel 1 ms Wn, 3 ≤ d := by
  unfold meetsGe3 at h
  cases hmr : symMeetsRounds ts Γ fuel 1 ss sW with
  | none => rw [hmr] at h; cases h
  | some ds =>
    rw [hmr] at h
    exact allGe3_sound ts Γ hy (symMeetsRounds_sound ts Γ hy fuel 1 ss ms sW Wn ds hs hW hmr) h

/-- **A checked pass-start tree, for the machine.**  At every point `y` of the root class inside the cone, from a
round start that agrees with the root (well formed, or `wf` is false and the check shows it), where the start's forms
take the values E, R and L: either `y` lies in a `cut` leaf; or L is in the class `cls` (a close leaf); or the machine
runs `r` rounds of the mark model without halting to a round start that is a landing of the loop's chain after the
`n + r` rounds from the start, reached with `cf` set and every end meeting of the `r` rounds at distance at least 3,
or a one-marker clean tape wider than E reached after at least one round. -/
theorem PTree.sound (k : Nat) (cls : Option (Int × Int)) (t : PTree) :
    ∀ (wf cf : Bool) (n : Nat) (ss : List SMark) (sW : YForm) (ts : List YForm) (f : SForms),
    t.ok Γ fuel k cls wf cf n ss sW ts f = true → ∀ (y : List Int), y.length = k → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn E R : Nat) (L : Int), agL y ss ms → agN y sW Wn → f.Ag y E R L →
    (wf = true → roundWF ms Wn) →
    t.cutMem y = true ∨ (∃ m c, cls = some (m, c) ∧ L % m = c) ∨
    ∃ r kk ms' Wn', steps kk (roundStart ms Wn) = some (roundStart ms' Wn') ∧
      roundsZ fuel r ms Wn = .newRound ms' Wn' ∧
      ((cf = true ∧ (∀ d ∈ meetsRounds fuel r ms Wn, 3 ≤ d) ∧ Landing (n + r) E R L ms' Wn') ∨
        (0 < n + r ∧ CleanTape ms' Wn' ∧ E < Wn')) := by
  induction t with
  | cut =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact Or.inl rfl
  | close =>
    intro wf cf n ss sW ts f h y _ _ ms Wn E R L _ _ hf _
    right; left
    simp only [PTree.ok] at h
    unfold clsCheck at h
    cases hcls : cls with
    | none => rw [hcls] at h; cases h
    | some p =>
      obtain ⟨m, c⟩ := p
      rw [hcls] at h
      simp only [beq_iff_eq] at h
      exact ⟨m, c, rfl, by rw [hf.2.2]; exact eval_mod f.L m c h y⟩
  | land =>
    intro wf cf n ss sW ts f h y _ hy ms Wn E R L hs hW hf _
    right; right
    simp only [PTree.ok, Bool.and_eq_true] at h
    obtain ⟨hcf, h⟩ := h
    refine ⟨0, 0, ms, Wn, rfl, rfl, Or.inl ⟨hcf, fun d hd => by simp [meetsRounds] at hd, ?_⟩⟩
    simpa using landingCheck_sound ts Γ hy hf hs hW h
  | clean =>
    intro wf cf n ss sW ts f h y _ hy ms Wn E R L hs hW hf _
    right; right
    simp only [PTree.ok, cleanOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hn, hc⟩, hlt⟩ := h
    have hl := (ltDec_sound _ _ ts Γ y hy true hlt).mpr rfl
    have hE := hf.1
    unfold agN at hE hW
    refine ⟨0, 0, ms, Wn, rfl, rfl, Or.inr ⟨by omega,
      cleanCheck_sound ts Γ hy hs (by unfold agN; exact hW) hc, by omega⟩⟩
  | adv t ih =>
    intro wf cf n ss sW ts f h y hlen hy ms Wn E R L hs hW hf hwf
    simp only [PTree.ok, Bool.and_eq_true] at h
    obtain ⟨hwf', hrun⟩ := h
    have hrwf := wf_of_check Γ hy hs hW hwf hwf'
    cases hr : symRoundsZ ts Γ fuel 1 ss sW with
    | none => rw [hr] at hrun; cases hrun
    | some r =>
      rw [hr] at hrun
      cases r with
      | newRound ss' sW' =>
        have hag := symRoundsZ_sound ts Γ hy fuel 1 ss ms sW Wn _ hs hW hr
        generalize hcr : roundsZ fuel 1 ms Wn = cr at hag
        cases cr with
        | newRound ms' Wn' =>
          obtain ⟨kk, hk, hw'⟩ := rounds_run fuel 1 ms Wn hrwf (by rw [hcr]; intro h; cases h)
          rw [hcr] at hk hw'
          rcases ih true _ (n + 1) ss' sW' ts f hrun y hlen hy ms' Wn' E R L hag.1 hag.2 hf (fun _ => hw') with
            hc | hc | ⟨r₂, kk₂, ms'', Wn'', hk₂, hr₂, hev⟩
          · exact Or.inl hc
          · exact Or.inr (Or.inl hc)
          · right; right
            refine ⟨1 + r₂, kk + kk₂, ms'', Wn'', steps_seq hk hk₂, ?_, ?_⟩
            · rw [roundsZ_add fuel 1 r₂ ms Wn ms' Wn' hcr]; exact hr₂
            · rw [show n + (1 + r₂) = n + 1 + r₂ by omega]
              rcases hev with ⟨hcf, hge₂, hl⟩ | hc
              · simp only [Bool.and_eq_true] at hcf
                obtain ⟨hcf, hm⟩ := hcf
                have hge := meetsGe3_sound Γ fuel hy hs hW hm
                refine Or.inl ⟨hcf, ?_, hl⟩
                rw [meetsRounds_append fuel 1 r₂ ms Wn ms' Wn' hcr]
                intro d hd
                rcases List.mem_append.mp hd with hd | hd
                · exact hge d hd
                · exact hge₂ d hd
              · exact Or.inr hc
        | _ => exact absurd hag id
      | _ => simp at hrun
  | split i t0 t1 ih0 ih1 =>
    intro wf cf n ss sW ts f h y hlen hy ms Wn E R L hs hW hf hwf
    simp only [PTree.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0⟩, h1⟩ := h
    have hiy : i < y.length := by omega
    have hy' := pt_lift_half y i hiy
    have hzl : (y.set i (y.getD i 0 / 2)).length = k := by simp [hlen]
    have hiz : i < (y.set i (y.getD i 0 / 2)).length := by simp; omega
    simp only [PTree.cutMem]
    rcases pt_mod_two (y.getD i 0) with he | he
    · simp only [he, ↓reduceIte]
      rw [he] at hy'
      rw [hy'] at hy hs hW hf
      exact ih0 _ _ _ _ _ _ _ h0 _ hzl (inCone_subst hiz hy) ms Wn E R L (agL_subst hiz hs) (agN_subst hiz hW)
        (SForms.ag_subst hiz hf) hwf
    · simp only [he, Int.reduceEq, ↓reduceIte]
      rw [he] at hy'
      rw [hy'] at hy hs hW hf
      exact ih1 _ _ _ _ _ _ _ h1 _ hzl (inCone_subst hiz hy) ms Wn E R L (agL_subst hiz hs) (agN_subst hiz hW)
        (SForms.ag_subst hiz hf) hwf
  | skew i j s t ih =>
    intro wf cf n ss sW ts f h y hlen hy ms Wn E R L hs hW hf hwf
    simp only [PTree.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, hij⟩, ht⟩ := h
    have hy' := pt_skew_down y i j s hij (by omega)
    have hzl : (y.set i (y.getD i 0 - s * y.getD j 0)).length = k := by simp [hlen]
    have hiz : i < (y.set i (y.getD i 0 - s * y.getD j 0)).length := by simp; omega
    have hjz : j < (y.set i (y.getD i 0 - s * y.getD j 0)).length := by simp; omega
    simp only [PTree.cutMem]
    rw [hy'] at hy hs hW hf
    exact ih _ _ _ _ _ _ _ ht _ hzl (inCone_skew hiz hjz hy) ms Wn E R L (agL_skew hiz hjz hs)
      (agN_skew hiz hjz hW) (SForms.ag_skew hiz hjz hf) hwf
  | cleave i c σ j0 j1 t0 t1 ih0 ih1 =>
    intro wf cf n ss sW ts f h y hlen hy ms Wn E R L hs hW hf hwf
    simp only [PTree.ok, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨_, hσ⟩, hb⟩, h0⟩, h1⟩ := h
    have hb' : 0 ≤ σ * (y.getD i 0 - c) := by
      have := ltDec_sound _ _ ts Γ y hy false hb
      rw [eval_cleaveBnd, eval_const] at this
      simp only [Bool.false_eq_true, iff_false] at this
      omega
    simp only [PTree.cutMem]
    by_cases hc : y.getD i 0 = c
    · simp only [hc, ↓reduceIte]
      exact ih0 _ _ _ _ _ _ _ h0 y hlen (inCone_pin hc j0 hy) ms Wn E R L (agL_pin hc hs) (agN_pin hc hW)
        (SForms.ag_pin hc hf) hwf
    · simp only [hc, ↓reduceIte]
      have hne : σ * (y.getD i 0 - c) ≠ 0 := Int.mul_ne_zero hσ (by omega)
      exact ih1 _ _ _ _ _ _ _ h1 y hlen (inCone_set hy j1 (by rw [eval_addc, eval_cleaveBnd]; omega)) ms Wn E R L
        hs hW hf hwf

/-! ## The explorer -/

/-- The first residue test of a round that the class does not decide: the form and the modulus (2 or 4). -/
def passUndec (ts : List YForm) : Nat → List SMark → YForm → List SMark → YForm → Option (YForm × Int)
  | 0, _, _, _, _ => none
  | fu + 1, sL, sg, sR, sW =>
    let here : Option (YForm × Int) := match sR with
      | m :: _ =>
        if m.t == .M && ltDec m.p (sg.addc 3) ts Γ == some false then
          let d := m.p.sub (sg.addc 3)
          match d.modDec 2 with
          | none => some (d, 2)
          | some 0 => match d.half? with
            | none => some (d, 2)
            | some _ => if (d.modDec 4).isNone then some (d, 4) else none
          | _ => none
        else none
      | [] => none
    match here with
    | some r => some r
    | none =>
      match symGapEvent ts Γ sL sg sR sW with
      | some (.gap a b c d) => passUndec ts fu a b c d
      | some (.pkt sL' sx sR' sW') =>
        match symPktBack ts Γ sL' sx sR' sW' with
        | some (.gap a b c d) => passUndec ts fu a b c d
        | _ => none
      | some (.pktM sL' sx sR' sW') =>
        match symPktLand ts Γ sL' sx sR' sW' with
        | some (.gap a b c d) => passUndec ts fu a b c d
        | _ => none
      | _ => none

/-- At a three-wall round start after 2, 7 or 8 rounds reached close-free (`cf`), when the parities decided so far allow
a landing: the first parity of a landing (a odd, b even, W ≡ 0 mod 4, right end even) that the class does not
decide. -/
def landUndec (cf : Bool) (n : Nat) (ss : List SMark) (sW : YForm) : Option (YForm × Int) :=
  if cf = true ∧ (n = 2 ∨ n = 7 ∨ n = 8) then
    match swwwOf ss with
    | none => none
    | some (a, b, c) =>
      let tests : List (YForm × Int × Int) :=
        [(a, 2, 1), (b, 2, 0), (sW, 2, 0), (sW, 4, 0), ((sW.sub c).addc (-1), 2, 0)]
      if tests.any (fun t => match t.1.modDec t.2.1 with | some r => r != t.2.2 | none => false) then none
      else (tests.find? (fun t => (t.1.modDec t.2.1).isNone)).map (fun t => (t.1, t.2.1))
  else none

/-- The coordinates (of the first `k`) whose coefficient in `f` is not divisible by `m`. -/
def oddCoordsK (k : Nat) (f : YForm) (m : Int) : List Nat := (List.range k).filter (fun i => f.c.getD i 0 % m != 0)

/-- One step of the explorer. -/
inductive PAct where
  | land
  | clean
  | cut
  | close
  | adv (ss' : List SMark) (sW' : YForm)
  | split (i : Nat)
  | skew (i j : Nat) (s : Int)
  | cleave (i : Nat) (c σ : Int) (j0 j1 : Nat)

/-- How to decide the residue of `g` mod `m`: skew another coordinate whose coefficient matters onto the first one,
or, when only one is left, split it. -/
def splitAct (k : Nat) : Option (YForm × Int) → PAct
  | some (g, m) =>
    match oddCoordsK k g m with
    | [i] => if i < k then .split i else .cut
    | i :: j :: _ => if i < k ∧ j < k ∧ i ≠ j then .skew i j 1 else .cut
    | [] => .cut
  | none => .cut

/-- A step of Euclid's algorithm on the first `kE` coefficients of a form, towards the form of coordinate kE − 1 alone:
a skew that reduces a coefficient by the smallest one (the one of coordinate kE − 1 kept on ties), or one that moves a
lone coefficient to coordinate kE − 1. -/
def euclidStep (kE : Nat) (a : List Int) : Option (Nat × Nat × Int) :=
  let idx := (List.range kE).filter (fun i => a.getD i 0 != 0)
  match idx with
  | [] => none
  | [p] => if p == kE - 1 then none else some (p, kE - 1, 1)
  | i0 :: _ =>
    let better (b i : Nat) : Bool :=
      (a.getD i 0).natAbs < (a.getD b 0).natAbs ||
        ((a.getD i 0).natAbs == (a.getD b 0).natAbs && i == kE - 1)
    let p := idx.foldl (fun b i => if better b i then i else b) i0
    match idx.filter (· != p) with
    | j :: _ => some (p, j, -((a.getD j 0).tdiv (a.getD p 0)))
    | [] => none

/-- Bisection: the largest c in [lo, hi) with `p c`, for a monotone `p` true at lo and false at hi. -/
def bisectHi (p : Int → Bool) : Nat → Int → Int → Int
  | 0, lo, _ => lo
  | fu + 1, lo, hi =>
    if hi - lo ≤ 1 then lo else
    let mid := (lo + hi) / 2
    if p mid then bisectHi p fu mid hi else bisectHi p fu lo mid

/-- Bisection: the smallest c in (lo, hi] with `p c`, for a monotone `p` false at lo and true at hi. -/
def bisectLo (p : Int → Bool) : Nat → Int → Int → Int
  | 0, _, hi => hi
  | fu + 1, lo, hi =>
    if hi - lo ≤ 1 then hi else
    let mid := (lo + hi) / 2
    if p mid then bisectLo p fu lo mid else bisectLo p fu mid hi

/-- A bound of coordinate `i` at the cone's integer points, with its direction: the largest c with yᵢ ≥ c decided
(σ = 1), else the smallest c with yᵢ ≤ c decided (σ = −1). -/
def coordBound (ts : List YForm) (i : Nat) : Option (Int × Int) :=
  let ok (σ c : Int) : Bool := ltDec (cleaveBnd i c σ) (YForm.const 0) ts Γ == some false
  let B : Int := 2 ^ 62
  if ok 1 (-B) && !ok 1 B then some (bisectHi (ok 1) 130 (-B) B, 1)
  else if ok (-1) B && !ok (-1) (-B) then some (bisectLo (ok (-1)) 130 (-B) B, -1)
  else none

/-- The cone's inverse checks: every order on it can be decided by the signs of its coefficients. -/
def coneOK (ts : List YForm) : Bool := invCheck ts (coneInv ts)

/-- The next round is decided on the class (for choosing a cone form to give up). -/
def roundOK (wf : Bool) (ts : List YForm) (ss : List SMark) (sW : YForm) : Bool :=
  (wf || symRightOK ts Γ (YForm.const 4) false sW ss) && (symRoundsZ ts Γ fuel 1 ss sW).isSome

/-- The first j < n whose cone `g j` checks and is `good`, else the first whose cone checks. -/
def pickForm (n : Nat) (g : Nat → List YForm) (good : List YForm → Bool) : Option Nat :=
  let js := (List.range n).filter (fun j => coneOK (g j))
  (js.find? (fun j => good (g j))).orElse (fun _ => js.head?)

/-- At a round left undecided where no undecided residue is found: bring the first mark's position to the last
coordinate the class still has (`ts.length − 1`) by skews, then cleave the class at that coordinate's bound on the
cone, giving up for the slice the cone form whose loss still decides its next round (if any) and for the rest the one
that the bound replaces best in the same sense. -/
def cleaveAct (k : Nat) (wf : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm) : PAct :=
  match ss with
  | [] => .cut
  | m :: _ =>
    match euclidStep ts.length m.p.c with
    | some (i, j, s) => if i < k ∧ j < k ∧ i ≠ j then .skew i j s else .cut
    | none =>
      let i := ts.length - 1
      if m.p.c.getD i 0 == 0 then .cut else
      match coordBound Γ ts i with
      | none => .cut
      | some (c, σ) =>
        let j0 := pickForm ts.length (fun j => (pinT ts i c).eraseIdx j)
          (fun t0 => roundOK Γ fuel wf t0 (pinL ss i c) (sW.pin i c))
        let j1 := pickForm ts.length (fun j => ts.set j ((cleaveBnd i c σ).addc (Γ - 1)))
          (fun t1 => roundOK Γ fuel wf t1 ss sW)
        match j0, j1 with
        | some j0, some j1 =>
          if i < k ∧ σ ≠ 0 ∧ ltDec (cleaveBnd i c σ) (YForm.const 0) ts Γ = some false then .cleave i c σ j0 j1
          else .cut
        | _, _ => .cut

/-- The explorer's step at a class: a close-free landing or a clean tape ends the path; a landing parity the class
does not decide is split first (on a close-free path); otherwise the round is run if it is decided as a new round
start, a round decided otherwise (a halt, or a place the model does not cover) ends the path at a close leaf when the
start's left countdown is decidedly in `cls` (else at a cut), and an undecided round is split on its first undecided
residue, or, where none is found and `cl` allows, cleaved (`cleaveAct`). -/
def passAct (k : Nat) (cls : Option (Int × Int)) (cl wf cf : Bool) (n : Nat) (ss : List SMark) (sW : YForm)
    (ts : List YForm) (f : SForms) : PAct :=
  if (cf && landingCheck ts Γ f n ss sW) = true then .land else
  if cleanOK Γ ts n ss sW f = true then .clean else
  match landUndec cf n ss sW with
  | some gm => splitAct k (some gm)
  | none =>
    if (wf || symRightOK ts Γ (YForm.const 4) false sW ss) = true then
      match symRoundsZ ts Γ fuel 1 ss sW with
      | some (.newRound ss' sW') => .adv ss' sW'
      | some _ => if clsCheck cls f.L = true then .close else .cut
      | none =>
        match passUndec Γ ts 2000 [] (YForm.const 1) ss sW with
        | some gm => splitAct k (some gm)
        | none => if cl then cleaveAct Γ fuel k wf ss sW ts else .cut
    else .cut

/-- What the check needs of a step. -/
def PActOK (k : Nat) (cls : Option (Int × Int)) (wf cf : Bool) (n : Nat) (ss : List SMark) (sW : YForm)
    (ts : List YForm) (f : SForms) : PAct → Prop
  | .land => (cf && landingCheck ts Γ f n ss sW) = true
  | .clean => cleanOK Γ ts n ss sW f = true
  | .cut => True
  | .close => clsCheck cls f.L = true
  | .adv ss' sW' => (wf || symRightOK ts Γ (YForm.const 4) false sW ss) = true ∧
      symRoundsZ ts Γ fuel 1 ss sW = some (.newRound ss' sW')
  | .split i => i < k
  | .skew i j _ => i < k ∧ j < k ∧ i ≠ j
  | .cleave i c σ _ _ => i < k ∧ σ ≠ 0 ∧ ltDec (cleaveBnd i c σ) (YForm.const 0) ts Γ = some false

theorem splitAct_ok (k : Nat) (cls : Option (Int × Int)) (wf cf : Bool) (n : Nat) (ss : List SMark) (sW : YForm)
    (ts : List YForm) (f : SForms) (o : Option (YForm × Int)) :
    PActOK Γ fuel k cls wf cf n ss sW ts f (splitAct k o) := by
  unfold splitAct
  split
  · split
    · split
      · next h => exact h
      · trivial
    · split
      · next h => exact h
      · trivial
    · trivial
  · trivial

theorem cleaveAct_ok (k : Nat) (cls : Option (Int × Int)) (wf cf : Bool) (n : Nat) (ss : List SMark) (sW : YForm)
    (ts : List YForm) (f : SForms) :
    PActOK Γ fuel k cls wf cf n ss sW ts f (cleaveAct Γ fuel k wf ss sW ts) := by
  unfold cleaveAct
  split
  · trivial
  · split
    · split
      · next h => exact h
      · trivial
    · dsimp only
      split
      · trivial
      · split
        · trivial
        · split
          · split
            · next h => exact h
            · trivial
          · trivial

theorem passAct_ok (k : Nat) (cls : Option (Int × Int)) (cl wf cf : Bool) (n : Nat) (ss : List SMark)
    (sW : YForm) (ts : List YForm) (f : SForms) :
    PActOK Γ fuel k cls wf cf n ss sW ts f (passAct Γ fuel k cls cl wf cf n ss sW ts f) := by
  unfold passAct
  split
  · next h => exact h
  · split
    · next h => exact h
    · split
      · exact splitAct_ok Γ fuel k cls wf cf n ss sW ts f _
      · split
        · next hwf =>
          split
          · next ss' sW' hr => exact ⟨hwf, hr⟩
          · split
            · next h => exact h
            · trivial
          · split
            · exact splitAct_ok Γ fuel k cls wf cf n ss sW ts f _
            · split
              · exact cleaveAct_ok Γ fuel k cls wf cf n ss sW ts f
              · trivial
        · trivial

/-- Build a pass-start tree (`S` steps, `d` splits, `nb` cleaves left on a path). -/
def PTree.explore (k : Nat) (cls : Option (Int × Int)) :
    Nat → Nat → Nat → Bool → Bool → Nat → List SMark → YForm → List YForm → SForms → PTree
  | 0, _, _, _, _, _, _, _, _, _ => .cut
  | S + 1, d, nb, wf, cf, n, ss, sW, ts, f =>
    match passAct Γ fuel k cls (nb != 0) wf cf n ss sW ts f with
    | .land => .land
    | .clean => .clean
    | .cut => .cut
    | .close => .close
    | .adv ss' sW' =>
      .adv (PTree.explore k cls S d nb true (cf && meetsGe3 Γ fuel ts ss sW) (n + 1) ss' sW' ts f)
    | .split i =>
      match d with
      | 0 => .cut
      | d + 1 =>
        .split i (PTree.explore k cls S d nb wf cf n (substL ss i 0) (sW.subst i 0) (substT ts i 0) (f.subst i 0))
          (PTree.explore k cls S d nb wf cf n (substL ss i 1) (sW.subst i 1) (substT ts i 1) (f.subst i 1))
    | .skew i j s =>
      .skew i j s
        (PTree.explore k cls S d nb wf cf n (skewL ss i j s) (sW.skew i j s) (skewT ts i j s) (f.skew i j s))
    | .cleave i c σ j0 j1 =>
      .cleave i c σ j0 j1
        (PTree.explore k cls S d (nb - 1) wf cf n (pinL ss i c) (sW.pin i c) ((pinT ts i c).eraseIdx j0)
          (f.pin i c))
        (PTree.explore k cls S d (nb - 1) wf cf n ss sW (ts.set j1 ((cleaveBnd i c σ).addc (Γ - 1))) f)

/-- **Every explored pass-start tree passes the check.** -/
theorem PTree.explore_ok (k : Nat) (cls : Option (Int × Int)) : ∀ (S d nb : Nat) (wf cf : Bool) (n : Nat)
    (ss : List SMark) (sW : YForm) (ts : List YForm) (f : SForms),
    (PTree.explore Γ fuel k cls S d nb wf cf n ss sW ts f).ok Γ fuel k cls wf cf n ss sW ts f = true := by
  intro S
  induction S with
  | zero => intro d nb wf cf n ss sW ts f; rfl
  | succ S ih =>
    intro d nb wf cf n ss sW ts f
    have hok := passAct_ok Γ fuel k cls (nb != 0) wf cf n ss sW ts f
    simp only [PTree.explore]
    generalize passAct Γ fuel k cls (nb != 0) wf cf n ss sW ts f = act at hok
    cases act with
    | land => exact hok
    | clean => exact hok
    | cut => rfl
    | close => exact hok
    | adv ss' sW' =>
      obtain ⟨hwf, hr⟩ := hok
      simp only [PTree.ok, hwf, hr, ih, Bool.true_and]
    | split i =>
      cases d with
      | zero => rfl
      | succ d => simp only [PTree.ok, ih, Bool.and_true, decide_eq_true_eq]; exact hok
    | skew i j s =>
      obtain ⟨hi, hj, hij⟩ := hok
      simp only [PTree.ok, ih, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hi, hj⟩, hij⟩
    | cleave i c σ j0 j1 =>
      obtain ⟨hi, hσ, hb⟩ := hok
      simp only [PTree.ok, ih, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq]
      exact ⟨⟨hi, hσ⟩, hb⟩

/-! ## The measure of the cut leaves -/

/-- The cut measure (numerator over 2^D) and the leaf counts (cut, landing, clean, close; the slices' leaves
included) of `PTree.explore`, without building the tree. -/
def passMass (k : Nat) (cls : Option (Int × Int)) :
    Nat → Nat → Nat → Nat → Bool → Bool → Nat → List SMark → YForm → List YForm → SForms →
      Nat × Nat × Nat × Nat × Nat
  | 0, _, D, _, _, _, _, _, _, _, _ => (2 ^ D, 1, 0, 0, 0)
  | S + 1, d, D, nb, wf, cf, n, ss, sW, ts, f =>
    match passAct Γ fuel k cls (nb != 0) wf cf n ss sW ts f with
    | .land => (0, 0, 1, 0, 0)
    | .clean => (0, 0, 0, 1, 0)
    | .cut => (2 ^ D, 1, 0, 0, 0)
    | .close => (0, 0, 0, 0, 1)
    | .adv ss' sW' => passMass k cls S d D nb true (cf && meetsGe3 Γ fuel ts ss sW) (n + 1) ss' sW' ts f
    | .split i =>
      match d with
      | 0 => (2 ^ D, 1, 0, 0, 0)
      | d + 1 =>
        let a := passMass k cls S d (D - 1) nb wf cf n (substL ss i 0) (sW.subst i 0) (substT ts i 0) (f.subst i 0)
        let b := passMass k cls S d (D - 1) nb wf cf n (substL ss i 1) (sW.subst i 1) (substT ts i 1) (f.subst i 1)
        (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1, a.2.2.2.2 + b.2.2.2.2)
    | .skew i j s =>
      passMass k cls S d D nb wf cf n (skewL ss i j s) (sW.skew i j s) (skewT ts i j s) (f.skew i j s)
    | .cleave i c σ j0 j1 =>
      let a := passMass k cls S d D (nb - 1) wf cf n (pinL ss i c) (sW.pin i c) ((pinT ts i c).eraseIdx j0)
        (f.pin i c)
      let b := passMass k cls S d D (nb - 1) wf cf n ss sW (ts.set j1 ((cleaveBnd i c σ).addc (Γ - 1))) f
      (b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1, a.2.2.2.2 + b.2.2.2.2)

theorem passMass_cut (k : Nat) (cls : Option (Int × Int)) : ∀ (S d D nb : Nat) (wf cf : Bool) (n : Nat)
    (ss : List SMark) (sW : YForm) (ts : List YForm) (f : SForms),
    (passMass Γ fuel k cls S d D nb wf cf n ss sW ts f).1 =
      (PTree.explore Γ fuel k cls S d nb wf cf n ss sW ts f).cutMass D := by
  intro S
  induction S with
  | zero => intro d D nb wf cf n ss sW ts f; rfl
  | succ S ih =>
    intro d D nb wf cf n ss sW ts f
    simp only [passMass, PTree.explore]
    generalize passAct Γ fuel k cls (nb != 0) wf cf n ss sW ts f = act
    cases act with
    | land => rfl
    | clean => rfl
    | cut => rfl
    | close => rfl
    | adv ss' sW' => simp only [PTree.cutMass]; exact ih _ _ _ _ _ _ _ _ _ _
    | split i =>
      cases d with
      | zero => rfl
      | succ d => simp only [PTree.cutMass, ih]
    | skew i j s => simp only [PTree.cutMass]; exact ih _ _ _ _ _ _ _ _ _ _
    | cleave i c σ j0 j1 => simp only [PTree.cutMass]; exact ih _ _ _ _ _ _ _ _ _ _

end BB6.Sym
