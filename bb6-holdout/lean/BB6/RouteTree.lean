import BB6.SymSplit

/-!
# Route trees: two-marker states run to the next clean tape

The route tree follows the run from a two-marker state G 1, M m, M E − 2 (width E; m even, E odd) to the next clean
tape (the gap at 1 and the end marker, with at most one marker between them), splitting the class of (m, E) when a
round is not decided.  Its classes are cosets of lattices in the plane, so besides the coordinate splits of
`SymSplit` a tree here can change coordinates by a shear `yᵢ = zᵢ + s·zⱼ` (j = 1 − i), which is a bijection of ℤ²:
a split of a coset on one binary digit of any linear form is a shear followed by a coordinate split.

`RTree` is such a tree with the rounds stored on its edges (`adv n`: run n rounds, which must be decided), so the
check never replays a round twice.  Its leaves are `clean` (the state reached is a clean tape, checked) and `cut`
(not followed further: no claim).  `RTree.sound` is the statement for the machine; `RTree.cutMem` follows a point
down the tree, so the statement names exactly the starts it makes no claim for.

Everything here is for two coordinates (the classes of (m, E)).
-/

namespace BB6.Sym
open BB6

/-! ## Two coordinates -/

theorem dot_two (c : List Int) (a b : Int) : dot c [a, b] = c.getD 0 0 * a + c.getD 1 0 * b := by
  match c with
  | [] => simp [dot]
  | [x] => simp [dot]
  | x :: x' :: xs => simp [dot]

theorem eval_two (f : YForm) (a b : Int) : f.eval [a, b] = f.k + f.c.getD 0 0 * a + f.c.getD 1 0 * b := by
  simp only [YForm.eval, dot_two]; omega

/-- The shear `yᵢ = zᵢ + s·zⱼ` (j = 1 − i) on a coefficient list: cⱼ gains s·cᵢ. -/
def shearC (c : List Int) (i : Nat) (s : Int) : List Int :=
  if i = 0 then [c.getD 0 0, c.getD 1 0 + s * c.getD 0 0] else [c.getD 0 0 + s * c.getD 1 0, c.getD 1 0]

def YForm.shear (f : YForm) (i : Nat) (s : Int) : YForm := ⟨f.k, shearC f.c i s⟩

/-- The point `z` sent to `y`: yᵢ = zᵢ + s·zⱼ. -/
def shearLift (z : List Int) (i : Nat) (s : Int) : List Int :=
  if i = 0 then [z.getD 0 0 + s * z.getD 1 0, z.getD 1 0] else [z.getD 0 0, z.getD 1 0 + s * z.getD 0 0]

/-- Its inverse: `y` sent back to `z`. -/
def shearDown (y : List Int) (i : Nat) (s : Int) : List Int :=
  if i = 0 then [y.getD 0 0 - s * y.getD 1 0, y.getD 1 0] else [y.getD 0 0, y.getD 1 0 - s * y.getD 0 0]

theorem eval_shear (f : YForm) (i : Nat) (s : Int) (a b : Int) :
    (f.shear i s).eval [a, b] = f.eval (shearLift [a, b] i s) := by
  have e3 : ∀ x y z : Int, x * y * z = y * (x * z) := fun x y z => by rw [Int.mul_comm x y, Int.mul_assoc]
  unfold YForm.shear shearC shearLift
  by_cases hi : i = 0
  · simp only [hi, if_true, eval_two, List.getD_cons_zero, List.getD_cons_succ]
    rw [Int.mul_add, Int.add_mul, e3]; omega
  · simp only [hi, if_false, eval_two, List.getD_cons_zero, List.getD_cons_succ]
    rw [Int.mul_add, Int.add_mul, e3]; omega

theorem shearLift_down (y : List Int) (hy : y.length = 2) (i : Nat) (s : Int) :
    shearLift (shearDown y i s) i s = y := by
  match y, hy with
  | [a, b], _ =>
    unfold shearLift shearDown
    by_cases hi : i = 0 <;> simp [hi]

theorem length_shearDown (y : List Int) (i : Nat) (s : Int) : (shearDown y i s).length = 2 := by
  unfold shearDown; split <;> rfl

def SMark.shear (m : SMark) (i : Nat) (s : Int) : SMark := ⟨m.t, m.p.shear i s⟩
def shearL (ss : List SMark) (i : Nat) (s : Int) : List SMark := ss.map (·.shear i s)
def shearT (ts : List YForm) (i : Nat) (s : Int) : List YForm := ts.map (·.shear i s)

theorem agN_shear {f : YForm} {i : Nat} {s : Int} {a b : Int} {n : Nat}
    (h : agN (shearLift [a, b] i s) f n) : agN [a, b] (f.shear i s) n := by
  unfold agN at *; rw [eval_shear]; exact h

theorem agL_shear {i : Nat} {s : Int} {a b : Int} :
    ∀ {ss : List SMark} {ms : List Mark}, agL (shearLift [a, b] i s) ss ms → agL [a, b] (shearL ss i s) ms
  | [], [], _ => trivial
  | _ :: ss, _ :: ms, h => ⟨⟨h.1.1, agN_shear h.1.2⟩, agL_shear (ss := ss) (ms := ms) h.2⟩
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

theorem inCone_shear {ts : List YForm} {Γ : Int} {i : Nat} {s : Int} {a b : Int}
    (h : inCone ts Γ (shearLift [a, b] i s)) : inCone (shearT ts i s) Γ [a, b] := by
  intro t ht
  simp only [shearT, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  rw [eval_shear]
  exact h t' ht'

/-- The child of a coordinate split that contains `y`: yᵢ = 2 zᵢ + ε. -/
theorem lift_half (y : List Int) (i : Nat) (_hi : i < y.length) :
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

theorem mod_two_cases (x : Int) : x % 2 = 0 ∨ x % 2 = 1 := by omega

/-! ## Clean tapes -/

/-- A clean tape: the gap at 1 (implicit at a round start), at most one marker, and the end marker at W − 2. -/
def cleanTape (ms : List Mark) (W : Nat) : Prop :=
  2 ≤ W ∧ ((∃ p, ms = [⟨.M, p⟩, ⟨.M, W - 2⟩]) ∨ ms = [⟨.M, W - 2⟩])

/-- The symbolic test: the last mark is a marker at W − 2, and the one before it, if any, is a marker. -/
def symClean (ss : List SMark) (sW : YForm) : Bool :=
  match ss with
  | [e] => e.t == .M && sameForm e.p (sW.addc (-2))
  | [a, e] => a.t == .M && e.t == .M && sameForm e.p (sW.addc (-2))
  | _ => false

theorem symClean_sound {y : List Int} {ss : List SMark} {ms : List Mark} {sW : YForm} {Wn : Nat}
    (hs : agL y ss ms) (hW : agN y sW Wn) (h : symClean ss sW = true) : cleanTape ms Wn := by
  match ss, ms, hs with
  | [e], [me], hs =>
    simp only [symClean, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨ht, hp⟩, -⟩ := hs
    have he := sameForm_eval h.2 y
    simp only [eval_addc] at he
    unfold agN at hp hW
    have h2 : 2 ≤ Wn := by omega
    refine ⟨h2, Or.inr ?_⟩
    obtain ⟨t, p⟩ := me
    simp only at ht hp
    rw [← ht, h.1]
    have : p = Wn - 2 := by omega
    rw [this]
  | [a, e], [ma, me], hs =>
    simp only [symClean, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hta, -⟩, ⟨hte, hpe⟩, -⟩ := hs
    have he := sameForm_eval h.2 y
    simp only [eval_addc] at he
    unfold agN at hpe hW
    have h2 : 2 ≤ Wn := by omega
    refine ⟨h2, Or.inl ⟨ma.p, ?_⟩⟩
    obtain ⟨ta, pa⟩ := ma
    obtain ⟨t, p⟩ := me
    simp only at hta hte hpe ⊢
    rw [← hta, ← hte, h.1.1, h.1.2]
    have : p = Wn - 2 := by omega
    rw [this]
  | [], _, _ => simp [symClean] at h
  | _ :: _ :: _ :: _, _, _ => simp [symClean] at h
  | [_], [], hs => exact absurd hs id
  | [_], _ :: _ :: _, hs => exact absurd hs.2 id
  | [_, _], [], hs => exact absurd hs id
  | [_, _], [_], hs => exact absurd hs.2 id
  | [_, _], _ :: _ :: _ :: _, hs => exact absurd hs.2.2 id

/-! ## Route trees -/

inductive RTree where
  /-- not followed further: no claim -/
  | cut
  /-- the state reached is a clean tape -/
  | clean
  /-- run `n` rounds (each decided on the class), then continue -/
  | adv (n : Nat) (t : RTree)
  /-- split on coordinate `i`: yᵢ = 2 zᵢ + ε -/
  | split (i : Nat) (t0 t1 : RTree)
  /-- change coordinates: yᵢ = zᵢ + s·zⱼ, j = 1 − i -/
  | shear (i : Nat) (s : Int) (t : RTree)
  deriving Repr, Inhabited

variable (Γ : Int) (fuel : Nat)

/-- The check.  `moved` records whether a round has been run on the way down, so that a `clean` leaf is a clean tape
reached after at least one round. -/
def RTree.ok : RTree → Bool → List SMark → YForm → List YForm → Bool
  | .cut, _, _, _, _ => true
  | .clean, moved, ss, sW, _ => moved && symClean ss sW
  | .adv n t, moved, ss, sW, ts =>
    match symRoundsZ ts Γ fuel n ss sW with
    | some (.newRound ss' sW') => t.ok (moved || decide (0 < n)) ss' sW' ts
    | _ => false
  | .split i t0 t1, moved, ss, sW, ts =>
    decide (i < 2) && t0.ok moved (substL ss i 0) (sW.subst i 0) (substT ts i 0) &&
      t1.ok moved (substL ss i 1) (sW.subst i 1) (substT ts i 1)
  | .shear i s t, moved, ss, sW, ts => t.ok moved (shearL ss i s) (sW.shear i s) (shearT ts i s)

/-- Follow a point down the tree: `true` when it ends in a `cut` leaf. -/
def RTree.cutMem : RTree → List Int → Bool
  | .cut, _ => true
  | .clean, _ => false
  | .adv _ t, y => t.cutMem y
  | .split i t0 t1, y =>
    if y.getD i 0 % 2 = 0 then t0.cutMem (y.set i (y.getD i 0 / 2)) else t1.cutMem (y.set i (y.getD i 0 / 2))
  | .shear i s t, y => t.cutMem (shearDown y i s)

/-- The measure of the cut leaves, as a numerator over 2^D (each split halves). -/
def RTree.cutMass : Nat → RTree → Nat
  | D, .cut => 2 ^ D
  | _, .clean => 0
  | D, .adv _ t => t.cutMass D
  | D, .split _ t0 t1 => t0.cutMass (D - 1) + t1.cutMass (D - 1)
  | D, .shear _ _ t => t.cutMass D

def RTree.depth : RTree → Nat
  | .cut => 0
  | .clean => 0
  | .adv _ t => t.depth
  | .split _ t0 t1 => max t0.depth t1.depth + 1
  | .shear _ _ t => t.depth

def RTree.leaves : RTree → Nat × Nat
  | .cut => (1, 0)
  | .clean => (0, 1)
  | .adv _ t => t.leaves
  | .split _ t0 t1 => (t0.leaves.1 + t1.leaves.1, t0.leaves.2 + t1.leaves.2)
  | .shear _ _ t => t.leaves

/-- **A checked route tree, for the machine.**  At every point `y` of the root class inside the cone, from a
well-formed round start that agrees with the root, the machine runs `n` rounds of the mark model to a round start —
it does not halt on the way — and either that round start is a clean tape reached after at least one round, or `y`
lies in a `cut` leaf. -/
theorem RTree.sound (t : RTree) : ∀ (moved : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm),
    t.ok Γ fuel moved ss sW ts = true → ∀ (y : List Int), y.length = 2 → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn : Nat), agL y ss ms → agN y sW Wn → roundWF ms Wn →
    ∃ n k ms' Wn', roundsZ fuel n ms Wn = .newRound ms' Wn' ∧ steps k (roundStart ms Wn) = some (roundStart ms' Wn') ∧
      (t.cutMem y = true ∨ ((moved = true ∨ 0 < n) ∧ cleanTape ms' Wn')) := by
  induction t with
  | cut =>
    intro moved ss sW ts _ y _ _ ms Wn _ _ _
    exact ⟨0, 0, ms, Wn, rfl, rfl, Or.inl rfl⟩
  | clean =>
    intro moved ss sW ts h y _ _ ms Wn hs hW _
    simp only [RTree.ok, Bool.and_eq_true] at h
    exact ⟨0, 0, ms, Wn, rfl, rfl, Or.inr ⟨Or.inl h.1, symClean_sound hs hW h.2⟩⟩
  | adv n t ih =>
    intro moved ss sW ts h y hlen hy ms Wn hs hW hwf
    simp only [RTree.ok] at h
    cases hr : symRoundsZ ts Γ fuel n ss sW with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      cases r with
      | newRound ss' sW' =>
        simp only at h
        have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hr
        generalize hcr : roundsZ fuel n ms Wn = cr at hag
        cases cr with
        | newRound ms₁ W₁ =>
          obtain ⟨k₁, hk₁, hwf₁⟩ := rounds_run fuel n ms Wn hwf (by rw [hcr]; intro h; cases h)
          rw [hcr] at hk₁ hwf₁
          obtain ⟨n₂, k₂, ms', Wn', hr₂, hk₂, hc⟩ := ih _ _ _ _ h y hlen hy ms₁ W₁ hag.1 hag.2 hwf₁
          refine ⟨n + n₂, k₁ + k₂, ms', Wn', ?_, steps_seq_any hk₁ hk₂, ?_⟩
          · rw [roundsZ_add fuel n n₂ ms Wn ms₁ W₁ hcr]; exact hr₂
          · simp only [RTree.cutMem]
            rcases hc with hc | ⟨hm, hcl⟩
            · exact Or.inl hc
            · refine Or.inr ⟨?_, hcl⟩
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hm
              rcases hm with (hm | hm) | hm
              · exact Or.inl hm
              · exact Or.inr (by omega)
              · exact Or.inr (by omega)
        | _ => exact absurd hag id
      | _ => simp at h
  | split i t0 t1 ih0 ih1 =>
    intro moved ss sW ts h y hlen hy ms Wn hs hW hwf
    simp only [RTree.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0⟩, h1⟩ := h
    have hiy : i < y.length := by omega
    have hy' := lift_half y i hiy
    have hzl : (y.set i (y.getD i 0 / 2)).length = 2 := by simp [hlen]
    have hiz : i < (y.set i (y.getD i 0 / 2)).length := by omega
    simp only [RTree.cutMem]
    rcases mod_two_cases (y.getD i 0) with he | he
    · rw [he] at hy'
      rw [hy'] at hy hs hW
      obtain ⟨n, k, ms', Wn', h1', h2', h3'⟩ := ih0 _ _ _ _ h0 _ hzl (inCone_subst hiz hy) ms Wn
        (agL_subst hiz hs) (agN_subst hiz hW) hwf
      exact ⟨n, k, ms', Wn', h1', h2', by rw [if_pos he]; exact h3'⟩
    · rw [he] at hy'
      rw [hy'] at hy hs hW
      obtain ⟨n, k, ms', Wn', h1', h2', h3'⟩ := ih1 _ _ _ _ h1 _ hzl (inCone_subst hiz hy) ms Wn
        (agL_subst hiz hs) (agN_subst hiz hW) hwf
      exact ⟨n, k, ms', Wn', h1', h2', by rw [if_neg (by omega)]; exact h3'⟩
  | shear i s t ih =>
    intro moved ss sW ts h y hlen hy ms Wn hs hW hwf
    simp only [RTree.ok] at h
    simp only [RTree.cutMem]
    have hz := length_shearDown y i s
    match hzz : shearDown y i s, hz with
    | [a, b], _ =>
      have hl := shearLift_down y hlen i s
      rw [hzz] at hl
      rw [← hl] at hy hs hW
      exact ih _ _ _ _ h [a, b] rfl (inCone_shear hy) ms Wn (agL_shear hs) (agN_shear hW) hwf

end BB6.Sym
