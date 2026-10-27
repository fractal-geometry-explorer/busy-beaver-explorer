import BB6.RouteTree

/-!
# Clean-tape trees: from a clean tape to the next one, wider

A clean tape is the round start G 1, M W − 2 with width W (the gap, then only the end marker).  The machine's run
from blank tape passes through clean tapes again and again (the exhaustive check in `../csearch/` follows exactly
these), and every clean tape is decided by the one number W.  A clean-tape tree is an `RTree` (`BB6/RouteTree`) over
the class of W, checked by `RTree.okW`: the same check as `RTree.ok`, except that a `clean` leaf must be a clean tape
with **one** marker (not a two-marker state), reached after at least one round, whose width is decided to be larger
than the start's (`w0`, the start's width carried down the tree).  So the run, read from clean tape to clean tape,
never comes back to a narrower one, and `RTree.soundW` gives, at every point of the root class inside the cone, a
halt-free run to a wider clean tape unless the point lies in a `cut` leaf.  The clean-tape trees also have `drop`
nodes, which run the smallest member of a class directly (below).

`roundStart_one_lt`: two clean tapes of different widths are different configurations, so a run from one clean tape to
a wider one takes at least one step (what the induction in `thm/EndToEnd.lean` needs).
-/

namespace BB6.Sym
open BB6

/-- A clean tape with one marker: the last (and only) mark is a marker at W − 2. -/
def symClean1 (ss : List SMark) (sW : YForm) : Bool :=
  match ss with
  | [e] => e.t == .M && sameForm e.p (sW.addc (-2))
  | _ => false

theorem symClean1_sound {y : List Int} {ss : List SMark} {ms : List Mark} {sW : YForm} {Wn : Nat}
    (hs : agL y ss ms) (hW : agN y sW Wn) (h : symClean1 ss sW = true) : 2 ≤ Wn ∧ ms = [⟨.M, Wn - 2⟩] := by
  match ss, ms, hs with
  | [e], [me], hs =>
    simp only [symClean1, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨ht, hp⟩, -⟩ := hs
    have he := sameForm_eval h.2 y
    simp only [eval_addc] at he
    unfold agN at hp hW
    refine ⟨by omega, ?_⟩
    obtain ⟨t, p⟩ := me
    simp only at ht hp
    rw [← ht, h.1]
    have : p = Wn - 2 := by omega
    rw [this]
  | [], _, _ => simp [symClean1] at h
  | _ :: _ :: _, _, _ => simp [symClean1] at h
  | [_], [], hs => exact absurd hs id
  | [_], _ :: _ :: _, hs => exact absurd hs.2 id

/-- The width `sW` is larger than `w0` on the whole class. -/
def widerB (sW w0 : YForm) (ts : List YForm) (Γ : Int) : Bool :=
  match sgn (sW.sub w0) ts Γ with
  | some .pos => true
  | _ => false

theorem widerB_sound {y : List Int} {ts : List YForm} {Γ : Int} (hy : inCone ts Γ y) {sW w0 : YForm} {Wn W0 : Nat}
    (hW : agN y sW Wn) (h0 : agN y w0 W0) (h : widerB sW w0 ts Γ = true) : W0 < Wn := by
  unfold widerB at h
  have hs := (sgn_sound (sW.sub w0) ts Γ y hy).1
  cases hg : sgn (sW.sub w0) ts Γ with
  | none => rw [hg] at h; cases h
  | some s =>
    rw [hg] at h
    cases s with
    | pos =>
      have := hs hg
      simp only [eval_sub] at this
      unfold agN at hW h0
      omega
    | neg => cases h
    | zero => cases h

/-! ## Direct runs -/

/-- A one-marker clean tape wider than `W0`. -/
def wider1 (ms : List Mark) (W W0 : Nat) : Bool :=
  match ms with
  | [⟨.M, p⟩] => p + 2 == W && decide (W0 < W)
  | _ => false

theorem wider1_eq {ms : List Mark} {W W0 : Nat} (h : wider1 ms W W0 = true) : ms = [⟨.M, W - 2⟩] ∧ W0 < W := by
  unfold wider1 at h
  split at h
  · rename_i p
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨by rw [show p = W - 2 by omega], h.2⟩
  · cases h

/-- Run at most `g` rounds from a round start, until a one-marker clean tape wider than `W0`. -/
def toWider (fuel W0 : Nat) : Nat → List Mark → Nat → Bool
  | 0, _, _ => false
  | g + 1, ms, W =>
    match roundZ fuel [] 1 ms W with
    | .newRound ms' W' => wider1 ms' W' W0 || toWider fuel W0 g ms' W'
    | _ => false

theorem toWider_sound (fuel W0 : Nat) : ∀ (g : Nat) (ms : List Mark) (W : Nat), toWider fuel W0 g ms W = true →
    ∃ n W', 0 < n ∧ roundsZ fuel n ms W = .newRound [⟨.M, W' - 2⟩] W' ∧ W0 < W' := by
  intro g
  induction g with
  | zero => intro ms W h; cases h
  | succ g ih =>
    intro ms W h
    simp only [toWider] at h
    split at h
    · next ms' W' hr =>
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨rfl, hlt⟩ := wider1_eq h
        exact ⟨1, W', Nat.one_pos, by simp [roundsZ, hr], hlt⟩
      · obtain ⟨n, W'', -, hr', hlt⟩ := ih ms' W' h
        refine ⟨n + 1, W'', by omega, ?_, hlt⟩
        simp only [roundsZ, hr]
        exact hr'
    · cases h

/-! ## Dropping the smallest member of a class

The cone W ≥ Γ is a condition over the rationals: a class y₀ ≡ r (mod 2^k) of the clean tapes of width at least Γ has
a smallest member, but the cone's corner, where the class's forms are compared, can lie below it, between two
members.  A comparison can then be undecided on the class although it comes out differently only below the smallest
member, or only at it.  A `drop z` node runs the member y₀ = z directly (`toWider`: the model's rounds, to a wider one-marker clean
tape) and continues with the rest of the class under the cone y₀ ≥ z + 1, whose corner is a member.  Its check
(`dropOK`) needs every form free of y₁, so that the member is one clean tape, and a cone form that excludes y₀ < z. -/

/-- The form does not depend on y₁. -/
def free1 (f : YForm) : Bool := f.c.getD 1 0 == 0

theorem eval_free1 {f : YForm} (h : free1 f = true) (a b : Int) : f.eval [a, b] = f.eval [a, 0] := by
  unfold free1 at h
  simp only [beq_iff_eq] at h
  rw [eval_two, eval_two, h]
  simp

theorem agN_free1 {f : YForm} (h : free1 f = true) {a b : Int} {n : Nat} (hn : agN [a, b] f n) : agN [a, 0] f n := by
  unfold agN at *; rw [← eval_free1 h]; exact hn

theorem agL_free1 {a b : Int} : ∀ {ss : List SMark} {ms : List Mark}, (ss.all fun s => free1 s.p) = true →
    agL [a, b] ss ms → agL [a, 0] ss ms
  | [], [], _, _ => trivial
  | _ :: ss, _ :: ms, hf, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    exact ⟨⟨h.1.1, agN_free1 hf.1 h.1.2⟩, agL_free1 (ss := ss) (ms := ms) hf.2 h.2⟩
  | [], _ :: _, _, h => absurd h id
  | _ :: _, [], _, h => absurd h id

/-- The marks at `y`. -/
def concL (y : List Int) (ss : List SMark) : List Mark := ss.map fun s => ⟨s.t, (s.p.eval y).toNat⟩

theorem agN_toNat {y : List Int} {f : YForm} {n : Nat} (h : agN y f n) : n = (f.eval y).toNat := by
  unfold agN at h; omega

theorem agL_concL {y : List Int} : ∀ {ss : List SMark} {ms : List Mark}, agL y ss ms → ms = concL y ss
  | [], [], _ => rfl
  | s :: ss, ⟨t, p⟩ :: ms, h => by
    obtain ⟨⟨ht, hp⟩, h'⟩ := h
    simp only at ht hp
    have hrest : ms = concL y ss := agL_concL h'
    simp only [concL, List.map_cons] at hrest ⊢
    rw [← hrest, ← ht, ← agN_toNat hp]
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

/-- The cone excludes every point with y₀ < z: some cone form, free of y₁ and nondecreasing in y₀, is below Γ at
y₀ = z − 1. -/
def coneFrom (ts : List YForm) (Γ z : Int) : Bool :=
  ts.any fun t => free1 t && decide (0 ≤ t.c.getD 0 0) && decide (t.eval [z - 1, 0] < Γ)

theorem coneFrom_sound {ts : List YForm} {Γ z : Int} (h : coneFrom ts Γ z = true) {a b : Int}
    (hy : inCone ts Γ [a, b]) : z ≤ a := by
  unfold coneFrom at h
  obtain ⟨t, ht, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hf, h0⟩, hlt⟩ := h
  have hc := hy t ht
  rw [eval_free1 hf, eval_two] at hc
  rw [eval_two] at hlt
  have hm : t.c.getD 0 0 * (z - 1) < t.c.getD 0 0 * a := by
    simp only [Int.mul_zero, Int.add_zero] at hc hlt; omega
  have := Int.lt_of_mul_lt_mul_left hm h0
  omega

/-- The cone of the rest of the class after the member y₀ = z is dropped: y₀ ≥ z + 1. -/
def dropCone (Γ z : Int) : YForm := ⟨Γ - (z + 1), [1, 0]⟩

theorem inCone_dropCone {Γ z a b : Int} (h : z + 1 ≤ a) : inCone [dropCone Γ z] Γ [a, b] := by
  intro t ht
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  subst ht
  simp only [dropCone, eval_two, List.getD_cons_zero, List.getD_cons_succ]
  omega

/-- The check of a `drop z` node, before its subtree: the cone excludes y₀ < z, the forms are free of y₁, and the
member y₀ = z runs to a one-marker clean tape wider than `w0` within 10,000 rounds. -/
def dropOK (Γ : Int) (fuel : Nat) (z : Int) (ss : List SMark) (sW w0 : YForm) (ts : List YForm) : Bool :=
  coneFrom ts Γ z && (ss.all fun s => free1 s.p) && free1 sW && free1 w0 &&
    toWider fuel (w0.eval [z, 0]).toNat 10000 (concL [z, 0] ss) (sW.eval [z, 0]).toNat

theorem dropOK_cone {Γ : Int} {fuel : Nat} {z : Int} {ss : List SMark} {sW w0 : YForm} {ts : List YForm}
    (h : dropOK Γ fuel z ss sW w0 ts = true) : coneFrom ts Γ z = true := by
  unfold dropOK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem dropOK_sound {Γ : Int} {fuel : Nat} {z : Int} {ss : List SMark} {sW w0 : YForm} {ts : List YForm}
    (h : dropOK Γ fuel z ss sW w0 ts = true) {b : Int} {ms : List Mark} {Wn W0 : Nat}
    (hs : agL [z, b] ss ms) (hW : agN [z, b] sW Wn) (h0 : agN [z, b] w0 W0) :
    ∃ n W', 0 < n ∧ roundsZ fuel n ms Wn = .newRound [⟨.M, W' - 2⟩] W' ∧ W0 < W' := by
  unfold dropOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, hfs⟩, hfW⟩, hf0⟩, hrun⟩ := h
  rw [← agL_concL (agL_free1 hfs hs), ← agN_toNat (agN_free1 hfW hW), ← agN_toNat (agN_free1 hf0 h0)] at hrun
  exact toWider_sound fuel W0 10000 ms Wn hrun

theorem two_cases (y : List Int) (h : y.length = 2) : ∃ a b, y = [a, b] := by
  match y, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

variable (Γ : Int) (fuel : Nat)

/-- The check for clean-tape trees: as `RTree.ok`, with `w0` the start's width (substituted along with everything
else), and a `clean` leaf a one-marker clean tape wider than the start. -/
def RTree.okW : RTree → Bool → List SMark → YForm → YForm → List YForm → Bool
  | .cut, _, _, _, _, _ => true
  | .clean, moved, ss, sW, w0, ts => moved && symClean1 ss sW && widerB sW w0 ts Γ
  | .adv n t, moved, ss, sW, w0, ts =>
    match symRoundsZ ts Γ fuel n ss sW with
    | some (.newRound ss' sW') => t.okW (moved || decide (0 < n)) ss' sW' w0 ts
    | _ => false
  | .split i t0 t1, moved, ss, sW, w0, ts =>
    decide (i < 2) && t0.okW moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0) &&
      t1.okW moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1)
  | .shear i s t, moved, ss, sW, w0, ts => t.okW moved (shearL ss i s) (sW.shear i s) (w0.shear i s) (shearT ts i s)
  | .drop z t, moved, ss, sW, w0, ts => dropOK Γ fuel z ss sW w0 ts && t.okW moved ss sW w0 [dropCone Γ z]

/-- **A checked clean-tape tree, for the machine.**  At every point `y` of the root class inside the cone, from a
well-formed round start that agrees with the root (width `Wn`; `W0` the value of `w0`), the machine runs `n` rounds of
the mark model to a round start without halting, and either that round start is a one-marker clean tape, reached
after at least one round, of width larger than `W0`, or `y` lies in a `cut` leaf. -/
theorem RTree.soundW (t : RTree) : ∀ (moved : Bool) (ss : List SMark) (sW w0 : YForm) (ts : List YForm),
    t.okW Γ fuel moved ss sW w0 ts = true → ∀ (y : List Int), y.length = 2 → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn W0 : Nat), agL y ss ms → agN y sW Wn → agN y w0 W0 → roundWF ms Wn →
    ∃ n k ms' Wn', roundsZ fuel n ms Wn = .newRound ms' Wn' ∧ steps k (roundStart ms Wn) = some (roundStart ms' Wn') ∧
      (t.cutMem y = true ∨ ((moved = true ∨ 0 < n) ∧ ms' = [⟨.M, Wn' - 2⟩] ∧ W0 < Wn')) := by
  induction t with
  | cut =>
    intro moved ss sW w0 ts _ y _ _ ms Wn W0 _ _ _ _
    exact ⟨0, 0, ms, Wn, rfl, rfl, Or.inl rfl⟩
  | clean =>
    intro moved ss sW w0 ts h y _ hy ms Wn W0 hs hW h0 _
    simp only [RTree.okW, Bool.and_eq_true] at h
    obtain ⟨⟨hm, hc⟩, hw⟩ := h
    exact ⟨0, 0, ms, Wn, rfl, rfl, Or.inr ⟨Or.inl hm, (symClean1_sound hs hW hc).2, widerB_sound hy hW h0 hw⟩⟩
  | adv n t ih =>
    intro moved ss sW w0 ts h y hlen hy ms Wn W0 hs hW h0 hwf
    simp only [RTree.okW] at h
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
          obtain ⟨n₂, k₂, ms', Wn', hr₂, hk₂, hc⟩ := ih _ _ _ _ _ h y hlen hy ms₁ W₁ W0 hag.1 hag.2 h0 hwf₁
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
    intro moved ss sW w0 ts h y hlen hy ms Wn W0 hs hW h0 hwf
    simp only [RTree.okW, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0'⟩, h1⟩ := h
    have hiy : i < y.length := by omega
    have hy' := lift_half y i hiy
    have hzl : (y.set i (y.getD i 0 / 2)).length = 2 := by simp [hlen]
    have hiz : i < (y.set i (y.getD i 0 / 2)).length := by omega
    simp only [RTree.cutMem]
    rcases mod_two_cases (y.getD i 0) with he | he
    · rw [he] at hy'
      rw [hy'] at hy hs hW h0
      obtain ⟨n, k, ms', Wn', h1', h2', h3'⟩ := ih0 _ _ _ _ _ h0' _ hzl (inCone_subst hiz hy) ms Wn W0
        (agL_subst hiz hs) (agN_subst hiz hW) (agN_subst hiz h0) hwf
      exact ⟨n, k, ms', Wn', h1', h2', by rw [if_pos he]; exact h3'⟩
    · rw [he] at hy'
      rw [hy'] at hy hs hW h0
      obtain ⟨n, k, ms', Wn', h1', h2', h3'⟩ := ih1 _ _ _ _ _ h1 _ hzl (inCone_subst hiz hy) ms Wn W0
        (agL_subst hiz hs) (agN_subst hiz hW) (agN_subst hiz h0) hwf
      exact ⟨n, k, ms', Wn', h1', h2', by rw [if_neg (by omega)]; exact h3'⟩
  | shear i s t ih =>
    intro moved ss sW w0 ts h y hlen hy ms Wn W0 hs hW h0 hwf
    simp only [RTree.okW] at h
    simp only [RTree.cutMem]
    have hz := length_shearDown y i s
    match hzz : shearDown y i s, hz with
    | [a, b], _ =>
      have hl := shearLift_down y hlen i s
      rw [hzz] at hl
      rw [← hl] at hy hs hW h0
      exact ih _ _ _ _ _ h [a, b] rfl (inCone_shear hy) ms Wn W0 (agL_shear hs) (agN_shear hW) (agN_shear h0) hwf
  | drop z t ih =>
    intro moved ss sW w0 ts h y hlen hy ms Wn W0 hs hW h0 hwf
    simp only [RTree.okW, Bool.and_eq_true] at h
    obtain ⟨hd, ht⟩ := h
    obtain ⟨a, b, rfl⟩ := two_cases y hlen
    have hza : z ≤ a := coneFrom_sound (dropOK_cone hd) hy
    simp only [RTree.cutMem, List.getD_cons_zero]
    by_cases hz : a = z
    · subst hz
      obtain ⟨n, W', hn, hr, hlt⟩ := dropOK_sound hd hs hW h0
      obtain ⟨k, hk, -⟩ := rounds_run fuel n ms Wn hwf (by rw [hr]; intro h; cases h)
      rw [hr] at hk
      exact ⟨n, k, _, W', hr, hk, Or.inr ⟨Or.inr hn, rfl, hlt⟩⟩
    · obtain ⟨n, k, ms', Wn', h1, h2, h3⟩ :=
        ih _ _ _ _ _ ht [a, b] rfl (inCone_dropCone (by omega)) ms Wn W0 hs hW h0 hwf
      exact ⟨n, k, ms', Wn', h1, h2, by rw [if_neg hz]; exact h3⟩

end BB6.Sym

namespace BB6

/-! ## Clean tapes of different widths are different configurations -/

theorem stripe_apply_lt (b : Bool) (s : Tape) : ∀ (n i : Nat), i < n →
    stripe b n s i = (if i % 2 = 0 then b else !b)
  | 0, i, h => absurd h (Nat.not_lt_zero i)
  | n + 1, 0, _ => by simp [stripe, cons]
  | n + 1, i + 1, h => by
    simp only [stripe, cons]
    rw [stripe_apply_lt (!b) s n i (by omega)]
    by_cases hi : i % 2 = 0
    · have : (i + 1) % 2 = 1 := by omega
      simp [hi, this]
    · have : (i + 1) % 2 = 0 := by omega
      simp [hi, this]

theorem stripe_apply_ge (b : Bool) (s : Tape) : ∀ (n j : Nat), stripe b n s (n + j) = s j
  | 0, j => by simp
  | n + 1, j => by
    simp only [stripe, cons]
    rw [show n + 1 + j = (n + j) + 1 by omega]
    exact stripe_apply_ge (!b) s n j

/-- The cell `W − 5` of a clean tape's right-hand stream (counted from cell 4): the second cell of its marker. -/
theorem clean_cell (W : Nat) (hW : 6 ≤ W) :
    build false 4 [⟨.M, W - 2⟩] W (W - 5) = true := by
  simp only [build, mcells, mval, mlen, Bool.not_false]
  rw [show W - 5 = (W - 2 - 4) + 1 by omega, stripe_apply_ge]
  rfl

theorem clean_cell_wider (W W' : Nat) (hW : 6 ≤ W) (hlt : W < W') (hpar : W % 2 = 0) (hpar' : W' % 2 = 0) :
    build false 4 [⟨.M, W' - 2⟩] W' (W - 5) = false := by
  simp only [build, mcells, mval, mlen, Bool.not_false]
  rw [stripe_apply_lt true _ (W' - 2 - 4) (W - 5) (by omega)]
  have : (W - 5) % 2 = 1 := by omega
  simp [this]

/-- Two one-marker clean tapes of different even widths (at least 6) are different round starts. -/
theorem roundStart_one_ne (W W' : Nat) (hW : 6 ≤ W) (hlt : W < W') (hpar : W % 2 = 0) (hpar' : W' % 2 = 0) :
    roundStart [⟨.M, W - 2⟩] W ≠ roundStart [⟨.M, W' - 2⟩] W' := by
  intro h
  have hr := congrArg (fun c => c.r (W - 5 + 1)) h
  simp only [roundStart, cons] at hr
  rw [clean_cell W hW, clean_cell_wider W W' hW hlt hpar hpar'] at hr
  cases hr

/-- A one-marker round start is well formed exactly when its width is even and at least 6. -/
theorem roundWF_one {W : Nat} : roundWF [⟨.M, W - 2⟩] W ↔ 6 ≤ W ∧ W % 2 = 0 := by
  simp only [roundWF, rightOK, mval, mlen, Bool.false_eq_true, Bool.true_eq_false, iff_false]
  omega

end BB6
