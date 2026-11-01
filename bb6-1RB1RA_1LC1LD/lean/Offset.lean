import Formula

/-!
# The offset `c` is at least `-1` for every list of blocks

`Formula.lean` proves that a recursive pass from `K ls (3j - 1)` ends with last block `2j + c`, `c = a + 2p - 2u`
read off where `pre` stops.  Here: for every list `ls` of blocks of at least 2 (any number of them), if `pre` stops then
`c ≥ 0`, or `c ≥ -1` when the block left of the last is 2 (there `recur_two` gives `c = -1` exactly); at most two words are taken from the supply; and the blocks
it leaves are all at least 2 (kernel only).

The proof is an abstract interpretation of the block machine.  A number is kept as a code (`gD`): exactly `0` to `3`,
or "at least 4" with its residue mod 3.  The blocks to the left keep their first three codes and, for the rest, one of
"all 0", "a block ≥ 2, then blocks ≥ 2, then 0s" or "anything" (`gL`).  The words to the right keep their first two
codes, and the rest is a nonempty run of words 1, 2, 3 in which every 1 is followed by a 2, described by its first and
its last word (`Seq`, `gW`).  `absNext` is the block machine on these descriptions, one abstract step for every way the
concrete step can go, `none` where the description would be lost; every concrete step of `pre` is matched by one of
them (`absNext_sound`).  Given a set of descriptions that contains the starts, loses none and has the bound at every
description where `pre` may stop (`checkT`), induction over `pre` gives the bound (`offset_bound_of`) and, with
`recur_sound`, the next pass start (`recur_next_of`).  The set itself, the 4,463 descriptions reachable from the
starts (`reach`), is written out as a search tree in `OffsetData.lean` by `OffsetGen.lean`, where the kernel checks it
piece by piece (`check_ok`) and the two results are stated for it (`offset_bound`, `recur_next`).
-/

namespace BB6c

open TM

/-! ## Codes for numbers -/

/-- `gD d n`: the code `d` describes `n`: `d < 4` means `n = d`, `4 + r` means `n ≥ 4` and `n ≡ r (mod 3)`. -/
def gD (d n : Nat) : Prop := (d < 4 ∧ n = d) ∨ (4 ≤ d ∧ 4 ≤ n ∧ n % 3 + 4 = d)

def mkD (n : Nat) : Nat := if n < 4 then n else n % 3 + 4

theorem gD_mk (n : Nat) : gD (mkD n) n := by
  unfold gD mkD; by_cases h : n < 4 <;> simp [h] <;> omega

def resD (d : Nat) : Nat := if d < 4 then d % 3 else d - 4

def addD (x y : Nat) : Nat := if x < 4 ∧ y < 4 then mkD (x + y) else (resD x + resD y) % 3 + 4

theorem gD_add {x y m n : Nat} (hx : gD x m) (hy : gD y n) : gD (addD x y) (m + n) := by
  unfold gD at hx hy
  unfold addD resD
  by_cases h : x < 4 ∧ y < 4
  · simp only [h, and_self, ↓reduceIte]
    have : m + n = x + y := by omega
    rw [this]; exact gD_mk _
  · simp only [h, ↓reduceIte]
    unfold gD
    by_cases hx4 : x < 4 <;> by_cases hy4 : y < 4 <;> simp [hx4, hy4] <;> omega

theorem gD_eq {d n : Nat} (h : gD d n) (v : Nat) (hv : v < 4) : (n = v ↔ d = v) := by
  unfold gD at h; omega

theorem gD_ge {d n : Nat} (h : gD d n) (v : Nat) (hv : v ≤ 4) : (v ≤ n ↔ v ≤ d) := by
  unfold gD at h; omega

theorem gD_res {d n : Nat} (h : gD d n) : n % 3 = resD d := by
  unfold gD at h; unfold resD; by_cases h4 : d < 4 <;> simp [h4] <;> omega

theorem gD_small {d n : Nat} (h : gD d n) (hd : d < 4) : n = d := by
  unfold gD at h; omega

/-- The codes of `n - c`, for `n ≥ c`, `c ≤ 3`. -/
def subD (d c : Nat) : List Nat :=
  if d < 4 then [d - c]
  else ((List.range 4).filter (fun v => 4 ≤ v + c && (v + c) % 3 + 4 = d)) ++ [(d - 4 + 3 - c % 3) % 3 + 4]

theorem gD_sub {d n c : Nat} (h : gD d n) (hc : c ≤ n) (hc3 : c ≤ 3) : ∃ e ∈ subD d c, gD e (n - c) := by
  unfold gD at h
  unfold subD
  by_cases h4 : d < 4
  · simp only [h4, ↓reduceIte, List.mem_singleton, exists_eq_left]; unfold gD; omega
  · simp only [h4, ↓reduceIte, List.mem_append, List.mem_filter, List.mem_range, List.mem_singleton]
    by_cases hs : n - c < 4
    · exact ⟨n - c, .inl ⟨by omega, by simp; omega⟩, by unfold gD; omega⟩
    · exact ⟨_, .inr rfl, by unfold gD; omega⟩

/-- Lower bound of the numbers a code describes. -/
def lowD (d : Nat) : Nat := if d < 4 then d else 4

theorem gD_low {d n : Nat} (h : gD d n) : lowD d ≤ n := by
  unfold gD at h; unfold lowD; by_cases h4 : d < 4 <;> simp [h4] <;> omega

/-! ## The blocks to the left -/

def allZ (L : List Nat) : Prop := ∀ b ∈ L, b = 0

/-- What the blocks past the explicit ones may be: `0` all zero, `1` a block ≥ 2 then blocks ≥ 2 then zeros,
otherwise anything. -/
def gR : Nat → List Nat → Prop
  | 0, L => allZ L
  | 1, L => ∃ b g z, L = b :: (g ++ z) ∧ 2 ≤ b ∧ (∀ x ∈ g, 2 ≤ x) ∧ allZ z
  | _, _ => True

/-- `gL xs r L`: the first blocks of `L` (missing ones read as 0) have the codes `xs`, the rest is described by `r`. -/
def gL : List Nat → Nat → List Nat → Prop
  | [], r, L => gR r L
  | x :: xs, r, L => gD x (L.headD 0) ∧ gL xs r L.tail

def lpopA : List Nat → Nat → List (Nat × List Nat × Nat)
  | x :: xs, r => [(x, xs, r)]
  | [], 0 => [(0, [], 0)]
  | [], 1 => [2, 3, 4, 5, 6].flatMap (fun b => [(b, [], 1), (b, [], 0)])
  | [], _ => [0, 1, 2, 3, 4, 5, 6].map (fun b => (b, [], 2))

theorem mkD_lt (n : Nat) : mkD n < 7 := by unfold mkD; split <;> omega

theorem lpop_sound {xs : List Nat} {r : Nat} {L : List Nat} (h : gL xs r L) :
    ∃ t ∈ lpopA xs r, gD t.1 (L.headD 0) ∧ gL t.2.1 t.2.2 L.tail := by
  cases xs with
  | cons x xs => exact ⟨_, List.mem_singleton_self _, h⟩
  | nil =>
    match r, h with
    | 0, h =>
      refine ⟨(0, [], 0), List.mem_singleton_self _, ?_, ?_⟩
      · cases L with
        | nil => exact .inl ⟨by omega, rfl⟩
        | cons b L => exact .inl ⟨by omega, h b (List.mem_cons_self ..)⟩
      · intro b hb; exact h b (List.mem_of_mem_tail hb)
    | 1, ⟨b, g, z, hL, hb, hg, hz⟩ =>
      subst hL
      have hm : mkD b ∈ [2, 3, 4, 5, 6] := by
        have := mkD_lt b; unfold mkD at this ⊢; simp only [List.mem_cons, List.not_mem_nil]; split <;> omega
      cases g with
      | nil =>
        refine ⟨(mkD b, [], 0), List.mem_flatMap.2 ⟨_, hm, by simp⟩, gD_mk b, ?_⟩
        exact hz
      | cons g₀ g =>
        refine ⟨(mkD b, [], 1), List.mem_flatMap.2 ⟨_, hm, by simp⟩, gD_mk b, ?_⟩
        exact ⟨g₀, g, z, rfl, hg g₀ (List.mem_cons_self ..), fun x hx => hg x (List.mem_cons_of_mem _ hx), hz⟩
    | r + 2, _ =>
      have hm : mkD (L.headD 0) ∈ [0, 1, 2, 3, 4, 5, 6] := by
        have := mkD_lt (L.headD 0); simp only [List.mem_cons, List.not_mem_nil]; omega
      exact ⟨(mkD (L.headD 0), [], 2), List.mem_map.2 ⟨_, hm, rfl⟩, gD_mk _, trivial⟩

/-- Fold the block with code `x` into the description `r` of the blocks after it. -/
def lfold (x r : Nat) : Nat := if r = 0 ∧ x = 0 then 0 else if r ≤ 1 ∧ 2 ≤ x then 1 else 2

theorem lfold_sound {x r : Nat} {L : List Nat} (hx : gD x (L.headD 0)) (hr : gR r L.tail) : gR (lfold x r) L := by
  unfold lfold
  by_cases h0 : r = 0 ∧ x = 0
  · simp only [h0, and_self, ↓reduceIte]
    obtain ⟨rfl, rfl⟩ := h0
    have hh := gD_small hx (by omega)
    intro b hb
    cases L with
    | nil => cases hb
    | cons b' L =>
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hh
      · exact hr b hb
  simp only [h0, ↓reduceIte]
  by_cases h1 : r ≤ 1 ∧ 2 ≤ x
  · simp only [h1, and_self, ↓reduceIte]
    have hb := (gD_ge hx 2 (by omega)).2 h1.2
    cases L with
    | nil => simp at hb
    | cons b L =>
      simp only [List.headD_cons] at hb
      simp only [List.tail_cons] at hr
      obtain ⟨hr1, -⟩ := h1
      match r, hr1, hr with
      | 0, _, hr => exact ⟨b, [], L, rfl, hb, by simp, hr⟩
      | 1, _, ⟨b', g, z, hL, hb', hg, hz⟩ =>
        subst hL
        exact ⟨b, b' :: g, z, rfl, hb, fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hb'
          · exact hg y hy, hz⟩
  · simp only [h1, ↓reduceIte]
    show gR (2 + 0) L
    trivial

def lfoldAll : List Nat → Nat → Nat
  | [], r => r
  | z :: zs, r => lfold z (lfoldAll zs r)

theorem lfoldAll_sound : ∀ (zs : List Nat) {r : Nat} {L : List Nat}, gL zs r L → gR (lfoldAll zs r) L
  | [], _, _, h => h
  | _ :: zs, _, _, ⟨hz, h⟩ => lfold_sound hz (lfoldAll_sound zs h)

theorem gL_split : ∀ (ys : List Nat) {zs : List Nat} {r : Nat} {L : List Nat}, gL (ys ++ zs) r L →
    gL ys (lfoldAll zs r) L
  | [], zs, _, _, h => lfoldAll_sound zs h
  | _ :: ys, _, _, _, ⟨hy, h⟩ => ⟨hy, gL_split ys h⟩

/-- At most three explicit blocks. -/
def lnorm (xs : List Nat) (r : Nat) : List Nat × Nat := (xs.take 3, lfoldAll (xs.drop 3) r)

theorem lnorm_sound {xs : List Nat} {r : Nat} {L : List Nat} (h : gL xs r L) :
    gL (lnorm xs r).1 (lnorm xs r).2 L := by
  rw [← List.take_append_drop 3 xs] at h
  exact gL_split _ h

def lcons (x : Nat) (l : List Nat × Nat) : List Nat × Nat := lnorm (x :: l.1) l.2

theorem lcons_sound {x n : Nat} {l : List Nat × Nat} {L : List Nat} (hx : gD x n) (h : gL l.1 l.2 L) :
    gL (lcons x l).1 (lcons x l).2 (n :: L) :=
  lnorm_sound (L := n :: L) ⟨hx, h⟩

/-- `k` blocks of length 0 in front (`zs`), for the code `k`. -/
def lzeros (k : Nat) (l : List Nat × Nat) : List Nat × Nat :=
  if k < 4 then (List.replicate k 0).foldr lcons l else ([0, 0, 0], 2)

theorem lzeros_sound {k m : Nat} {l : List Nat × Nat} {L : List Nat} (hk : gD k m) (h : gL l.1 l.2 L) :
    gL (lzeros k l).1 (lzeros k l).2 (zs m L) := by
  unfold lzeros zs
  by_cases h4 : k < 4
  · simp only [h4, ↓reduceIte]
    have hm := gD_small hk h4
    subst hm
    clear hk h4
    induction m with
    | zero => exact h
    | succ m ih => exact lcons_sound (.inl ⟨by omega, rfl⟩) ih
  · simp only [h4, ↓reduceIte]
    have : 4 ≤ m := by unfold gD at hk; omega
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
    refine ⟨.inl ⟨by omega, rfl⟩, .inl ⟨by omega, rfl⟩, .inl ⟨by omega, rfl⟩, trivial⟩

theorem gR_app_zeros : ∀ {r : Nat} {L : List Nat} (m : Nat), gR r L → gR r (L ++ List.replicate m 0)
  | 0, L, m, h => by
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact h b hb
    · exact List.eq_of_mem_replicate hb
  | 1, _, m, ⟨b, g, z, hL, hb, hg, hz⟩ => by
    subst hL
    refine ⟨b, g, z ++ List.replicate m 0, by simp, hb, hg, ?_⟩
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hz y hy
    · exact List.eq_of_mem_replicate hy
  | _ + 2, _, _, _ => trivial

theorem gL_app_zeros : ∀ {xs : List Nat} {r : Nat} {L : List Nat} (m : Nat), gL xs r L →
    gL xs r (L ++ List.replicate m 0)
  | [], _, _, m, h => gR_app_zeros m h
  | x :: xs, r, L, m, ⟨hx, h⟩ => by
    cases L with
    | nil =>
      cases m with
      | zero => exact ⟨hx, h⟩
      | succ m =>
        refine ⟨hx, ?_⟩
        have := gL_app_zeros (xs := xs) (r := r) (L := []) m h
        simpa using this
    | cons b L => exact ⟨hx, gL_app_zeros m h⟩

theorem pad_eq : ∀ (n : Nat) (L : List Nat), pad n L = L ++ List.replicate (n - L.length) 0
  | 0, L => by simp [pad]
  | n + 1, [] => by
    show 0 :: pad n [] = _
    rw [pad_eq n []]; simp [List.replicate_succ]
  | n + 1, b :: L => by
    show b :: pad n L = _
    rw [pad_eq n L]; simp

theorem gL_pad {xs : List Nat} {r : Nat} {L : List Nat} (n : Nat) (h : gL xs r L) : gL xs r (pad n L) := by
  rw [pad_eq]; exact gL_app_zeros _ h

/-! ## The words to the right -/

/-- A nonempty run of words 1, 2, 3, every 1 followed by a 2, first word `s`, last word `e`. -/
inductive Seq : Nat → Nat → List Nat → Prop
  | one {e : Nat} : 1 ≤ e → e ≤ 3 → Seq e e [e]
  | cons {e s t : Nat} {W : List Nat} : 1 ≤ s → s ≤ 3 → (s = 1 → t = 2) → Seq e t W → Seq e s (s :: W)

theorem Seq.range {e s : Nat} {W : List Nat} (h : Seq e s W) : 1 ≤ s ∧ s ≤ 3 := by
  cases h with
  | one h1 h2 => exact ⟨h1, h2⟩
  | cons h1 h2 _ _ => exact ⟨h1, h2⟩

theorem Seq.ne_nil {e s : Nat} {W : List Nat} (h : Seq e s W) : W ≠ [] := by
  cases h <;> simp

/-- `gW xs R W`: the first words of `W` have the codes `xs`; the rest is empty (`R = none`) or a `Seq e s`. -/
def gW : List Nat → Option (Nat × Nat) → List Nat → Prop
  | [], none, W => W = []
  | [], some (e, s), W => Seq e s W
  | _ :: _, _, [] => False
  | x :: xs, R, w :: W => gD x w ∧ gW xs R W

theorem gW_nil {xs : List Nat} {R : Option (Nat × Nat)} (h : gW xs R []) : xs = [] ∧ R = none := by
  match xs, R, h with
  | [], none, _ => exact ⟨rfl, rfl⟩
  | [], some (_, _), h => exact absurd rfl h.ne_nil

def wpopA : List Nat → Option (Nat × Nat) → List (Nat × List Nat × Option (Nat × Nat))
  | x :: xs, R => [(x, xs, R)]
  | [], none => []
  | [], some (e, s) =>
    (if s = e then [(s, [], none)] else []) ++ (if s = 1 then [2] else [1, 2, 3]).map (fun t => (s, [], some (e, t)))

theorem wpop_sound {xs : List Nat} {R : Option (Nat × Nat)} {w : Nat} {W : List Nat} (h : gW xs R (w :: W)) :
    ∃ t ∈ wpopA xs R, gD t.1 w ∧ gW t.2.1 t.2.2 W := by
  match xs, R, h with
  | x :: xs, R, h => exact ⟨_, List.mem_singleton_self _, h⟩
  | [], some (e, s), h =>
    cases h with
    | one h1 h2 =>
      exact ⟨(w, [], none), by simp [wpopA], .inl ⟨by omega, rfl⟩, rfl⟩
    | cons h1 h2 h12 hs =>
      rename_i t
      have ht := hs.range
      refine ⟨(w, [], some (e, t)), ?_, .inl ⟨by omega, rfl⟩, hs⟩
      simp only [wpopA, List.mem_append, List.mem_map]
      refine .inr ⟨t, ?_, rfl⟩
      by_cases hw : w = 1
      · subst hw; have := h12 rfl; subst this; simp
      · simp only [hw, ↓reduceIte, List.mem_cons, List.not_mem_nil]; omega

/-- Abstract word lists: `none` when the description is lost. -/
abbrev AW := Option (List Nat × Option (Nat × Nat))

def gW' : AW → List Nat → Prop
  | none, _ => True
  | some (xs, R), W => gW xs R W

/-- Fold the word with code `x` into the description of the words after it. -/
def wfold (x : Nat) : Option (Nat × Nat) → Option (Option (Nat × Nat))
  | none => if 1 ≤ x ∧ x ≤ 3 then some (some (x, x)) else none
  | some (e, s) => if 1 ≤ x ∧ x ≤ 3 ∧ (x = 1 → s = 2) then some (some (e, x)) else none

theorem wfold_sound {x w : Nat} {R R' : Option (Nat × Nat)} {W : List Nat} (hx : gD x w) (h : gW [] R W)
    (e : wfold x R = some R') : gW [] R' (w :: W) := by
  match R, h with
  | none, h =>
    simp only [wfold] at e
    split at e
    · rename_i hx3
      cases e
      have := gD_small hx (by omega); subst this
      have : W = [] := h
      subst this
      exact .one hx3.1 hx3.2
    · cases e
  | some (e', s), h =>
    simp only [wfold] at e
    split at e
    · rename_i hx3
      cases e
      have := gD_small hx (by omega); subst this
      exact .cons hx3.1 hx3.2.1 hx3.2.2 h
    · cases e

def wfoldAll : List Nat → Option (Nat × Nat) → Option (Option (Nat × Nat))
  | [], R => some R
  | z :: zs, R => (wfoldAll zs R).bind (wfold z)

theorem wfoldAll_sound : ∀ (zs : List Nat) {R R' : Option (Nat × Nat)} {W : List Nat}, gW zs R W →
    wfoldAll zs R = some R' → gW [] R' W
  | [], _, _, _, h, e => by cases e; exact h
  | z :: zs, R, R', W, h, e => by
    cases W with
    | nil => exact absurd h (by simp [gW])
    | cons w W =>
      obtain ⟨hz, h⟩ := h
      simp only [wfoldAll, Option.bind_eq_some_iff] at e
      obtain ⟨R'', e₁, e₂⟩ := e
      exact wfold_sound hz (wfoldAll_sound zs h e₁) e₂

theorem gW_split : ∀ (ys : List Nat) {zs : List Nat} {R R' : Option (Nat × Nat)} {W : List Nat},
    gW (ys ++ zs) R W → wfoldAll zs R = some R' → gW ys R' W
  | [], zs, _, _, _, h, e => wfoldAll_sound zs h e
  | y :: ys, zs, R, R', W, h, e => by
    cases W with
    | nil => exact absurd h (by simp [gW])
    | cons w W => exact ⟨h.1, gW_split ys h.2 e⟩

/-- At most two explicit words. -/
def wnorm (xs : List Nat) (R : Option (Nat × Nat)) : AW :=
  (wfoldAll (xs.drop 2) R).map (fun R' => (xs.take 2, R'))

theorem wnorm_sound {xs : List Nat} {R : Option (Nat × Nat)} {W : List Nat} (h : gW xs R W) :
    gW' (wnorm xs R) W := by
  unfold wnorm
  cases e : wfoldAll (xs.drop 2) R with
  | none => trivial
  | some R' =>
    rw [← List.take_append_drop 2 xs] at h
    exact gW_split _ h e

def wcons (x : Nat) (aw : AW) : AW := aw.bind (fun p => wnorm (x :: p.1) p.2)

theorem wcons_sound {x w : Nat} {aw : AW} {W : List Nat} (hx : gD x w) (h : gW' aw W) : gW' (wcons x aw) (w :: W) := by
  match aw, h with
  | none, _ => trivial
  | some (xs, R), h => exact wnorm_sound (W := w :: W) ⟨hx, h⟩

def push2s : Nat → AW → AW
  | 0, aw => aw
  | m + 1, aw => wcons 2 (push2s m aw)

theorem push2s_sound : ∀ (m : Nat) {aw : AW} {W : List Nat}, gW' aw W → gW' (push2s m aw) (List.replicate m 2 ++ W)
  | 0, _, _, h => h
  | m + 1, _, _, h => wcons_sound (.inl ⟨by omega, rfl⟩) (push2s_sound m h)

theorem wfold_two {R R' : Option (Nat × Nat)} (e : wfold 2 R = some R') : wfold 2 R' = some R' := by
  match R with
  | none => simp [wfold] at e; subst e; simp [wfold]
  | some (e', s) => simp [wfold] at e; subst e; simp [wfold]

theorem wcons_wnorm (x : Nat) (ys : List Nat) (R : Option (Nat × Nat)) : wcons x (wnorm ys R) = wnorm (x :: ys) R := by
  rcases ys with _ | ⟨y₀, _ | ⟨y₁, ys⟩⟩
  · simp [wcons, wnorm, wfoldAll]
  · simp [wcons, wnorm, wfoldAll]
  · simp only [wcons, wnorm, wfoldAll, List.drop, List.take, Option.bind_map, Option.map_bind]
    cases wfoldAll ys R <;> simp [wfoldAll, Function.comp_def]

theorem push2s_eq (xs : List Nat) (R : Option (Nat × Nat)) :
    ∀ m : Nat, push2s (m + 1) (some (xs, R)) = wnorm (List.replicate (m + 1) 2 ++ xs) R
  | 0 => rfl
  | m + 1 => by
    show wcons 2 (push2s (m + 1) _) = _
    rw [push2s_eq xs R m, wcons_wnorm]; rfl

theorem wfoldAll_two (xs : List Nat) (R : Option (Nat × Nat)) :
    wfoldAll (2 :: 2 :: xs) R = wfoldAll (2 :: xs) R := by
  show ((wfoldAll xs R).bind (wfold 2)).bind (wfold 2) = (wfoldAll xs R).bind (wfold 2)
  cases wfoldAll xs R with
  | none => rfl
  | some R₀ =>
    simp only [Option.bind_some]
    cases h : wfold 2 R₀ with
    | none => rfl
    | some R' => exact wfold_two h

/-- Three words 2 in front are as good as any more. -/
theorem push2s_fix (aw : AW) : wcons 2 (push2s 3 aw) = push2s 3 aw := by
  rcases aw with _ | ⟨xs, R⟩
  · rfl
  show push2s 4 _ = push2s 3 _
  rw [push2s_eq xs R 3, push2s_eq xs R 2]
  show wnorm (2 :: 2 :: 2 :: 2 :: xs) R = wnorm (2 :: 2 :: 2 :: xs) R
  unfold wnorm
  simp only [List.drop, List.take]
  rw [wfoldAll_two]

theorem push2s_big (aw : AW) : ∀ m : Nat, push2s (m + 3) aw = push2s 3 aw
  | 0 => rfl
  | m + 1 => by
    show wcons 2 (push2s (m + 3) aw) = _
    rw [push2s_big aw m, push2s_fix]


theorem tw_two_eq (k : Nat) : ∀ j : Nat, tw 2 j k = List.replicate j 2 ++ [2 + k]
  | 0 => rfl
  | j + 1 => by show 2 :: tw 2 j k = _; rw [tw_two_eq k j]; rfl

/-- `tw a j k` in front, for the codes `a` and `k`. -/
def twExact (a : Nat) : Nat → Nat → AW → AW
  | 0, k, aw => wcons (addD a k) aw
  | j + 1, k, aw => wcons a (push2s j (wcons (addD 2 k) aw))

theorem twExact_sound {a av k kv : Nat} {aw : AW} {W : List Nat} (ha : gD a av) (hk : gD k kv) (h : gW' aw W) :
    ∀ j : Nat, gW' (twExact a j k aw) (tw av j kv ++ W)
  | 0 => wcons_sound (gD_add ha hk) h
  | j + 1 => by
    show gW' (wcons a _) (av :: (tw 2 j kv ++ W))
    rw [tw_two_eq, List.append_assoc]
    exact wcons_sound ha (push2s_sound j (wcons_sound (gD_add (.inl ⟨by omega, rfl⟩) hk) h))

theorem twExact_big (a k : Nat) (aw : AW) (j : Nat) : twExact a (j + 4) k aw = twExact a 4 k aw := by
  show wcons a (push2s (j + 3) _) = wcons a (push2s 3 _)
  rw [push2s_big]

/-- `tw a j k` in front, for `j` (capped at 4) in `js`. -/
def twA (a : Nat) (js : List Nat) (k : Nat) (aw : AW) : List AW := js.map (fun j => twExact a j k aw)

theorem twA_sound {a av k kv j : Nat} {js : List Nat} {aw : AW} {W : List Nat} (ha : gD a av) (hk : gD k kv)
    (h : gW' aw W) (hj : min j 4 ∈ js) : ∃ aw' ∈ twA a js k aw, gW' aw' (tw av j kv ++ W) := by
  refine ⟨_, List.mem_map.2 ⟨_, hj, rfl⟩, ?_⟩
  by_cases hj4 : j < 4
  · rw [Nat.min_eq_left (by omega)]; exact twExact_sound ha hk h j
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 4 := ⟨j - 4, by omega⟩
    rw [Nat.min_eq_right (by omega), ← twExact_big a k aw i]
    exact twExact_sound ha hk h _

/-- The values of `n / 3 - d` (capped at 4) for the numbers `n` with code `nc`. -/
def jsA (nc d : Nat) : List Nat :=
  if nc < 4 then [min (nc / 3 - d) 4] else (List.range 5).filter (fun j => (if nc = 4 then 2 else 1) - d ≤ j)

theorem jsA_mem {nc n d j : Nat} (h : gD nc n) (hj : j = n / 3 - d) : min j 4 ∈ jsA nc d := by
  unfold gD at h; unfold jsA
  by_cases h4 : nc < 4
  · simp only [h4, ↓reduceIte, List.mem_singleton]; omega
  · simp only [h4, ↓reduceIte, List.mem_filter, List.mem_range, decide_eq_true_eq]
    by_cases h5 : nc = 4 <;> simp only [h5, ↓reduceIte] <;> omega

/-! ## Abstract configurations -/

structure AC where
  two : Bool
  u : Nat
  q : St
  h : Nat
  lx : List Nat
  lr : Nat
  wx : List Nat
  wr : Option (Nat × Nat)
  deriving DecidableEq

def gC (a : AC) (u : Nat) (c : ACfg) : Prop :=
  a.u = u ∧ a.q = c.q ∧ gD a.h c.h ∧ gL a.lx a.lr c.L ∧ gW a.wx a.wr c.W

def gC' : Option AC → Nat → ACfg → Prop
  | none, _, _ => True
  | some a, u, c => gC a u c

def mkC (a : AC) (q : St) (h : Nat) (l : List Nat × Nat) (aw : AW) : Option AC :=
  aw.map (fun p => { a with q := q, h := h, lx := l.1, lr := l.2, wx := p.1, wr := p.2 })

theorem mkC_sound {a : AC} {q : St} {h hv : Nat} {l : List Nat × Nat} {aw : AW} {L W : List Nat}
    (hh : gD h hv) (hl : gL l.1 l.2 L) (hw : gW' aw W) : gC' (mkC a q h l aw) a.u ⟨q, hv, L, W⟩ := by
  match aw, hw with
  | none, _ => trivial
  | some (xs, R), hw => exact ⟨rfl, rfl, hh, hl, hw⟩

theorem gD_c (v : Nat) (hv : v < 4) : gD v v := .inl ⟨hv, rfl⟩

theorem mkC_sound' {a : AC} {q : St} {h hv : Nat} {xs : List Nat} {r : Nat} {wx : List Nat}
    {wr : Option (Nat × Nat)} {L W : List Nat}
    (hh : gD h hv) (hl : gL xs r L) (hw : gW wx wr W) : gC' (mkC a q h (xs, r) (some (wx, wr))) a.u ⟨q, hv, L, W⟩ :=
  mkC_sound (l := (xs, r)) (aw := some (wx, wr)) hh hl hw

theorem lcons_sound' {x n : Nat} {xs : List Nat} {r : Nat} {L : List Nat} (hx : gD x n) (h : gL xs r L) :
    gL (lcons x (xs, r)).1 (lcons x (xs, r)).2 (n :: L) := lcons_sound (l := (xs, r)) hx h

theorem lzeros_sound' {k m : Nat} {xs : List Nat} {r : Nat} {L : List Nat} (hk : gD k m) (h : gL xs r L) :
    gL (lzeros k (xs, r)).1 (lzeros k (xs, r)).2 (zs m L) := lzeros_sound (l := (xs, r)) hk h

/-! ## One abstract step -/

def absA (a : AC) : List (Option AC) :=
  if a.h ≠ 0 then (lpopA a.lx a.lr).map (fun t => mkC a .A 0 (lcons (addD t.1 a.h) (t.2.1, t.2.2)) (some (a.wx, a.wr)))
  else (wpopA a.wx a.wr).flatMap (fun t => if t.1 = 0 then [] else
    (subD t.1 1).map (fun k => mkC a .B 0 (lcons 1 (lzeros k (a.lx, a.lr))) (some (t.2.1, t.2.2))))

def absDE (a : AC) (inc : Nat) : List (Option AC) :=
  (lpopA a.lx a.lr).flatMap fun t => (wpopA a.wx a.wr).flatMap fun w =>
    if w.1 = 1 then [mkC a .D 0 (lcons (addD t.1 inc) (t.2.1, t.2.2)) (some (w.2.1, w.2.2))]
    else if w.1 = 2 then [mkC a .F 0 (lcons 0 (lcons (addD t.1 inc) (t.2.1, t.2.2))) (some (w.2.1, w.2.2))]
    else if w.1 = 0 then []
    else (subD w.1 3).map (fun k =>
      mkC a .B 0 (lcons 1 (lzeros k (lcons (addD t.1 inc) (t.2.1, t.2.2)))) (some (w.2.1, w.2.2)))

def absF (a : AC) : List (Option AC) :=
  if a.h ≠ 0 then [] else
  (lpopA a.lx a.lr).flatMap fun t => (wpopA a.wx a.wr).map fun w =>
    mkC a .A 0 (lcons (addD (addD t.1 w.1) 1) (t.2.1, t.2.2)) (some (w.2.1, w.2.2))

def absC (a : AC) : List (Option AC) :=
  if a.h ≠ 0 then [] else
  (lpopA a.lx a.lr).flatMap fun t => (wpopA a.wx a.wr).flatMap fun w =>
    if t.1 ≠ 0 then
      if w.1 = 1 then (wpopA w.2.1 w.2.2).map (fun w₂ =>
        mkC a .C 0 (lcons 0 (t.2.1, t.2.2)) (wcons 1 (wcons (addD w₂.1 t.1) (some (w₂.2.1, w₂.2.2)))))
      else (subD t.1 1).map (fun c =>
        mkC a .B 0 (lcons 1 (lzeros w.1 (lcons c (t.2.1, t.2.2)))) (some (w.2.1, w.2.2)))
    else (lpopA t.2.1 t.2.2).flatMap fun d =>
      if w.1 = 1 then [mkC a .F 0 (lcons 0 (lcons (addD d.1 2) (d.2.1, d.2.2))) (some (w.2.1, w.2.2))]
      else if w.1 = 0 then []
      else (subD w.1 2).map (fun k =>
        mkC a .B 0 (lcons 1 (lzeros k (lcons (addD d.1 2) (d.2.1, d.2.2)))) (some (w.2.1, w.2.2)))

def absBstep (a : AC) (n c d : Nat) (M : List Nat × Nat) (k : Nat) (W : List Nat × Option (Nat × Nat)) :
    List (Option AC) :=
  if resD n = 1 then
    (twA 1 (jsA n 0) k (some W)).map (fun aw => mkC a .B 0 (lcons c (lcons d M)) (wcons 0 aw))
  else if n = 2 then [mkC a .E (addD k 1) (lcons (addD c 3) (lcons d M)) (some W)]
  else if resD n = 2 then (twA 2 (jsA n 1) k (some W)).map (fun aw => mkC a .E 1 (lcons (addD c 3) (lcons d M)) aw)
  else if k = 0 then
    (twA 1 (jsA n 0) 0 (some W)).map (fun aw => mkC a .C 0 (lcons c (lcons d M)) aw)
  else if n = 0 then [mkC a .C 0 (lcons c (lcons d M)) (wcons (addD k 1) (some W))]
  else if n = 3 then [mkC a .A (addD k 1) (lcons (addD c 2) (lcons (addD d 2) M)) (some W)]
  else (twA 2 (jsA n 2) k (some W)).map (fun aw => mkC a .A 1 (lcons (addD c 2) (lcons (addD d 2) M)) aw)

def absB (a : AC) : List (Option AC) :=
  if a.h ≠ 0 then [] else
  (lpopA a.lx a.lr).flatMap fun t₁ => (lpopA t₁.2.1 t₁.2.2).flatMap fun t₂ => (lpopA t₂.2.1 t₂.2.2).flatMap fun t₃ =>
    (wpopA a.wx a.wr).flatMap fun w => absBstep a t₁.1 t₂.1 t₃.1 (t₃.2.1, t₃.2.2) w.1 (w.2.1, w.2.2)

def absAstep (a : AC) : List (Option AC) :=
  match a.q with
  | .A => absA a
  | .B => absB a
  | .C => absC a
  | .D => if a.h ≠ 0 then [] else absDE a 2
  | .E => if a.h ≠ 1 then [] else absDE a 3
  | .F => absF a

/-! ## Every concrete step is matched by an abstract one -/

theorem ite_t {c : Prop} [Decidable c] (h : c) {α : Sort _} (t e : α) : (if c then t else e) = t := by simp [h]
theorem ite_f {c : Prop} [Decidable c] (h : ¬c) {α : Sort _} (t e : α) : (if c then t else e) = e := by simp [h]

theorem gD_ne0 {d n : Nat} (h : gD d n) (hn : n ≠ 0) : d ≠ 0 := by unfold gD at h; omega
theorem gD_0 {d : Nat} (h : gD d 0) : d = 0 := by unfold gD at h; omega
theorem gD_1 {d : Nat} (h : gD d 1) : d = 1 := by unfold gD at h; omega
theorem gD_2 {d : Nat} (h : gD d 2) : d = 2 := by unfold gD at h; omega
theorem gD_ne {d n : Nat} (h : gD d n) (v : Nat) (hv : v < 4) (hn : n ≠ v) : d ≠ v := by unfold gD at h; omega

theorem sA {a : AC} {h n w : Nat} {M W : List Nat} {c' : ACfg} (hh : gD a.h h) (hL : gL a.lx a.lr (n :: M))
    (hW : gW a.wx a.wr (w :: W)) (e : astep' .A h (n :: M) (w :: W) = some (.go c')) :
    ∃ o ∈ absA a, gC' o a.u c' := by
  cases h with
  | zero =>
    have h0 := gD_0 hh
    cases w with
    | zero => simp [astep'] at e
    | succ k =>
      simp only [astep', Option.some.injEq, Out.go.injEq] at e
      subst e
      obtain ⟨t, ht, ht1, ht2⟩ := wpop_sound hW
      obtain ⟨kk, hkk, hk⟩ := gD_sub ht1 (by omega : 1 ≤ k + 1) (by omega)
      have hne := gD_ne0 ht1 (by omega)
      refine ⟨_, ?_, mkC_sound (gD_c 0 (by omega)) (lcons_sound (gD_c 1 (by omega)) (lzeros_sound' hk hL))
        (aw := some (t.2.1, t.2.2)) ht2⟩
      unfold absA
      simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte]
      exact List.mem_flatMap.2 ⟨t, ht, by simp only [hne, ↓reduceIte]; exact List.mem_map.2 ⟨kk, hkk, rfl⟩⟩
  | succ h =>
    simp only [astep', Option.some.injEq, Out.go.injEq] at e
    subst e
    obtain ⟨t, ht, ht1, ht2⟩ := lpop_sound hL
    have hne := gD_ne0 hh (by omega)
    have hx : gD (addD t.1 a.h) (n + h + 1) := gD_add (m := n) ht1 hh
    refine ⟨_, ?_, mkC_sound (gD_c 0 (by omega)) (lcons_sound (l := (t.2.1, t.2.2)) hx ht2) (aw := some (a.wx, a.wr)) hW⟩
    unfold absA
    simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte]
    exact List.mem_map.2 ⟨t, ht, rfl⟩

theorem sDE {a : AC} {inc n w : Nat} {M W : List Nat} {c' : ACfg} (hL : gL a.lx a.lr (n :: M))
    (hW : gW a.wx a.wr (w :: W)) (hinc : inc < 4)
    (e : (if w = 1 then some (Out.go ⟨.D, 0, (n + inc) :: M, W⟩)
      else if w = 2 then some (Out.go ⟨.F, 0, 0 :: (n + inc) :: M, W⟩)
      else if 3 ≤ w then some (Out.go ⟨.B, 0, 1 :: zs (w - 3) ((n + inc) :: M), W⟩) else none) = some (.go c')) :
    ∃ o ∈ absDE a inc, gC' o a.u c' := by
  obtain ⟨t, ht, ht1, ht2⟩ := lpop_sound hL
  obtain ⟨v, hv, hv1, hv2⟩ := wpop_sound hW
  have hx := gD_add ht1 (gD_c inc hinc)
  simp only [List.headD_cons] at ht1 hx
  unfold absDE
  by_cases w1 : w = 1
  · rw [ite_t w1] at e; cases e
    have := gD_1 (w1 ▸ hv1)
    refine ⟨_, List.mem_flatMap.2 ⟨t, ht, List.mem_flatMap.2 ⟨v, hv, by rw [ite_t this]; exact List.mem_singleton_self _⟩⟩,
      mkC_sound' (gD_c 0 (by omega)) (lcons_sound' hx ht2) hv2⟩
  by_cases w2 : w = 2
  · rw [ite_f w1, ite_t w2] at e; cases e
    have := gD_2 (w2 ▸ hv1)
    refine ⟨_, List.mem_flatMap.2 ⟨t, ht, List.mem_flatMap.2 ⟨v, hv, by
      rw [ite_f (by omega), ite_t this]; exact List.mem_singleton_self _⟩⟩,
      mkC_sound' (gD_c 0 (by omega)) (lcons_sound' (gD_c 0 (by omega)) (lcons_sound' hx ht2)) hv2⟩
  by_cases w3 : 3 ≤ w
  · rw [ite_f w1, ite_f w2, ite_t w3] at e; cases e
    obtain ⟨kk, hkk, hk⟩ := gD_sub hv1 w3 (by omega)
    have n1 := gD_ne hv1 1 (by omega) w1
    have n2 := gD_ne hv1 2 (by omega) w2
    have n0 := gD_ne hv1 0 (by omega) (by omega)
    refine ⟨_, List.mem_flatMap.2 ⟨t, ht, List.mem_flatMap.2 ⟨v, hv, ?_⟩⟩,
      mkC_sound' (gD_c 0 (by omega)) (lcons_sound' (gD_c 1 (by omega)) (lzeros_sound' hk (lcons_sound' hx ht2))) hv2⟩
    rw [ite_f n1, ite_f n2, ite_f n0]
    exact List.mem_map.2 ⟨kk, hkk, rfl⟩
  · rw [ite_f w1, ite_f w2, ite_f w3] at e; cases e

theorem astep'_D_eq (n w : Nat) (M W : List Nat) :
    astep' .D 0 (n :: M) (w :: W) =
      (if w = 1 then some (Out.go ⟨.D, 0, (n + 2) :: M, W⟩)
      else if w = 2 then some (Out.go ⟨.F, 0, 0 :: (n + 2) :: M, W⟩)
      else if 3 ≤ w then some (Out.go ⟨.B, 0, 1 :: zs (w - 3) ((n + 2) :: M), W⟩) else none) := by
  rcases w with _ | _ | _ | k <;> simp [astep']

theorem astep'_E_eq (n w : Nat) (M W : List Nat) :
    astep' .E 1 (n :: M) (w :: W) =
      (if w = 1 then some (Out.go ⟨.D, 0, (n + 3) :: M, W⟩)
      else if w = 2 then some (Out.go ⟨.F, 0, 0 :: (n + 3) :: M, W⟩)
      else if 3 ≤ w then some (Out.go ⟨.B, 0, 1 :: zs (w - 3) ((n + 3) :: M), W⟩) else none) := by
  rcases w with _ | _ | _ | k <;> simp [astep']

theorem sF {a : AC} {n w : Nat} {M W : List Nat} {c' : ACfg} (hh : gD a.h 0) (hL : gL a.lx a.lr (n :: M))
    (hW : gW a.wx a.wr (w :: W)) (e : astep' .F 0 (n :: M) (w :: W) = some (.go c')) :
    ∃ o ∈ absF a, gC' o a.u c' := by
  simp only [astep', Option.some.injEq, Out.go.injEq] at e
  subst e
  obtain ⟨t, ht, ht1, ht2⟩ := lpop_sound hL
  obtain ⟨v, hv, hv1, hv2⟩ := wpop_sound hW
  refine ⟨_, ?_, mkC_sound' (gD_c 0 (by omega)) (lcons_sound' (gD_add (gD_add ht1 hv1) (gD_c 1 (by omega))) ht2) hv2⟩
  unfold absF
  simp only [gD_0 hh, ne_eq, not_true_eq_false, ↓reduceIte]
  exact List.mem_flatMap.2 ⟨t, ht, List.mem_map.2 ⟨v, hv, rfl⟩⟩

theorem sC {a : AC} {n d w : Nat} {M W : List Nat} {c' : ACfg} (hh : gD a.h 0) (hL : gL a.lx a.lr (n :: d :: M))
    (hW : gW a.wx a.wr (w :: W)) (hC : ¬(w = 1 ∧ W = [])) (e : astep' .C 0 (n :: d :: M) (w :: W) = some (.go c')) :
    ∃ o ∈ absC a, gC' o a.u c' := by
  obtain ⟨t, ht, ht1, ht2⟩ := lpop_sound hL
  obtain ⟨v, hv, hv1, hv2⟩ := wpop_sound hW
  simp only [List.headD_cons, List.tail_cons] at ht1 ht2
  have hh0 := gD_0 hh
  unfold absC
  rw [ite_f (by simp [hh0])]
  cases n with
  | succ c =>
    have tn := gD_ne0 ht1 (by omega)
    by_cases w1 : w = 1
    · subst w1
      obtain ⟨k, W, rfl⟩ : ∃ k W', W = k :: W' := by
        cases W with
        | nil => exact absurd ⟨rfl, rfl⟩ hC
        | cons k W => exact ⟨k, W, rfl⟩
      simp only [astep', Option.some.injEq, Out.go.injEq] at e
      subst e
      obtain ⟨v₂, hv₂, hv₂1, hv₂2⟩ := wpop_sound hv2
      have hx : gD (addD v₂.1 t.1) (k + c + 1) := gD_add (m := k) (n := c + 1) hv₂1 ht1
      refine ⟨_, List.mem_flatMap.2 ⟨t, ht, List.mem_flatMap.2 ⟨v, hv, ?_⟩⟩,
        mkC_sound (gD_c 0 (by omega)) (lcons_sound' (gD_c 0 (by omega)) ht2)
          (wcons_sound (gD_c 1 (by omega)) (wcons_sound hx (aw := some (v₂.2.1, v₂.2.2)) hv₂2))⟩
      rw [ite_t tn, ite_t (gD_1 hv1)]
      exact List.mem_map.2 ⟨v₂, hv₂, rfl⟩
    · have e' : astep' .C 0 ((c + 1) :: d :: M) (w :: W) = some (.go ⟨.B, 0, 1 :: zs w (c :: d :: M), W⟩) := by
        rcases w with _ | _ | w
        · rfl
        · exact absurd rfl w1
        · rfl
      rw [e'] at e; cases e
      obtain ⟨cc, hcc, hc⟩ := gD_sub ht1 (by omega : 1 ≤ c + 1) (by omega)
      refine ⟨_, List.mem_flatMap.2 ⟨t, ht, List.mem_flatMap.2 ⟨v, hv, ?_⟩⟩,
        mkC_sound' (gD_c 0 (by omega)) (lcons_sound' (gD_c 1 (by omega)) (lzeros_sound' hv1 (lcons_sound' hc ht2))) hv2⟩
      rw [ite_t tn, ite_f (gD_ne hv1 1 (by omega) w1)]
      exact List.mem_map.2 ⟨cc, hcc, rfl⟩
  | zero =>
    have t0 := gD_0 ht1
    obtain ⟨t₂, ht₂, ht₂1, ht₂2⟩ := lpop_sound ht2
    simp only [List.headD_cons, List.tail_cons] at ht₂1 ht₂2
    have hx : gD (addD t₂.1 2) (d + 2) := gD_add ht₂1 (gD_c 2 (by omega))
    rcases w with _ | _ | k
    · simp [astep'] at e
    · simp only [astep', Option.some.injEq, Out.go.injEq] at e
      subst e
      refine ⟨_, List.mem_flatMap.2 ⟨t, ht, List.mem_flatMap.2 ⟨v, hv, ?_⟩⟩,
        mkC_sound' (gD_c 0 (by omega)) (lcons_sound' (gD_c 0 (by omega)) (lcons_sound' hx ht₂2)) hv2⟩
      rw [ite_f (by simp [t0])]
      refine List.mem_flatMap.2 ⟨t₂, ht₂, ?_⟩
      rw [ite_t (gD_1 hv1)]
      exact List.mem_singleton_self _
    · simp only [astep', Option.some.injEq, Out.go.injEq] at e
      subst e
      obtain ⟨kk, hkk, hk⟩ := gD_sub hv1 (by omega : 2 ≤ k + 2) (by omega)
      refine ⟨_, List.mem_flatMap.2 ⟨t, ht, List.mem_flatMap.2 ⟨v, hv, ?_⟩⟩,
        mkC_sound' (gD_c 0 (by omega)) (lcons_sound' (gD_c 1 (by omega)) (lzeros_sound' hk (lcons_sound' hx ht₂2))) hv2⟩
      rw [ite_f (by simp [t0])]
      refine List.mem_flatMap.2 ⟨t₂, ht₂, ?_⟩
      rw [ite_f (gD_ne hv1 1 (by omega) (by omega)), ite_f (gD_ne hv1 0 (by omega) (by omega))]
      exact List.mem_map.2 ⟨kk, hkk, rfl⟩

theorem absBstep_sound {a : AC} {nc cc dc kc : Nat} {Mx : List Nat × Nat} {Wx : List Nat × Option (Nat × Nat)}
    {n c d k : Nat} {M W : List Nat} {c' : ACfg} (hn : gD nc n) (hc : gD cc c) (hd : gD dc d) (hM : gL Mx.1 Mx.2 M)
    (hk : gD kc k) (hW : gW Wx.1 Wx.2 W) (e : bstep n c d M k W = some (.go c')) :
    ∃ o ∈ absBstep a nc cc dc Mx kc Wx, gC' o a.u c' := by
  have hr := gD_res hn
  have hCD := lcons_sound hc (lcons_sound hd hM)
  have hW' : gW' (some Wx) W := hW
  unfold bstep at e
  unfold absBstep
  by_cases h1 : n % 3 = 1
  · rw [ite_t h1] at e; cases e
    rw [ite_t (by omega)]
    obtain ⟨aw, haw, hg⟩ := twA_sound (j := n / 3) (gD_c 1 (by omega)) hk hW' (jsA_mem (d := 0) hn (by omega))
    exact ⟨_, List.mem_map.2 ⟨aw, haw, rfl⟩, mkC_sound (gD_c 0 (by omega)) hCD (wcons_sound (gD_c 0 (by omega)) hg)⟩
  rw [ite_f h1] at e; rw [ite_f (by omega)]
  by_cases h2 : n = 2
  · rw [ite_t h2] at e; cases e
    rw [ite_t ((gD_eq hn 2 (by omega)).1 h2)]
    exact ⟨_, List.mem_singleton_self _, mkC_sound (gD_add hk (gD_c 1 (by omega)))
      (lcons_sound (gD_add hc (gD_c 3 (by omega))) (lcons_sound hd hM)) hW'⟩
  rw [ite_f h2] at e; rw [ite_f (fun h => h2 ((gD_eq hn 2 (by omega)).2 h))]
  by_cases h3 : n % 3 = 2
  · rw [ite_t h3] at e; cases e
    rw [ite_t (by omega)]
    obtain ⟨aw, haw, hg⟩ := twA_sound (j := n / 3 - 1) (gD_c 2 (by omega)) hk hW' (jsA_mem hn rfl)
    exact ⟨_, List.mem_map.2 ⟨aw, haw, rfl⟩,
      mkC_sound (gD_c 1 (by omega)) (lcons_sound (gD_add hc (gD_c 3 (by omega))) (lcons_sound hd hM)) hg⟩
  rw [ite_f h3] at e; rw [ite_f (by omega)]
  by_cases h4 : k = 0
  · rw [ite_t h4] at e; cases e
    rw [ite_t ((gD_eq hk 0 (by omega)).1 h4)]
    obtain ⟨aw, haw, hg⟩ := twA_sound (j := n / 3) (gD_c 1 (by omega)) (gD_c 0 (by omega)) hW' (jsA_mem (d := 0) hn (by omega))
    exact ⟨_, List.mem_map.2 ⟨aw, haw, rfl⟩, mkC_sound (gD_c 0 (by omega)) hCD hg⟩
  rw [ite_f h4] at e; rw [ite_f (fun h => h4 ((gD_eq hk 0 (by omega)).2 h))]
  by_cases h5 : n = 0
  · rw [ite_t h5] at e; cases e
    rw [ite_t ((gD_eq hn 0 (by omega)).1 h5)]
    exact ⟨_, List.mem_singleton_self _, mkC_sound (gD_c 0 (by omega)) hCD
      (wcons_sound (gD_add hk (gD_c 1 (by omega))) hW')⟩
  rw [ite_f h5] at e; rw [ite_f (fun h => h5 ((gD_eq hn 0 (by omega)).2 h))]
  by_cases h6 : n = 3
  · rw [ite_t h6] at e; cases e
    rw [ite_t ((gD_eq hn 3 (by omega)).1 h6)]
    exact ⟨_, List.mem_singleton_self _, mkC_sound (gD_add hk (gD_c 1 (by omega)))
      (lcons_sound (gD_add hc (gD_c 2 (by omega))) (lcons_sound (gD_add hd (gD_c 2 (by omega))) hM)) hW'⟩
  rw [ite_f h6] at e; rw [ite_f (fun h => h6 ((gD_eq hn 3 (by omega)).2 h))]
  cases e
  obtain ⟨aw, haw, hg⟩ := twA_sound (j := n / 3 - 2) (gD_c 2 (by omega)) hk hW' (jsA_mem hn rfl)
  exact ⟨_, List.mem_map.2 ⟨aw, haw, rfl⟩, mkC_sound (gD_c 1 (by omega))
    (lcons_sound (gD_add hc (gD_c 2 (by omega))) (lcons_sound (gD_add hd (gD_c 2 (by omega))) hM)) hg⟩

theorem sB {a : AC} {n c d w : Nat} {M W : List Nat} {c' : ACfg} (hh : gD a.h 0)
    (hL : gL a.lx a.lr (n :: c :: d :: M)) (hW : gW a.wx a.wr (w :: W))
    (e : astep' .B 0 (n :: c :: d :: M) (w :: W) = some (.go c')) : ∃ o ∈ absB a, gC' o a.u c' := by
  have e' : bstep n c d M w W = some (.go c') := by simp only [astep'] at e; exact e
  obtain ⟨t₁, ht₁, h₁, l₁⟩ := lpop_sound hL
  obtain ⟨t₂, ht₂, h₂, l₂⟩ := lpop_sound l₁
  obtain ⟨t₃, ht₃, h₃, l₃⟩ := lpop_sound l₂
  obtain ⟨v, hv, hv1, hv2⟩ := wpop_sound hW
  simp only [List.headD_cons, List.tail_cons] at h₁ h₂ h₃ l₃
  obtain ⟨o, ho, hg⟩ := absBstep_sound (a := a) (Mx := (t₃.2.1, t₃.2.2)) (Wx := (v.2.1, v.2.2)) h₁ h₂ h₃ l₃ hv1 hv2 e'
  refine ⟨o, ?_, hg⟩
  unfold absB
  rw [ite_f (by simp [gD_0 hh])]
  exact List.mem_flatMap.2 ⟨t₁, ht₁, List.mem_flatMap.2 ⟨t₂, ht₂, List.mem_flatMap.2 ⟨t₃, ht₃,
    List.mem_flatMap.2 ⟨v, hv, ho⟩⟩⟩⟩

/-- **Every step of the block machine is matched by an abstract step.** -/
theorem absAstep_sound {a : AC} {u : Nat} {c c' : ACfg} (hc : gC a u c) (hne : c.W ≠ [])
    (hC : ¬(c.q = .C ∧ c.W = [1])) (e : astep c = some (.go c')) : ∃ o ∈ absAstep a, gC' o u c' := by
  obtain ⟨q, h, L, W⟩ := c
  obtain ⟨hu, hq, hh, hL, hW⟩ := hc
  subst hu
  have hP := gL_pad 4 hL
  obtain ⟨n, c₁, d, M, hPe⟩ : ∃ n c₁ d M, pad 4 L = n :: c₁ :: d :: M := ⟨_, _, _, _, rfl⟩
  rw [hPe] at hP
  obtain ⟨w, W, rfl⟩ : ∃ w W', W = w :: W' := by
    cases W with
    | nil => exact absurd rfl hne
    | cons w W => exact ⟨w, W, rfl⟩
  simp only at hq hh hL hW hC
  have e₀ : astep' q h (n :: c₁ :: d :: M) (w :: W) = some (.go c') := by rw [← hPe]; exact e
  unfold absAstep
  rw [hq]
  cases q with
  | A => exact sA hh hP hW e₀
  | B =>
    cases h with
    | zero => exact sB hh hP hW e₀
    | succ h => simp [astep'] at e₀
  | C =>
    cases h with
    | zero => exact sC hh hP hW (fun h => hC ⟨rfl, by rw [h.1, h.2]⟩) e₀
    | succ h => simp [astep'] at e₀
  | D =>
    cases h with
    | zero =>
      dsimp only
      rw [ite_f (by simp [gD_0 hh])]
      rw [astep'_D_eq] at e₀
      exact sDE hP hW (by omega) e₀
    | succ h => simp [astep'] at e₀
  | E =>
    by_cases h1 : h = 1
    · subst h1
      dsimp only
      rw [ite_f (by simp [gD_1 hh])]
      rw [astep'_E_eq] at e₀
      exact sDE hP hW (by omega) e₀
    · exfalso
      rcases h with _ | h
      · simp [astep'] at e₀
      · rcases h with _ | h
        · exact h1 rfl
        · simp [astep'] at e₀
  | F =>
    cases h with
    | zero => exact sF hh hP hW e₀
    | succ h => simp [astep'] at e₀

/-! ## One step of `pre` -/

/-- `2`: the words are all 2 for sure; `1`: they may be; `0`: they are not. -/
def allTwoA : List Nat → Option (Nat × Nat) → Nat
  | [], none => 2
  | [], some (e, s) => if e = 2 ∧ s = 2 then 1 else 0
  | x :: xs, R => if x = 2 then allTwoA xs R else 0

/-- Take a word `0 1 1` from the supply. -/
def unfoldA (a : AC) : Option AC :=
  mkC { a with u := a.u + 1 } a.q a.h (a.lx, a.lr) (wnorm (a.wx ++ [2]) none)

/-- One step of `pre` on descriptions; `[]` where `pre` stops for sure. -/
def absNext (a : AC) : List (Option AC) :=
  if a.q = .A ∧ a.h = 0 ∧ allTwoA a.wx a.wr = 2 then []
  else if (a.wx = [] ∧ a.wr = none) ∨ (a.q = .C ∧ a.wx = [1] ∧ a.wr = none) then [unfoldA a]
  else if a.q = .C ∧ a.wx = [] ∧ a.wr = some (1, 1) then [none]
  else absAstep a

/-- The codes `xs` then the rest `r` describe blocks at least 2, then 0s. -/
def gzB : List Nat → Nat → Bool
  | [], r => decide (r ≤ 1)
  | x :: xs, r => (decide (2 ≤ x) && gzB xs r) || (x == 0 && xs.all (· == 0) && r == 0)

/-- Moreover the first block is at least 2. -/
def tailB : List Nat → Nat → Bool
  | [], r => r == 1
  | x :: xs, r => decide (2 ≤ x) && gzB xs r

/-- Where `pre` may stop: at most two words taken, the bound on `c`, and the blocks after the first at least 2. -/
def stopP (a : AC) : Prop :=
  a.q = .A → a.h = 0 → allTwoA a.wx a.wr ≠ 0 → a.u ≤ 2 ∧ ∀ t ∈ lpopA a.lx a.lr,
    2 * a.u ≤ lowD t.1 + 2 * a.wx.length + (if a.two then 1 else 0) ∧ tailB t.2.1 t.2.2 = true

instance (a : AC) : Decidable (stopP a) := by unfold stopP; infer_instance

/-! ## The reachable descriptions, computed -/

/-- A key for the search tree. -/
def keyL : List Nat → Nat
  | [] => 0
  | x :: xs => 1 + x + 8 * keyL xs

def keyQ : St → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

def keyC (a : AC) : Nat :=
  let wr := match a.wr with | none => 0 | some (e, s) => 1 + e + 4 * s
  (if a.two then 1 else 0) + 2 * (a.u + 8 * (keyQ a.q + 6 * (a.h + 8 * (a.lr + 4 * (wr + 32 * (keyL a.wx +
    1024 * keyL a.lx))))))

inductive TS where
  | leaf : TS
  | node : TS → AC → TS → TS

def TS.mem (b : AC) : TS → Bool
  | .leaf => false
  | .node l a r => if keyC b < keyC a then l.mem b else if keyC a < keyC b then r.mem b else if b = a then true
      else l.mem b

def TS.ins (b : AC) : TS → TS
  | .leaf => .node .leaf b .leaf
  | .node l a r => if keyC b < keyC a then .node (l.ins b) a r else if keyC a < keyC b then .node l a (r.ins b)
      else if b = a then .node l a r else .node (l.ins b) a r

def TS.toList : TS → List AC
  | .leaf => []
  | .node l a r => l.toList ++ a :: r.toList

theorem TS.mem_toList {b : AC} : ∀ {t : TS}, t.mem b = true → b ∈ t.toList
  | .leaf, h => by simp [TS.mem] at h
  | .node l a r, h => by
    simp only [TS.mem] at h
    simp only [TS.toList, List.mem_append, List.mem_cons]
    split at h
    · exact .inl (mem_toList h)
    split at h
    · exact .inr (.inr (mem_toList h))
    split at h
    · rename_i e; exact .inr (.inl e)
    · exact .inl (mem_toList h)

/-- Add the new descriptions to the tree and to the frontier. -/
def addAll : List (Option AC) → TS → List AC → TS × List AC
  | [], t, fr => (t, fr)
  | none :: os, t, fr => addAll os t fr
  | some b :: os, t, fr => if t.mem b then addAll os t fr else addAll os (t.ins b) (b :: fr)

def explore : Nat → TS → List AC → TS
  | 0, t, _ => t
  | _ + 1, t, [] => t
  | f + 1, t, a :: fr => match addAll (absNext a) t fr with
    | (t', fr') => explore f t' fr'

def mkS (two : Bool) (x r : Nat) : AC := ⟨two, 0, .B, 0, [x], r, [0, 1], none⟩

/-- The starts: the block left of the last is 2 (`two`), 3 or more, or there is none; the blocks further left are at
least 2, then 0s. -/
def starts : List AC :=
  [mkS true 2 0, mkS true 2 1] ++ ([3, 4, 5, 6].flatMap fun x => [mkS false x 0, mkS false x 1]) ++ [mkS false 0 0]

/-- The descriptions found from the starts (evaluated by `OffsetGen.lean` to write the tree in `OffsetData.lean`). -/
def reach : TS := explore 100000 (starts.foldl (fun t a => t.ins a) .leaf) starts

/-- One description is fine: where `pre` may stop it has the bound, and its abstract steps are all in the tree `t`
and keep `two`. -/
def okA (t : TS) (a : AC) : Bool :=
  decide (stopP a) && (absNext a).all fun o => match o with
    | some b => t.mem b && b.two == a.two
    | none => false

def okT (t s : TS) : Bool := s.toList.all (okA t)

theorem okT_node (t l r : TS) (a : AC) : okT t (.node l a r) = (okT t l && okA t a && okT t r) := by
  simp only [okT, TS.toList, List.all_append, List.all_cons, Bool.and_assoc]

def checkT (t : TS) : Bool := starts.all (fun a => t.mem a) && okT t t

/-! ## Soundness of the step of `pre` -/

theorem Seq.mem_e {e s : Nat} {W : List Nat} (h : Seq e s W) : e ∈ W := by
  induction h with
  | one => exact List.mem_singleton_self _
  | cons _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem Seq.mem_s {e s : Nat} {W : List Nat} (h : Seq e s W) : s ∈ W := by
  cases h <;> simp

theorem allTwo_mem {W : List Nat} (h : allTwo W = true) : ∀ x ∈ W, x = 2 := by
  intro x hx
  rw [allTwo_eq h] at hx
  exact List.eq_of_mem_replicate hx

theorem allTwoA_ne : ∀ {wx : List Nat} {wr : Option (Nat × Nat)} {W : List Nat}, gW wx wr W → (∀ x ∈ W, x = 2) →
    allTwoA wx wr ≠ 0
  | [], none, _, _, _ => by simp [allTwoA]
  | [], some (e, s), W, h, h2 => by
    have h' : Seq e s W := h
    have he := h2 _ h'.mem_e
    have hs := h2 _ h'.mem_s
    simp [allTwoA, he, hs]
  | _ :: _, _, [], h, _ => h.elim
  | x :: xs, R, w :: W, h, h2 => by
    have hw := h2 w (List.mem_cons_self ..)
    have hx : x = 2 := gD_2 (hw ▸ h.1)
    simp only [allTwoA, hx, ↓reduceIte]
    exact allTwoA_ne h.2 (fun y hy => h2 y (List.mem_cons_of_mem _ hy))

theorem allTwoA_two : ∀ {wx : List Nat} {wr : Option (Nat × Nat)} {W : List Nat}, gW wx wr W → allTwoA wx wr = 2 →
    allTwo W = true
  | [], none, W, h, _ => by rw [show W = [] from h]; rfl
  | [], some (e, s), _, _, h2 => by simp only [allTwoA] at h2; split at h2 <;> omega
  | _ :: _, _, [], h, _ => h.elim
  | x :: xs, R, w :: W, h, h2 => by
    simp only [allTwoA] at h2
    split at h2
    · rename_i hx
      have hw : w = 2 := gD_small (hx ▸ h.1) (by omega)
      simp only [allTwo, hw, BEq.rfl, Bool.true_and]
      exact allTwoA_two h.2 h2
    · omega

theorem gW_snoc : ∀ {wx W : List Nat}, gW wx none W → gW (wx ++ [2]) none (W ++ [2])
  | [], W, h => by
    rw [show W = [] from h]
    show gD 2 2 ∧ gW [] none []
    exact ⟨gD_c 2 (by omega), rfl⟩
  | _ :: _, [], h => h.elim
  | x :: xs, w :: W, h => by
    show gD x w ∧ gW (xs ++ [2]) none (W ++ [2])
    exact ⟨h.1, gW_snoc h.2⟩

theorem unfoldA_sound {a : AC} {u : Nat} {c : ACfg} (hc : gC a u c) (hr : a.wr = none) :
    gC' (unfoldA a) (u + 1) ⟨c.q, c.h, c.L, c.W ++ [2]⟩ := by
  obtain ⟨hu, hq, hh, hL, hW⟩ := hc
  rw [hr] at hW
  have := mkC_sound (a := { a with u := a.u + 1 }) (q := a.q) (l := (a.lx, a.lr)) hh hL (wnorm_sound (gW_snoc hW))
  rw [← hu, ← hq]
  exact this

theorem gW_one {wx : List Nat} {wr : Option (Nat × Nat)} (h : gW wx wr [1]) :
    (wx = [] ∧ wr = some (1, 1)) ∨ (wx = [1] ∧ wr = none) := by
  match wx, wr, h with
  | [], none, h => exact absurd (h : [1] = []) (List.cons_ne_nil _ _)
  | [], some (e, s), h =>
    have h' : Seq e s [1] := h
    cases h' with
    | one => exact .inl ⟨rfl, rfl⟩
    | cons _ _ _ hs => exact absurd rfl hs.ne_nil
  | x :: xs, R, h =>
    obtain ⟨hx, hr⟩ := h
    obtain ⟨rfl, rfl⟩ := gW_nil hr
    exact .inr ⟨by rw [gD_1 hx], rfl⟩

theorem gW_single {W : List Nat} (h : gW [1] none W) : W = [1] := by
  match W, h with
  | [], h => exact h.elim
  | w :: W, h =>
    obtain ⟨h1, h2⟩ := h
    rw [gD_small h1 (by omega), show W = [] from h2]

theorem gW_len : ∀ {wx : List Nat} {wr : Option (Nat × Nat)} {W : List Nat}, gW wx wr W → wx.length ≤ W.length
  | [], _, _, _ => Nat.zero_le _
  | _ :: _, _, [], h => h.elim
  | _ :: _, _, _ :: _, h => Nat.succ_le_succ (gW_len h.2)

/-- **Every step of `pre` that does not stop is matched by an abstract one.** -/
theorem absNext_sound {a : AC} {u : Nat} {c : ACfg} (hc : gC a u c)
    (hs : ¬(c.q = .A ∧ c.h = 0 ∧ allTwo c.W = true)) :
    (c.W = [] ∨ (c.q = .C ∧ c.W = [1]) → ∃ o ∈ absNext a, gC' o (u + 1) ⟨c.q, c.h, c.L, c.W ++ [2]⟩) ∧
    (∀ c', ¬(c.W = [] ∨ (c.q = .C ∧ c.W = [1])) → astep c = some (.go c') → ∃ o ∈ absNext a, gC' o u c') := by
  have hc0 := hc
  obtain ⟨hu, hq, hh, hL, hW⟩ := hc
  unfold absNext
  rw [ite_f (by
    rintro ⟨h1, h2, h3⟩
    rw [h2] at hh
    exact hs ⟨by rw [← hq]; exact h1, gD_small hh (by omega), allTwoA_two hW h3⟩)]
  by_cases hB : (a.wx = [] ∧ a.wr = none) ∨ (a.q = .C ∧ a.wx = [1] ∧ a.wr = none)
  · rw [ite_t hB]
    have hr : a.wr = none := by rcases hB with h | h; exact h.2; exact h.2.2
    refine ⟨fun _ => ⟨_, List.mem_singleton_self _, unfoldA_sound hc0 hr⟩, fun c' hn _ => ?_⟩
    exfalso
    apply hn
    rcases hB with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · left; rw [h1, h2] at hW; exact hW
    · right
      rw [h2, h3] at hW
      exact ⟨by rw [← hq]; exact h1, gW_single hW⟩
  rw [ite_f hB]
  by_cases hN : a.q = .C ∧ a.wx = [] ∧ a.wr = some (1, 1)
  · rw [ite_t hN]
    exact ⟨fun _ => ⟨none, List.mem_singleton_self _, trivial⟩, fun _ _ _ => ⟨none, List.mem_singleton_self _, trivial⟩⟩
  rw [ite_f hN]
  refine ⟨fun hU => ?_, fun c' hn e => absAstep_sound hc0 (fun h => hn (.inl h)) (fun h => hn (.inr h)) e⟩
  exfalso
  rcases hU with h1 | ⟨h1, h2⟩
  · rw [h1] at hW
    obtain ⟨e1, e2⟩ := gW_nil hW
    exact hB (.inl ⟨e1, e2⟩)
  · rw [h2] at hW
    rcases gW_one hW with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact hN ⟨by rw [hq]; exact h1, e1, e2⟩
    · exact hB (.inr ⟨by rw [hq]; exact h1, e1, e2⟩)

/-! ## Where `pre` stops -/

/-- Blocks at least 2, then 0s. -/
def GZ (M : List Nat) : Prop := ∃ g z, M = g ++ z ∧ (∀ x ∈ g, 2 ≤ x) ∧ allZ z

theorem allZ_of_gL : ∀ {xs : List Nat} {L : List Nat}, xs.all (· == 0) = true → gL xs 0 L → allZ L
  | [], _, _, h => h
  | x :: xs, L, hx, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hx
    obtain ⟨h1, h2⟩ := h
    rw [hx.1] at h1
    have h0 := gD_small h1 (by omega)
    have ih := allZ_of_gL hx.2 h2
    cases L with
    | nil => intro b hb; cases hb
    | cons b L =>
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h0
      · exact ih y hy

theorem gzB_sound : ∀ {xs : List Nat} {r : Nat} {L : List Nat}, gzB xs r = true → gL xs r L → GZ L
  | [], r, L, hb, h => by
    simp only [gzB, decide_eq_true_eq] at hb
    by_cases h0 : r = 0
    · subst h0
      exact ⟨[], L, rfl, by simp, h⟩
    · obtain rfl : r = 1 := by omega
      obtain ⟨b, g, z, rfl, hb2, hg, hz⟩ := h
      exact ⟨b :: g, z, rfl, List.forall_mem_cons.2 ⟨hb2, hg⟩, hz⟩
  | x :: xs, r, L, hb, h => by
    simp only [gzB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
    obtain ⟨h1, h2⟩ := h
    rcases hb with ⟨hx, hb⟩ | ⟨⟨hx, hxs⟩, hr⟩
    · have hv := (gD_ge h1 2 (by omega)).2 hx
      obtain ⟨g, z, he, hg, hz⟩ := gzB_sound hb h2
      cases L with
      | nil => simp at hv
      | cons b L =>
        simp only [List.headD_cons, List.tail_cons] at hv he
        exact ⟨b :: g, z, by rw [he]; rfl, List.forall_mem_cons.2 ⟨hv, hg⟩, hz⟩
    · subst hr
      refine ⟨[], L, rfl, by simp, allZ_of_gL (xs := x :: xs) ?_ ⟨h1, h2⟩⟩
      simp only [List.all_cons, hx, hxs, beq_self_eq_true, Bool.and_self]

theorem tailB_sound {xs : List Nat} {r : Nat} {L : List Nat} (hb : tailB xs r = true) (h : gL xs r L) :
    ∃ b M, L = b :: M ∧ 2 ≤ b ∧ GZ M := by
  cases xs with
  | nil =>
    simp only [tailB, beq_iff_eq] at hb
    subst hb
    obtain ⟨b, g, z, rfl, hb2, hg, hz⟩ := h
    exact ⟨b, g ++ z, rfl, hb2, g, z, rfl, hg, hz⟩
  | cons x xs =>
    simp only [tailB, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨h1, h2⟩ := h
    have hv := (gD_ge h1 2 (by omega)).2 hb.1
    cases L with
    | nil => simp at hv
    | cons b M => exact ⟨b, M, rfl, by simpa using hv, gzB_sound hb.2 h2⟩

theorem checkT_sound {t : TS} (h : checkT t = true) :
    (∀ a ∈ starts, a ∈ t.toList) ∧
      ∀ a ∈ t.toList, stopP a ∧ ∀ o ∈ absNext a, ∃ b, o = some b ∧ b ∈ t.toList ∧ b.two = a.two := by
  unfold checkT okT okA at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨fun a ha => TS.mem_toList (h.1 a ha), fun a ha => ⟨(h.2 a ha).1, fun o ho => ?_⟩⟩
  have := (h.2 a ha).2 o ho
  match o, this with
  | some b, hb =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact ⟨b, rfl, TS.mem_toList hb.1, hb.2⟩
  | none, hb => cases hb

/-- What `pre` gives where it stops: two explicit blocks, the bound on `c`, the blocks after the first at least 2
(then 0s), and at most two words taken. -/
def Res (two : Bool) (L : List Nat) (p u : Nat) : Prop :=
  ∃ x b M, L = x :: b :: M ∧ 2 * u ≤ x + 2 * p + (if two then 1 else 0) ∧ 2 ≤ b ∧ GZ M ∧ u ≤ 2

theorem pre_abs {T : List AC}
    (hT : ∀ a ∈ T, stopP a ∧ ∀ o ∈ absNext a, ∃ b, o = some b ∧ b ∈ T ∧ b.two = a.two) :
    ∀ (f : Nat) {c : ACfg} {u : Nat} {a : AC} {L : List Nat} {p u' : Nat}, a ∈ T → gC a u c →
      pre f c u = some (L, p, u') → Res a.two L p u' := by
  intro f
  induction f with
  | zero => intro c u a L p u' _ _ e; cases e
  | succ f ih =>
    intro c u a L p u' ha hc e
    have hc0 := hc
    obtain ⟨hu, hq, hh, hL, hW⟩ := hc
    unfold pre at e
    split at e
    · rename_i hs
      cases e
      obtain ⟨h1, h2, h3⟩ := hs
      have hA : a.q = .A := by rw [hq]; exact h1
      have h0 : a.h = 0 := by rw [h2] at hh; exact gD_0 hh
      have hne := allTwoA_ne hW (allTwo_mem h3)
      obtain ⟨hu2, hall⟩ := (hT a ha).1 hA h0 hne
      obtain ⟨t, ht, hx, hl⟩ := lpop_sound hL
      obtain ⟨hb, htl⟩ := hall t ht
      obtain ⟨b, M, hLe, hb2, hM⟩ := tailB_sound htl hl
      refine ⟨c.L.headD 0, b, M, ?_, ?_, hb2, hM, by omega⟩
      · show c.L.headD 0 :: pad 1 c.L.tail = _
        rw [hLe]; rfl
      · have := gD_low hx
        have := gW_len hW
        omega
    split at e
    · rename_i hs1 hs2
      obtain ⟨o, ho, hg⟩ := (absNext_sound hc0 hs1).1 hs2
      obtain ⟨b, rfl, hbT, hbt⟩ := (hT a ha).2 o ho
      rw [← hbt]
      exact ih hbT hg e
    · rename_i hs1 hs2
      split at e
      · rename_i c' hc'
        obtain ⟨o, ho, hg⟩ := (absNext_sound hc0 hs1).2 c' hs2 hc'
        obtain ⟨b, rfl, hbT, hbt⟩ := (hT a ha).2 o ho
        rw [← hbt]
        exact ih hbT hg e
      · cases e

theorem starts_mem (two : Bool) (x r : Nat) (hx : (two = true ∧ x = 2) ∨ (two = false ∧ 3 ≤ x ∧ x ≤ 6))
    (hr : r ≤ 1) : mkS two x r ∈ starts := by
  obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
  · rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, hx⟩
    · decide
    · obtain rfl | rfl | rfl | rfl : x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by omega
      all_goals decide
  · rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, hx⟩
    · decide
    · obtain rfl | rfl | rfl | rfl : x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by omega
      all_goals decide

theorem start_mem {ls : List Nat} (hg : ∀ b ∈ ls, 2 ≤ b) :
    ∃ a ∈ starts, a.two = (ls.headD 0 == 2) ∧ gC a 0 ⟨.B, 0, pad 1 ls, [0, 1]⟩ := by
  have hW : gW [0, 1] none [0, 1] := ⟨gD_c 0 (by omega), gD_c 1 (by omega), rfl⟩
  cases ls with
  | nil =>
    refine ⟨mkS false 0 0, by decide, rfl, rfl, rfl, gD_c 0 (by omega), ?_, hW⟩
    exact ⟨gD_c 0 (by omega), fun b hb => by cases hb⟩
  | cons x rest =>
    have hx : 2 ≤ x := hg x (List.mem_cons_self ..)
    have hrest : ∀ b ∈ rest, 2 ≤ b := fun b hb => hg b (List.mem_cons_of_mem _ hb)
    have hR : gR (if rest = [] then 0 else 1) rest := by
      cases rest with
      | nil => exact fun b hb => by cases hb
      | cons y g =>
        exact ⟨y, g, [], by simp, hrest y (List.mem_cons_self ..),
          fun b hb => hrest b (List.mem_cons_of_mem _ hb), fun b hb => by cases hb⟩
    have hr : (if rest = [] then 0 else 1) ≤ 1 := by split <;> omega
    refine ⟨mkS (x == 2) (mkD x) (if rest = [] then 0 else 1), starts_mem _ _ _ ?_ hr, rfl, rfl, rfl,
      gD_c 0 (by omega), ⟨gD_mk x, hR⟩, hW⟩
    unfold mkD
    by_cases h2 : x = 2
    · left; subst h2; exact ⟨rfl, rfl⟩
    · right; refine ⟨by simp [h2], ?_⟩
      split <;> omega

/-- Where `pre` stops, given a tree `t` that passes `checkT` (`OffsetData.offset_bound` with the kernel-checked
tree).  For every list `ls` of blocks of at least 2 (any number of them, nearest first), if `pre` stops then it returns two explicit blocks
`a, b` and `p`, `u` with `2u ≤ a + 2p + 1`, and `2u ≤ a + 2p` unless `ls` starts with 2; `u ≤ 2`; `b ≥ 2`, and the
blocks after `b` are at least 2, then 0s. -/
theorem offset_bound_of {t : TS} (ht : checkT t = true) {ls : List Nat} (hg : ∀ b ∈ ls, 2 ≤ b) {f : Nat}
    {L : List Nat} {p u : Nat}
    (e : pre f ⟨.B, 0, pad 1 ls, [0, 1]⟩ 0 = some (L, p, u)) :
    ∃ a b M, L = a :: b :: M ∧ 2 * u ≤ a + 2 * p + (if ls.headD 0 = 2 then 1 else 0) ∧ 2 ≤ b ∧ GZ M ∧ u ≤ 2 := by
  obtain ⟨hs, hT⟩ := checkT_sound ht
  obtain ⟨a, ha, htwo, hc⟩ := start_mem hg
  obtain ⟨x, b, M, h1, h2, h3, h4, h5⟩ := pre_abs hT f (hs a ha) hc e
  refine ⟨x, b, M, h1, ?_, h3, h4, h5⟩
  rw [htwo] at h2
  by_cases hx : ls.headD 0 = 2
  · simp only [hx, BEq.rfl, ↓reduceIte] at h2 ⊢; exact h2
  · simp only [hx, ↓reduceIte] at h2 ⊢
    simp only [beq_iff_eq, hx, ↓reduceIte] at h2
    exact h2

theorem lt_allZ : ∀ {z : List Nat}, allZ z → lt z = lt []
  | [], _ => rfl
  | b :: z, h => by
    have hb : b = 0 := h b (List.mem_cons_self ..)
    subst hb
    show rep 0 [true] (cons false (lt z)) = blank
    rw [rep_zero, lt_allZ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    exact cons_false_blank

theorem lt_app_allZ {z : List Nat} (hz : allZ z) : ∀ L : List Nat, lt (L ++ z) = lt L
  | [] => lt_allZ hz
  | b :: L => by
    show rep b [true] (cons false (lt (L ++ z))) = rep b [true] (cons false (lt L))
    rw [lt_app_allZ hz L]

/-- The next pass start, given a tree `t` that passes `checkT` (`OffsetData.recur_next`).  For every list `ls` of blocks of at least 2, if `pre` stops, then for every
`j ≥ 2` the pass from a last block `3j` reaches a pass start with all blocks at least 2 and last block `2j + c`,
`c ≥ -1`, and `c ≥ 0` unless `ls` starts with 2. -/
theorem recur_next_of {t : TS} (ht : checkT t = true) {ls : List Nat} (hg : ∀ b ∈ ls, 2 ≤ b) {f : Nat}
    {L : List Nat} {p u : Nat}
    (e : pre f ⟨.B, 0, pad 1 ls, [0, 1]⟩ 0 = some (L, p, u)) (j : Nat) (hj : 2 ≤ j) :
    ∃ ls' n, (∀ b ∈ ls', 2 ≤ b) ∧ Reaches (K ls (3 * j - 1)) (K ls' n) ∧
      2 * j ≤ n + 1 + (if ls.headD 0 = 2 then 1 else 0) := by
  obtain ⟨a, b, M, rfl, hc, hb, ⟨g, z, rfl, hgg, hz⟩, hu⟩ := offset_bound_of ht hg e
  have hle : 2 * j ≤ a + 2 * (p + (j - u)) + (if ls.headD 0 = 2 then 1 else 0) := by
    split at hc <;> split <;> omega
  have hpos : 1 ≤ a + 2 * (p + (j - u)) := by split at hle <;> omega
  have r := recur_sound e j (by omega) (by omega) hpos
  refine ⟨(b + 2 * ((p + (j - u) + 1) / 2)) :: g, a + 2 * (p + (j - u)) - 1, ?_, ?_, by omega⟩
  · exact List.forall_mem_cons.2 ⟨by omega, hgg⟩
  · have hK : K ((b + 2 * ((p + (j - u) + 1) / 2)) :: (g ++ z)) (a + 2 * (p + (j - u)) - 1) =
        K ((b + 2 * ((p + (j - u) + 1) / 2)) :: g) (a + 2 * (p + (j - u)) - 1) := by
      unfold K
      rw [show (b + 2 * ((p + (j - u) + 1) / 2)) :: (g ++ z) = ((b + 2 * ((p + (j - u) + 1) / 2)) :: g) ++ z from rfl,
        lt_app_allZ hz]
    exact reaches_eq r hK

end BB6c
