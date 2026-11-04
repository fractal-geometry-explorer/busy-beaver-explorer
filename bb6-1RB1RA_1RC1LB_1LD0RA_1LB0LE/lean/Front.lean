import Pass

/-!
# Where a stop block of 1 can be: only at the first block, and never two front stops in a row

`halts_only_by_one` (`Pass.lean`) reduces halting to a pass whose sweep stops at a block of a single 1.  This file
narrows where that can happen, for every block list the orbit can reach.

* `Good`: every block is at least 2, except the first on the tape (the farthest from the head), which is at least 1.
  The pass map keeps it (`next_good`), so it holds on the whole orbit (`orbit_good`).  So a sweep can stop at a block
  of 1 only at the first block, after crossing every other one (`one_front`).
* `FrontStop`: the sweep of the pass crosses every block but the first and stops there (the last block odd, the
  ones between even, the first odd).  With a count of ones divisible by 4, two passes in a row are never both front
  stops (`front_twice`): both would force the last block to 3 mod 4, the blocks between to 0 mod 4 and the first to
  3 mod 4, so 2 mod 4 ones.  Every pass start of the orbit has 4n ones, so this holds on the orbit
  (`orbit_front_twice`).

Together (`halts_only_at_front`): if the machine halts from blank tape, some pass start of the orbit is
`1 0 1^e1 0 ... 0 1^b A>0` with every `e` even and `b` odd (first block a single 1, the sweep crossing all the rest),
and the pass before it did not stop at its first block.

Kernel only, no `native_decide` (`Axioms.lean`).  Lists are nearest block first, as in `Pass.lean`: the first block
on the tape is the last element.
-/

namespace BB6d

/-! ## Blocks after the first are at least 2 -/

/-- Every block is at least 2, except the farthest (the first on the tape), which is at least 1. -/
def Good : List Nat → Prop
  | [] => True
  | [y] => 0 < y
  | y :: z :: zs => 2 ≤ y ∧ Good (z :: zs)

theorem good_tail (y : Nat) (ys : List Nat) (h : Good (y :: ys)) : Good ys := by
  match ys, h with
  | [], _ => trivial
  | _ :: _, h => exact h.2

theorem good_head (y : Nat) (ys : List Nat) (h : Good (y :: ys)) : 0 < y := by
  match ys, h with
  | [], h => exact h
  | _ :: _, h => have := h.1; omega

theorem good_cons (y : Nat) (ys : List Nat) (hne : ys ≠ []) (hy : 2 ≤ y) (h : Good ys) : Good (y :: ys) := by
  match ys, hne with
  | _ :: _, _ => exact ⟨hy, h⟩

theorem bump_fst_ge (k : Nat) (ys : List Nat) : k ≤ (bump k ys).1 := by
  match ys with
  | [] => simp [bump]
  | [b] => simp [bump]
  | b :: a :: ms => simp [bump]

/-- The blocks behind the two bumped ones: nonempty, and `Good` when `ys` is. -/
theorem bump_good (k : Nat) (ys : List Nat) (hk : 1 ≤ k) (h : Good ys) :
    Good (bump k ys).2 ∧ (bump k ys).2 ≠ [] := by
  match ys with
  | [] => exact ⟨show 0 < k by omega, by simp [bump]⟩
  | [b] => exact ⟨show 0 < k by omega, by simp [bump]⟩
  | b :: a :: ms =>
    refine ⟨?_, by simp [bump]⟩
    have h' : Good (a :: ms) := h.2
    show Good ((a + k) :: ms)
    match ms, h' with
    | [], h' => show 0 < a + k; omega
    | m :: ms', h' => exact ⟨by have := h'.1; omega, h'.2⟩

theorem zag_good (gs : List Nat) : ∀ (q : Nat) (ms : List Nat),
    Good ms → ms ≠ [] → 2 ≤ lastOr q gs → Good (zag q ms gs) := by
  induction gs with
  | nil => intro q ms hm hne hq; exact good_cons q ms hne hq hm
  | cons g gs ih =>
    intro q ms hm hne hq
    exact ih g ((q + g + 2) :: ms) (good_cons _ ms hne (by omega) hm) (by simp) hq

theorem sweep_good (ys : List Nat) : ∀ (gs out : List Nat), gs ≠ [] → 2 ≤ lastOr 0 gs → Good ys →
    sweep gs ys = .ok out → Good out := by
  induction ys with
  | nil => intro gs out _ _ _ h; simp [sweep] at h
  | cons y ys ih =>
    intro gs out hne hl hg h
    have hgs : Good ys := good_tail y ys hg
    unfold sweep at h
    by_cases hy : y % 2 = 0
    · by_cases h0 : y = 0
      · rw [if_pos hy, if_pos h0] at h; cases h
      rw [if_pos hy, if_neg h0] at h
      exact ih _ out (by simp) (by rw [lastOr_cons _ _ _ hne]; exact hl) hgs h
    · rw [if_neg hy] at h
      by_cases h1 : y = 1
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      cases h
      have hb := bump_good ((y - 1) / 2) ys (by omega) hgs
      refine zag_good gs _ _ hb.1 hb.2 ?_
      match gs, hne with
      | g :: gs', _ => exact hl

/-- The pass map keeps `Good`. -/
theorem next_good (zs out : List Nat) (hg : Good zs) (h : next zs = .ok out) : Good out := by
  match zs with
  | [] => simp [next] at h; subst h; exact ⟨Nat.le_refl 2, show 0 < 2 by omega⟩
  | y :: ys =>
    have hgs : Good ys := good_tail y ys hg
    rw [next] at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy] at h
      cases h
      have hb := bump_good (y / 2 + 2) ys (by omega) hgs
      exact good_cons _ _ hb.2 (by have := bump_fst_ge (y / 2 + 2) ys; omega) hb.1
    · rw [if_neg hy] at h
      exact sweep_good ys _ out (by simp) (by simp [lastOr]; omega) hgs h

theorem orbit_good (n : Nat) (zs : List Nat) (h : orbit n = .ok zs) : Good zs := by
  induction n generalizing zs with
  | zero => simp [orbit] at h; subst h; trivial
  | succ n ih =>
    cases hn : orbit n with
    | ok ys => simp only [orbit, hn] at h; exact next_good ys zs (ih ys hn) h
    | halt => simp [orbit, hn] at h
    | one => simp [orbit, hn] at h

theorem sweep_one (ys : List Nat) : ∀ (gs : List Nat), Good ys → sweep gs ys = .one →
    ∃ es, ys = es ++ [1] ∧ ∀ e ∈ es, e % 2 = 0 := by
  induction ys with
  | nil => intro gs _ h; simp [sweep] at h
  | cons y ys ih =>
    intro gs hg h
    unfold sweep at h
    by_cases hy : y % 2 = 0
    · by_cases h0 : y = 0
      · rw [if_pos hy, if_pos h0] at h; cases h
      rw [if_pos hy, if_neg h0] at h
      obtain ⟨es, rfl, he⟩ := ih _ (good_tail y ys hg) h
      refine ⟨y :: es, rfl, ?_⟩
      intro e he'
      simp only [List.mem_cons] at he'
      rcases he' with rfl | he'
      · exact hy
      · exact he e he'
    · rw [if_neg hy] at h
      by_cases h1 : y = 1
      · subst h1
        match ys, hg with
        | [], _ => exact ⟨[], rfl, by simp⟩
        | _ :: _, hg => have := hg.1; omega
      · rw [if_neg h1] at h; cases h

/-- On a `Good` list, a sweep stops at a block of 1 only at the first block, having crossed every other block: the
last block odd and the ones between even. -/
theorem one_front (zs : List Nat) (hg : Good zs) (h : next zs = .one) :
    ∃ b es, zs = b :: (es ++ [1]) ∧ b % 2 = 1 ∧ ∀ e ∈ es, e % 2 = 0 := by
  match zs with
  | [] => simp [next] at h
  | y :: ys =>
    rw [next] at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy] at h; cases h
    · rw [if_neg hy] at h
      obtain ⟨es, rfl, he⟩ := sweep_one ys _ (good_tail y ys hg) h
      exact ⟨y, es, rfl, by omega, he⟩

/-! ## No two front stops in a row -/

/-- The sweep crosses every block but the first and stops there: the last block odd, the ones between even, the
first odd. -/
def FrontStop (zs : List Nat) : Prop :=
  ∃ b es f, zs = b :: (es ++ [f]) ∧ b % 2 = 1 ∧ (∀ e ∈ es, e % 2 = 0) ∧ f % 2 = 1

/-- The sweep across even blocks to an odd first block `f`. -/
theorem sweep_evens (f : Nat) (hf : f % 2 = 1) (es : List Nat) : ∀ (gs : List Nat), (∀ e ∈ es, e % 2 = 0 ∧ 0 < e) →
    sweep gs (es ++ [f]) =
      if f = 1 then .one else .ok (zag ((f - 1) / 2) [(f - 1) / 2] ((es.map (fun e => e / 2 - 1)).reverse ++ gs)) := by
  induction es with
  | nil =>
    intro gs _
    simp only [List.nil_append, List.map_nil, List.reverse_nil]
    unfold sweep
    rw [if_neg (by omega)]
    by_cases h1 : f = 1
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]; rfl
  | cons e es ih =>
    intro gs he
    have he0 := he e (by simp)
    simp only [List.cons_append]
    unfold sweep
    rw [if_pos he0.1, if_neg (by omega), ih _ (fun x hx => he x (by simp [hx]))]
    simp

theorem zag_app (gs : List Nat) : ∀ (q : Nat) (ms : List Nat), zag q ms gs = zag q [] gs ++ ms := by
  induction gs with
  | nil => intro q ms; rfl
  | cons g gs ih =>
    intro q ms
    show zag g ((q + g + 2) :: ms) gs = zag g [(q + g + 2)] gs ++ ms
    rw [ih g ((q + g + 2) :: ms), ih g [q + g + 2]]
    simp

theorem zag_ne_nil (gs : List Nat) : ∀ (q : Nat), zag q [] gs ≠ [] := by
  induction gs with
  | nil => intro q; simp [zag]
  | cons g gs ih => intro q; show zag g [q + g + 2] gs ≠ []; rw [zag_app]; simp

/-- The nearest block odd, the rest even. -/
def NearOdd : List Nat → Prop
  | [] => False
  | x :: rest => x % 2 = 1 ∧ ∀ r ∈ rest, r % 2 = 0

theorem nearOdd_snoc (xs : List Nat) (c : Nat) (hne : xs ≠ []) (h : NearOdd (xs ++ [c])) :
    NearOdd xs ∧ c % 2 = 0 := by
  match xs, hne with
  | x :: rest, _ =>
    simp only [List.cons_append, NearOdd] at h
    exact ⟨⟨h.1, fun r hr => h.2 r (by simp [hr])⟩, h.2 c (by simp)⟩

/-- If the zigzag's blocks are nearest odd and the rest even, every recorded `g` and the start `q` are odd. -/
theorem zag_parity (gs : List Nat) : ∀ (q : Nat), NearOdd (zag q [] gs) → q % 2 = 1 ∧ ∀ g ∈ gs, g % 2 = 1 := by
  induction gs with
  | nil => intro q h; simp only [zag, NearOdd] at h; exact ⟨h.1, by simp⟩
  | cons g gs ih =>
    intro q h
    have e : zag q [] (g :: gs) = zag g [] gs ++ [q + g + 2] := zag_app gs g [q + g + 2]
    rw [e] at h
    obtain ⟨h1, h2⟩ := nearOdd_snoc _ _ (zag_ne_nil gs g) h
    obtain ⟨hg, hgs⟩ := ih g h1
    refine ⟨by omega, ?_⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hg
    · exact hgs x hx

theorem sum_mod4 (es : List Nat) (h : ∀ e ∈ es, e % 4 = 0) : es.sum % 4 = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.sum_cons]
    have := h e (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    omega

/-- **Two front stops in a row need 2 mod 4 ones.** -/
theorem front_twice (zs out : List Nat) (h4 : zs.sum % 4 = 0) (hp : Pos zs) (hf : FrontStop zs)
    (h : next zs = .ok out) : ¬ FrontStop out := by
  obtain ⟨b, es, f, rfl, hb, he, hff⟩ := hf
  rintro ⟨b', es', f', hout, hb', he', hf'⟩
  have hpe : ∀ e ∈ es, e % 2 = 0 ∧ 0 < e := fun e hx => ⟨he e hx, hp e (by simp [hx])⟩
  rw [next, if_neg (by omega), sweep_evens f hff es _ hpe] at h
  by_cases h1 : f = 1
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  cases h
  rw [zag_app] at hout
  -- `out` is the zigzag's near part, then the far block (f - 1)/2
  have hlast := congrArg List.getLast? hout
  rw [List.getLast?_append, List.getLast?_singleton] at hlast
  simp only [List.getLast?_cons, List.getLast?_append] at hlast
  have hk : f' = (f - 1) / 2 := by
    simp at hlast
    exact hlast.symm
  subst hk
  have hnear : zag ((f - 1) / 2) [] ((es.map (fun e => e / 2 - 1)).reverse ++ [(b + 3) / 2]) = b' :: es' := by
    have := hout
    rw [← List.cons_append] at this
    exact (List.append_inj_left' this rfl)
  have hno : NearOdd (b' :: es') := ⟨hb', he'⟩
  rw [← hnear] at hno
  obtain ⟨hq, hg⟩ := zag_parity _ _ hno
  have hb4 : b % 4 = 3 := by have := hg ((b + 3) / 2) (by simp); omega
  have he4 : ∀ e ∈ es, e % 4 = 0 := by
    intro e hx
    have := hg (e / 2 - 1) (by simp; exact Or.inl ⟨e, hx, rfl⟩)
    have := hpe e hx
    omega
  have := sum_mod4 es he4
  simp only [List.sum_cons, List.sum_append, List.sum_nil] at h4
  omega

/-- On the orbit (4n ones at pass n), no two passes in a row are both front stops. -/
theorem orbit_front_twice (n : Nat) (zs out : List Nat) (h : orbit n = .ok zs) (h' : orbit (n + 1) = .ok out)
    (hf : FrontStop zs) : ¬ FrontStop out := by
  obtain ⟨hs, hp, _⟩ := orbit_ok n zs h
  simp only [orbit, h] at h'
  exact front_twice zs out (by omega) hp hf h'

/-! ## The reduction, narrowed -/

theorem orbit_one_first (m : Nat) (h : orbit m = .one) : ∃ n zs, orbit n = .ok zs ∧ next zs = .one := by
  induction m with
  | zero => simp [orbit] at h
  | succ m ih =>
    cases hm : orbit m with
    | ok zs => simp only [orbit, hm] at h; exact ⟨m, zs, hm, h⟩
    | halt => simp [orbit, hm] at h
    | one => exact ih hm

/-- **If the machine halts from blank tape**, some pass start of the closed form's orbit has a single 1 as its first
block, its sweep crosses every other block (the last odd, the rest even) and stops at that 1, and the pass before it
did not stop at its first block. -/
theorem halts_only_at_front (h : HaltsFromBlank) :
    ∃ n b es, orbit (n + 1) = .ok (b :: (es ++ [1])) ∧ b % 2 = 1 ∧ (∀ e ∈ es, e % 2 = 0) ∧
      next (b :: (es ++ [1])) = .one ∧ ∃ zs, orbit n = .ok zs ∧ ¬ FrontStop zs := by
  obtain ⟨m, hm⟩ := halts_only_by_one h
  obtain ⟨n, zs, hn, hz⟩ := orbit_one_first m hm
  obtain ⟨b, es, rfl, hb, he⟩ := one_front zs (orbit_good n _ hn) hz
  match n, hn with
  | 0, hn => simp [orbit] at hn
  | n + 1, hn =>
    cases hp : orbit n with
    | ok ws =>
      refine ⟨n, b, es, hn, hb, he, hz, ws, hp, fun hw => ?_⟩
      exact orbit_front_twice n ws _ hp hn hw ⟨b, es, 1, rfl, hb, he, rfl⟩
    | halt => simp [orbit, hp] at hn
    | one => simp [orbit, hp] at hn

end BB6d
