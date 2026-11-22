import Sweep

/-!
# 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA: the machine halts iff a block of 3 meets a block of 8

`Sweep.lean` says that the machine halts iff some sweep starts on a bad right list: a first block of 3 cells
followed by more, or a block of exactly one cell before the end.  This file shows that such a list is made by
one local event, and so turns a question about whole block lists into a question about two neighbouring blocks.

**`halts_iff_8`** (kernel only): the machine halts from blank tape iff the block map reaches a frame
`E L (3 :: 0 :: j :: R)` with `hd L = 8` (and `j ≥ 1`, which always holds): a zigzag has cut the block next to
the head down to exactly 3 cells, and the block on its left has exactly 8.  From there (`pat_halts`) the 3 cells
join the 8 into a block of 10, the next zigzag cuts it to 7 and 4 while the block behind it grows from 1 to 3,
and the sweep that follows starts on that block of 3: 11 frames to the critical frame `0 1 1 C> 0 1`.

In terms of the zigzag of `Series.lean` (`zig`): a block of `m` cells with `i` cells on its left reaches the
pattern iff `m ≡ 0 (mod 3)` and `i + 2m/3 = 10`, the pairs (i, m) = (8, 3), (6, 6), (4, 9), (2, 12), and (0, 15)
at the left end of the tape (`halts_of_15`, `critical_mid`).

How:

* `Inv4`, an invariant kept by every frame that is not a pattern frame (`inv4_next`): every block is at least 2
  cells except the head's neighbours and the last block on the right (which may be 1), and the block just behind
  the zigzag (the "accumulator" `j` of `E L (m :: 0 :: j :: R)`) is safe: from `(m, j)` the zigzag does not end
  with a block of 4 against an accumulator of 3, and does not leave an accumulator of 1 behind (`S`).  The
  conditions on B frames and on C frames in the middle of a trip or a sweep say the same one or two frames ahead.
* `inv4_total`: no frame satisfying `Inv4` is critical.  Frame 4 of the run satisfies it (`inv4_frame4`).
* The only frames whose successor breaks `Inv4` are `Pat`: the pattern above, or a block of 3 cut next to a
  leftmost block of 3 (`halts_iff_pat`).  `LM`, `lm_next`: the leftmost block of the tape is never a block of 3,
  so only the first kind occurs.
-/

namespace H15414

open TM

/-! ## Lists of blocks of at least two cells -/

/-- Every block has at least 2 cells (trailing empty blocks stand for blank tape). -/
def G2 : List Nat → Prop
  | [] => True
  | x :: l => (2 ≤ x ∧ G2 l) ∨ Z (x :: l)

/-- Every block has at least 2 cells, except that the last non-empty block may have 1. -/
def W : List Nat → Prop
  | [] => True
  | x :: l => (2 ≤ x ∧ W l) ∨ (x = 1 ∧ Z l) ∨ Z (x :: l)

theorem Z_nil : Z [] := fun _ h => by simp at h

theorem Z_hd : ∀ l : List Nat, Z l → hd l = 0
  | [], _ => rfl
  | x :: _, h => h x (List.mem_cons_self ..)

theorem Z_tl : ∀ l : List Nat, Z l → Z (tl l)
  | [], _ => Z_nil
  | _ :: _, h => Z_tail h

theorem Z_hd_tl (l : List Nat) (h : Z l) : Z (hd l :: tl l) := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact Z_hd l h
  · exact Z_tl l h y hy

theorem Z_W (l : List Nat) (h : Z l) : W l := by
  cases l with
  | nil => trivial
  | cons x l => exact Or.inr (Or.inr h)

theorem Z_G2 (l : List Nat) (h : Z l) : G2 l := by
  cases l with
  | nil => trivial
  | cons x l => exact Or.inr h

theorem Z_cons {x : Nat} {l : List Nat} (hx : x = 0) (hl : Z l) : Z (x :: l) := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hl y hy

theorem G2_tl : ∀ l : List Nat, G2 l → G2 (tl l)
  | [], _ => trivial
  | _ :: l, h => by
    rcases h with ⟨_, h⟩ | h
    · exact h
    · exact Z_G2 l (Z_tail h)

theorem G2_hd : ∀ l : List Nat, G2 l → hd l = 0 ∨ 2 ≤ hd l
  | [], _ => Or.inl rfl
  | x :: _, h => by
    rcases h with ⟨hx, _⟩ | h
    · exact Or.inr hx
    · exact Or.inl (h x (List.mem_cons_self ..))

/-- In a `G2` list an empty first block means blank tape. -/
theorem G2_hd_zero : ∀ l : List Nat, G2 l → hd l = 0 → Z l
  | [], _, _ => Z_nil
  | x :: _, h, h0 => by
    rcases h with ⟨hx, _⟩ | h
    · simp [hd] at h0; omega
    · exact h

theorem G2_hd_tl (l : List Nat) (h : G2 l) : G2 (hd l :: tl l) := by
  cases l with
  | nil => exact Or.inr (Z_cons rfl Z_nil)
  | cons x l => exact h

theorem G2_cons {x : Nat} {l : List Nat} (hx : 2 ≤ x) (hl : G2 l) : G2 (x :: l) := Or.inl ⟨hx, hl⟩

theorem W_tl : ∀ l : List Nat, W l → W (tl l)
  | [], _ => trivial
  | _ :: l, h => by
    rcases h with ⟨_, h⟩ | ⟨_, h⟩ | h
    · exact h
    · exact Z_W l h
    · exact Z_W l (Z_tail h)

theorem W_hd_tl (l : List Nat) (h : W l) : W (hd l :: tl l) := by
  cases l with
  | nil => exact Or.inr (Or.inr (Z_cons rfl Z_nil))
  | cons x l => exact h

/-- The first block of a `W` list: empty (then blank tape), one cell (then the last block), or at least 2. -/
theorem W_cases : ∀ l : List Nat, W l → Z l ∨ (hd l = 1 ∧ Z (tl l)) ∨ 2 ≤ hd l
  | [], _ => Or.inl Z_nil
  | x :: l, h => by
    rcases h with ⟨hx, _⟩ | ⟨hx, h⟩ | h
    · exact Or.inr (Or.inr hx)
    · exact Or.inr (Or.inl ⟨hx, h⟩)
    · exact Or.inl h

theorem W_cons {x : Nat} {l : List Nat} (hx : 1 ≤ x) (hl : W l) (h1 : x = 1 → Z l) : W (x :: l) := by
  by_cases h : x = 1
  · exact Or.inr (Or.inl ⟨h, h1 h⟩)
  · exact Or.inl ⟨by omega, hl⟩

/-! ## The accumulator -/

/-- The zigzag on a block of `m` cells, with `i` cells on its left and the accumulator `j` behind it, does not end
with a block of 4 against an accumulator of 3, and does not leave an accumulator of 1 behind. -/
def S (i m j : Nat) : Prop :=
  (j = 3 → m ≠ 4) ∧ (j = 2 → m ≠ 7 ∧ (m = 2 → i ≠ 2)) ∧
  (j = 1 → m ≠ 10 ∧ m ≠ 3 ∧ (m = 5 → i ≠ 0) ∧ (m = 2 → i ≠ 5))

/-- `S`, or the accumulator is the last block (nothing behind it). -/
def Sacc (L : List Nat) (m j : Nat) (R : List Nat) : Prop := Z R ∨ S (hd L) m j

/-- The B frame `B (a :: L) R`. -/
def InvB (a : Nat) (L R : List Nat) : Prop :=
  5 ≤ a ∧ G2 L ∧ W (tl R) ∧ (hd R = 0 → Z R) ∧ (hd R = 3 → Z (tl R)) ∧
  (hd R = 2 → Sacc L a (hd (tl R) + 1) (tl (tl R)))

/-- `C (c :: b :: L) (0 :: j :: R)`: in the middle of a trip of the zigzag. -/
def TripC (c b : Nat) (L : List Nat) (j : Nat) (R : List Nat) : Prop :=
  match c with
  | 0 => Sacc L b (j + 1) R
  | 1 => (2 ≤ j ∨ Z R) ∧ S (hd L) b 1
  | 2 => InvB (b + 5) L (j :: R)
  | c + 3 => Sacc (b :: L) (c + 2) (j + 1) R

/-- `C (c :: b :: L) R`: sweeping right (or turning round). -/
def SweepC (c b : Nat) (L R : List Nat) : Prop :=
  W (tl R) ∧
  match c with
  | 1 => Sacc L b (hd R + 1) (tl R)
  | 2 => Z R
  | _ => W R

/-- The invariant. -/
def Inv4 : Ph → Prop
  | .E L R => ∃ m j R', R = m :: 0 :: j :: R' ∧ G2 L ∧ 2 ≤ m ∧ 1 ≤ j ∧ W R' ∧ Sacc L m j R'
  | .C L R => ∃ c b L', L = c :: b :: L' ∧ 2 ≤ b ∧ G2 L' ∧
      ((∃ j R', R = 0 :: j :: R' ∧ 1 ≤ j ∧ W R' ∧ TripC c b L' j R') ∨ SweepC c b L' R)
  | .B L R => ∃ a L', L = a :: L' ∧ InvB a L' R
  | .F _ _ => False

/-- The pattern frames: the zigzag has left 3 cells, with a block of 8 on the left, or with a block of 3 that is the
leftmost block of the tape. -/
def Pat : Ph → Prop
  | .E L R => (∃ j R', R = 3 :: 0 :: j :: R' ∧ 1 ≤ j) ∧ (hd L = 8 ∨ (hd L = 3 ∧ Z (tl L)))
  | _ => False

/-! ## The invariant is kept -/

theorem inv4_E (L R : List Nat) (p' : Ph) (hi : Inv4 (.E L R)) (hp : ¬ Pat (.E L R))
    (h : next (.E L R) = some p') : Inv4 p' := by
  obtain ⟨m, j, R', rfl, hL, hm, hj, hR', hS⟩ := hi
  simp only [next, hd_cons, tl_cons] at h
  have hL0 := G2_hd L hL
  match m, hm, h with
  | 2, _, h =>
    simp only [nextE, Option.some.injEq] at h; subst h
    refine ⟨0, hd L + 2, tl L, rfl, by omega, G2_tl L hL, Or.inl ⟨j, R', rfl, hj, hR', ?_⟩⟩
    show Sacc (tl L) (hd L + 2) (j + 1) R'
    rcases hS with hz | ⟨h3, h2, h1⟩
    · exact Or.inl hz
    · refine Or.inr ⟨fun hj3 => ?_, fun hj2 => ?_, fun hj1 => by omega⟩
      · have := (h2 (by omega)).2 rfl; omega
      · refine ⟨by have := (h1 (by omega)).2.2.2 rfl; omega, fun he => ?_⟩
        have hz := G2_hd_zero L hL (by omega)
        rw [Z_hd _ (Z_tl L hz)]; omega
  | 3, _, h =>
    simp only [nextE, Option.some.injEq] at h; subst h
    refine ⟨1, hd L + 2, tl L, rfl, by omega, G2_tl L hL, Or.inl ⟨j, R', rfl, hj, hR', ?_⟩⟩
    show (2 ≤ j ∨ Z R') ∧ S (hd (tl L)) (hd L + 2) 1
    refine ⟨?_, fun h3 => by omega, fun h2 => by omega, fun _ => ⟨?_, ?_, fun h5 => ?_, fun h2 => ?_⟩⟩
    · rcases hS with hz | ⟨_, _, h1⟩
      · exact Or.inr hz
      · by_cases hj1 : j = 1
        · exact absurd rfl (h1 hj1).2.1
        · exact Or.inl (by omega)
    · intro h8; exact hp ⟨⟨j, R', rfl, hj⟩, Or.inl (by omega)⟩
    · omega
    · intro h0
      exact hp ⟨⟨j, R', rfl, hj⟩, Or.inr ⟨by omega, G2_hd_zero (tl L) (G2_tl L hL) h0⟩⟩
    · have hz := G2_hd_zero L hL (by omega)
      rw [Z_hd _ (Z_tl L hz)]; omega
  | 4, _, h =>
    simp only [nextE, Option.some.injEq] at h; subst h
    refine ⟨2, hd L + 2, tl L, rfl, by omega, G2_tl L hL, Or.inl ⟨j, R', rfl, hj, hR', ?_⟩⟩
    show InvB (hd L + 2 + 5) (tl L) (j :: R')
    refine ⟨by omega, G2_tl L hL, hR', fun h0 => by simp [hd] at h0; omega, fun h3 => ?_, fun h2 => ?_⟩
    · simp only [hd] at h3
      rcases hS with hz | ⟨h3', _, _⟩
      · exact hz
      · exact absurd rfl (h3' h3)
    · show Z (tl R') ∨ S (hd (tl L)) (hd L + 2 + 5) (hd R' + 1)
      rcases W_cases R' hR' with hz | ⟨_, hz⟩ | h2'
      · exact Or.inl (Z_tl R' hz)
      · exact Or.inl hz
      · exact Or.inr ⟨fun _ => by omega, fun _ => by omega, fun _ => by omega⟩
  | m + 5, _, h =>
    simp only [nextE, Option.some.injEq] at h; subst h
    refine ⟨m + 3, hd L + 2, tl L, rfl, by omega, G2_tl L hL, Or.inl ⟨j, R', rfl, hj, hR', ?_⟩⟩
    show Sacc ((hd L + 2) :: tl L) (m + 2) (j + 1) R'
    rcases hS with hz | ⟨h3, h2, h1⟩
    · exact Or.inl hz
    · refine Or.inr ⟨fun hj3 => ?_, fun hj2 => ⟨?_, fun he => ?_⟩, fun hj1 => by omega⟩
      · have := (h2 (by omega)).1; omega
      · have := (h1 (by omega)).1; omega
      · have := (h1 (by omega)).2.2.1 (by omega); show hd L + 2 ≠ 2; omega

theorem inv4_C (L R : List Nat) (p' : Ph) (hi : Inv4 (.C L R)) (h : next (.C L R) = some p') : Inv4 p' := by
  obtain ⟨c, b, L', rfl, hb, hL', hR⟩ := hi
  simp only [next, hd_cons, tl_cons] at h
  rcases hR with ⟨j, R', rfl, hj, hR', ht⟩ | ⟨hW, hs⟩
  · -- in the middle of a trip
    simp only [hd_cons, tl_cons] at h
    match c, h, ht with
    | 0, h, ht =>
      simp only [nextC, Option.some.injEq] at h; subst h
      exact ⟨1, b, L', rfl, hb, hL', Or.inr ⟨hR', ht⟩⟩
    | 1, h, ⟨hj2, hS⟩ =>
      simp only [nextC, Option.some.injEq] at h; subst h
      refine ⟨b, 1, j :: R', rfl, hL', hb, by omega, ?_, Or.inr hS⟩
      rcases hj2 with hj2 | hz
      · exact Or.inl ⟨hj2, hR'⟩
      · exact W_cons hj hR' (fun _ => hz)
    | 2, h, ht =>
      simp only [nextC, Option.some.injEq] at h; subst h
      exact ⟨b + 5, L', rfl, ht⟩
    | c + 3, h, ht =>
      simp only [nextC, Option.some.injEq] at h; subst h
      exact ⟨1, c + 2, b :: L', rfl, by omega, G2_cons hb hL', Or.inr ⟨hR', ht⟩⟩
  · -- sweeping
    have key : ∀ c', (c' = 1 → Sacc L' b (hd R + 1) (tl R)) → c' ≠ 1 → W R →
        SweepC (hd R + 1) c' L' (tl R) ∧ True := by
      intro _ _ _ hWR
      refine ⟨⟨W_tl _ hW, ?_⟩, trivial⟩
      rcases W_cases R hWR with hz | ⟨h1, hz⟩ | h2
      · rw [Z_hd R hz]; exact Or.inl (Z_tl _ (Z_tl R hz))
      · rw [h1]; exact hz
      · obtain ⟨r, hr⟩ : ∃ r, hd R = r + 2 := ⟨hd R - 2, by omega⟩
        rw [hr]; exact W_tl R hWR
    match c, h, hs with
    | 0, h, hs =>
      simp only [nextC, Option.some.injEq] at h; subst h
      refine ⟨hd R + 1, b, L', rfl, hb, hL', Or.inr ?_⟩
      have hWR : W R := hs
      refine ⟨W_tl _ hW, ?_⟩
      rcases W_cases R hWR with hz | ⟨h1, hz⟩ | h2
      · rw [Z_hd R hz]; exact Or.inl (Z_tl _ (Z_tl R hz))
      · rw [h1]; exact hz
      · obtain ⟨r, hr⟩ : ∃ r, hd R = r + 2 := ⟨hd R - 2, by omega⟩
        rw [hr]; exact W_tl R hWR
    | 1, h, hs =>
      simp only [nextC, Option.some.injEq] at h; subst h
      exact ⟨b, hd R + 1, tl R, rfl, hL', hb, by omega, hW, hs⟩
    | 2, h, hs =>
      have hz : Z R := hs
      rw [Z_hd R hz] at h
      simp only [nextC, Option.some.injEq] at h; subst h
      have hz' := Z_tl R hz
      refine ⟨b + 5, L', rfl, by omega, hL', W_tl _ (Z_W _ hz'), fun _ => hz', fun h3 => ?_, fun h2 => ?_⟩
      · rw [Z_hd _ hz'] at h3; omega
      · rw [Z_hd _ hz'] at h2; omega
    | c + 3, h, hs =>
      simp only [nextC, Option.some.injEq] at h; subst h
      refine ⟨hd R + 1, c + 2, b :: L', rfl, by omega, G2_cons hb hL', Or.inr ?_⟩
      have hWR : W R := hs
      refine ⟨W_tl _ hW, ?_⟩
      rcases W_cases R hWR with hz | ⟨h1, hz⟩ | h2
      · rw [Z_hd R hz]; exact Or.inl (Z_tl _ (Z_tl R hz))
      · rw [h1]; exact hz
      · obtain ⟨r, hr⟩ : ∃ r, hd R = r + 2 := ⟨hd R - 2, by omega⟩
        rw [hr]; exact W_tl R hWR

theorem inv4_B (L R : List Nat) (p' : Ph) (hi : Inv4 (.B L R)) (h : next (.B L R) = some p') : Inv4 p' := by
  obtain ⟨a, L', rfl, ha, hL', hW, h0, h3, h2⟩ := hi
  simp only [next, hd_cons, tl_cons] at h
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 5 := ⟨a - 5, by omega⟩
  have hL2 := G2_hd_tl L' hL'
  generalize hr : hd R = r at h h0 h3 h2
  match r, h with
  | 0, h =>
    have hz := h0 rfl
    rw [Z_hd _ (Z_tl R hz)] at h
    simp only [nextB, Option.some.injEq] at h; subst h
    refine ⟨0, a + 5, hd L' :: tl L', rfl, by omega, hL2, Or.inr ⟨?_, ?_⟩⟩
    · exact Z_W _ (Z_tl _ (Z_tl _ (Z_tl R hz)))
    · exact Z_W _ (Z_tl _ (Z_tl R hz))
  | r + 1, h =>
    simp only [nextB, Option.some.injEq] at h; subst h
    refine ⟨r, a + 5, hd L' :: tl L', rfl, by omega, hL2, Or.inr ⟨?_, ?_⟩⟩
    · show W (tl (tl R)); exact W_tl _ hW
    · match r with
      | 0 => exact W_hd_tl _ hW
      | 1 => show Sacc (hd L' :: tl L') (a + 5) (hd (tl R) + 1) (tl (tl R)); exact h2 rfl
      | 2 => exact Z_hd_tl _ (h3 rfl)
      | _ + 3 => exact W_hd_tl _ hW

/-- **`Inv4` is kept by every frame that is not a pattern frame.** -/
theorem inv4_next : ∀ p p', Inv4 p → ¬ Pat p → next p = some p' → Inv4 p'
  | .E L R, p', hi, hp, h => inv4_E L R p' hi hp h
  | .C L R, p', hi, _, h => inv4_C L R p' hi h
  | .B L R, p', hi, _, h => inv4_B L R p' hi h
  | .F _ _, _, hi, _, _ => hi.elim

/-- **No frame satisfying `Inv4` is a critical frame.** -/
theorem inv4_total : ∀ p, Inv4 p → ∃ p', next p = some p'
  | .E L R, ⟨m, j, R', hR, _, hm, _⟩ => by
    subst hR
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    exact ⟨_, rfl⟩
  | .C L R, ⟨c, b, L', hL, _, _, hR⟩ => by
    subst hL
    simp only [next, hd_cons, tl_cons]
    match c with
    | 0 => exact ⟨_, rfl⟩
    | 1 => exact ⟨_, rfl⟩
    | c + 3 => exact ⟨_, rfl⟩
    | 2 =>
      have h0 : hd R = 0 := by
        rcases hR with ⟨j, R', rfl, _⟩ | ⟨_, hz⟩
        · rfl
        · exact Z_hd R hz
      rw [h0]; exact ⟨_, rfl⟩
  | .B L R, ⟨a, L', hL, ha, _, _, _, h3, _⟩ => by
    subst hL
    simp only [next, hd_cons, tl_cons]
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
    generalize hd R = r
    match r with
    | 0 => exact ⟨_, rfl⟩
    | r + 1 => exact ⟨_, rfl⟩
  | .F _ _, hi => hi.elim

/-! ## The run -/

theorem frame4 : iterF next 4 start = some (.C [0, 2] [1]) := rfl

theorem inv4_frame4 : Inv4 (.C [0, 2] [1]) :=
  ⟨0, 2, [], rfl, by omega, trivial, Or.inr ⟨trivial, Or.inr (Or.inl ⟨rfl, Z_nil⟩)⟩⟩

/-- From a pattern frame the block map reaches a critical frame. -/
theorem pat_halts (L R : List Nat) (hp : Pat (.E L R)) :
    ∃ k p, iterF next k (.E L R) = some p ∧ Critical p := by
  obtain ⟨⟨j, R, rfl, hj⟩, h8 | ⟨h3', hz⟩⟩ := hp
  · match L, h8 with
    | 8 :: L, _ =>
      exact ⟨11, .C (2 :: (hd L + 11) :: hd (tl L) :: tl (tl L)) (j :: R), rfl,
        by show (2:Nat) = 2 ∧ 1 ≤ j; omega⟩
  · match L, h3' with
    | 3 :: L, _ =>
      have hz : Z L := hz
      have e1 := Z_hd _ hz
      have e2 := Z_hd _ (Z_tl _ hz)
      have e3 := Z_hd _ (Z_tl _ (Z_tl _ hz))
      refine ⟨11, .C (2 :: 7 :: 0 :: tl (tl (tl L))) (j :: R), ?_,
        by show (2:Nat) = 2 ∧ 1 ≤ j; omega⟩
      simp only [iterF, next, nextE, nextC, nextB, hd_cons, tl_cons, e1, e2, e3, Option.bind_some]

/-- **The machine halts from blank tape iff the block map, from `B [1] []`, reaches a pattern frame**: the zigzag
leaves a block of exactly 3 cells next to a block of exactly 8 on its left, or next to a leftmost block of 3. -/
theorem halts_iff_pat : HaltsFromBlank ↔ ∃ k p, iterF next k start = some p ∧ Pat p := by
  constructor
  · intro hh
    obtain ⟨k, p, hk, hn⟩ := (halts_iff).1 hh
    refine Classical.byContradiction fun hno => ?_
    let Good : Ph → Prop := fun p => Inv4 p ∧ ∃ j, iterF next j start = some p
    have good : ∀ p p', Good p → next p = some p' → Good p' := by
      rintro p p' ⟨hi, j, hj⟩ hn'
      refine ⟨inv4_next p p' hi (fun hp => hno ⟨j, p, hj, hp⟩) hn', j + 1, ?_⟩
      rw [iterF_succ next j start p hj, hn']
    have g4 : Good (.C [0, 2] [1]) := ⟨inv4_frame4, 4, frame4⟩
    by_cases hk4 : k < 4
    · have : ∃ q, iterF next (k + 1) start = some q := by
        match k, hk4 with
        | 0, _ => exact ⟨_, rfl⟩
        | 1, _ => exact ⟨_, rfl⟩
        | 2, _ => exact ⟨_, rfl⟩
        | 3, _ => exact ⟨_, rfl⟩
      obtain ⟨q, hq⟩ := this
      rw [iterF_succ next k start p hk, hn] at hq; cases hq
    · obtain ⟨n, rfl⟩ : ∃ n, k = 4 + n := ⟨k - 4, by omega⟩
      rw [iterF_add_some next 4 start _ frame4 n] at hk
      obtain ⟨hi, _⟩ := iterF_good next Good good n _ p g4 hk
      obtain ⟨p', hp'⟩ := inv4_total p hi
      rw [hn] at hp'; cases hp'
  · rintro ⟨k, p, hk, hp⟩
    match p, hp with
    | .E L R, hp =>
      obtain ⟨n, q, hq, hc⟩ := pat_halts L R hp
      refine (halts_iff_critical).2 ⟨k + n, q, ?_, hc⟩
      rw [iterF_add_some next k start _ hk n]; exact hq

/-! ## The leftmost block is never 3

So the second kind of pattern frame (a leftmost block of 3) never occurs, and halting is one event. -/

/-- The leftmost non-empty block of the list is not a block of 3 (trailing empty blocks are blank tape). -/
def NL3 : List Nat → Prop
  | [] => True
  | x :: l => (Z l → x ≠ 3) ∧ NL3 l

theorem NL3_tl : ∀ l : List Nat, NL3 l → NL3 (tl l)
  | [], _ => trivial
  | _ :: _, h => h.2

theorem NL3_hd_tl (l : List Nat) (h : NL3 l) : NL3 (hd l :: tl l) := by
  cases l with
  | nil => exact ⟨fun _ => by simp [hd], trivial⟩
  | cons x l => exact h

theorem NL3_push {x : Nat} {l : List Nat} (hx : x ≠ 3) (hl : NL3 l) : NL3 (x :: l) := ⟨fun _ => hx, hl⟩

/-- Where the leftmost block of the tape is, in each kind of frame. -/
def LM : Ph → Prop
  | .E L _ => NL3 L
  | .C L _ => NL3 (tl L)
  | .B L _ => NL3 L
  | .F _ _ => True

theorem lm_next (p p' : Ph) (hi : Inv4 p) (hl : LM p) (h : next p = some p') : LM p' := by
  match p, hi, hl with
  | .E L R, ⟨m, j, R', hR, hL, hm, _⟩, hl =>
    subst hR
    have hL0 := G2_hd L hL
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    simp only [next, hd_cons, tl_cons, nextE, Option.some.injEq] at h; subst h
    exact NL3_push (by omega) (NL3_tl L hl)
  | .C L R, ⟨c, b, L', hL, hb, _, hR⟩, hl =>
    subst hL
    have hl : NL3 (b :: L') := hl
    simp only [next, hd_cons, tl_cons] at h
    match c with
    | 0 => simp only [nextC, Option.some.injEq] at h; subst h; exact hl
    | 1 => simp only [nextC, Option.some.injEq] at h; subst h; exact hl.2
    | 2 =>
      generalize hd R = r at h
      match r with
      | 0 => simp only [nextC, Option.some.injEq] at h; subst h; exact NL3_push (by omega) hl.2
      | _ + 1 => simp [nextC] at h
    | c + 3 =>
      simp only [nextC, Option.some.injEq] at h; subst h
      exact ⟨fun hz => absurd (Z_hd _ hz) (by simp [hd]; omega), hl⟩
  | .B L R, ⟨a, L', hL, ha, _⟩, hl =>
    subst hL
    simp only [next, hd_cons, tl_cons] at h
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 5 := ⟨a - 5, by omega⟩
    generalize hd R = r at h
    match r with
    | 0 =>
      simp only [nextB, Option.some.injEq] at h; subst h
      exact NL3_push (by omega) (NL3_hd_tl _ hl.2)
    | _ + 1 =>
      simp only [nextB, Option.some.injEq] at h; subst h
      exact NL3_push (by omega) (NL3_hd_tl _ hl.2)
  | .F _ _, hi, _ => exact hi.elim

theorem lm_frame4 : LM (.C [0, 2] [1]) := ⟨fun _ => by omega, trivial⟩

/-- The pattern frame that can occur: the zigzag leaves 3 cells with a block of exactly 8 on its left. -/
def Pat8 : Ph → Prop
  | .E L R => (∃ j R', R = 3 :: 0 :: j :: R' ∧ 1 ≤ j) ∧ hd L = 8
  | _ => False

theorem pat_of_lm (p : Ph) (hl : LM p) (hp : Pat p) : Pat8 p := by
  match p, hp with
  | .E L R, ⟨hR, h⟩ =>
    rcases h with h8 | ⟨h3, hz⟩
    · exact ⟨hR, h8⟩
    · exfalso
      match L, hl with
      | [], _ => simp [hd] at h3
      | x :: l, hl => exact hl.1 hz h3

/-- **The machine halts from blank tape iff the block map reaches a frame `E L (3 :: 0 :: j :: R)` with `hd L = 8`**
(and `j ≥ 1`): a zigzag that ends with a block of exactly 3 cells next to a block of exactly 8 on its left. -/
theorem halts_iff_8 : HaltsFromBlank ↔ ∃ k p, iterF next k start = some p ∧ Pat8 p := by
  constructor
  · intro hh
    obtain ⟨k, p, hk, hn⟩ := (halts_iff).1 hh
    refine Classical.byContradiction fun hno => ?_
    let Good : Ph → Prop := fun p => Inv4 p ∧ LM p ∧ ∃ j, iterF next j start = some p
    have good : ∀ p p', Good p → next p = some p' → Good p' := by
      rintro p p' ⟨hi, hl, j, hj⟩ hn'
      refine ⟨inv4_next p p' hi (fun hp => hno ⟨j, p, hj, pat_of_lm p hl hp⟩) hn', lm_next p p' hi hl hn',
        j + 1, ?_⟩
      rw [iterF_succ next j start p hj, hn']
    have g4 : Good (.C [0, 2] [1]) := ⟨inv4_frame4, lm_frame4, 4, frame4⟩
    by_cases hk4 : k < 4
    · have : ∃ q, iterF next (k + 1) start = some q := by
        match k, hk4 with
        | 0, _ => exact ⟨_, rfl⟩
        | 1, _ => exact ⟨_, rfl⟩
        | 2, _ => exact ⟨_, rfl⟩
        | 3, _ => exact ⟨_, rfl⟩
      obtain ⟨q, hq⟩ := this
      rw [iterF_succ next k start p hk, hn] at hq; cases hq
    · obtain ⟨n, rfl⟩ : ∃ n, k = 4 + n := ⟨k - 4, by omega⟩
      rw [iterF_add_some next 4 start _ frame4 n] at hk
      obtain ⟨hi, _⟩ := iterF_good next Good good n _ p g4 hk
      obtain ⟨p', hp'⟩ := inv4_total p hi
      rw [hn] at hp'; cases hp'
  · rintro ⟨k, p, hk, hp⟩
    match p, hp with
    | .E L R, ⟨hR, h8⟩ => exact (halts_iff_pat).2 ⟨k, .E L R, hk, hR, Or.inl h8⟩

end H15414
