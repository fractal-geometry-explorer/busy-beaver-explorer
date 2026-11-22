import Blocks

/-!
# 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA: an invariant of the block map

`halts_iff_critical` (`Blocks.lean`) reduces halting to the block map reaching one of three critical frames.
This file proves an invariant `Inv` of every frame after the first one, and with it that two of the three
critical frames are never reached and that the third can only be reached from a B or C frame, never from an E
frame:

* E frames: no empty block on the left, and on the right exactly one empty block, right after the first block
  (`E L (m :: 0 :: R')` with `m ≥ 1`): the tape is `blk(L) E> 0 1^m 0 0 blk(R')`.
* C frames: the left list has at least two blocks, the second one not empty, no empty block further out; on the
  right an empty block can only be the first one.
* B frames: the block left of the head has at least five 1s, and there is no empty block anywhere.
* F frames: never reached.

"No empty block" allows the list to end in empty blocks (`NZ`): they stand for blank tape, and `next` can append
such a block when it reads past the end of a list.

Consequences (kernel only, no `native_decide` here):

* `no_B_F_critical`: no frame of the run is a critical B frame (`0 1 B> 1 1 1`) or a critical F frame (`F> 1 1`).
* `halts_iff_C`: **the machine halts from blank tape iff the block map reaches `C (2 :: L) (r + 1 :: R)`**
  (`0 1 1 C> 0 1`).
* `critical_after_BC`: a critical frame of the run is never the successor of an E frame; the frame before it is a
  B or C frame (the head moving right).
-/

namespace H15414

open TM

/-- Every entry is 0: the list stands for blank tape. -/
def Z (l : List Nat) : Prop := ∀ x ∈ l, x = 0

/-- No empty block, except that the list may end in empty blocks (which stand for blank tape). -/
def NZ : List Nat → Prop
  | [] => True
  | x :: l => (1 ≤ x ∧ NZ l) ∨ Z (x :: l)

theorem Z_NZ : ∀ l : List Nat, Z l → NZ l
  | [], _ => trivial
  | _ :: _, h => Or.inr h

theorem Z_tail {x : Nat} {l : List Nat} (h : Z (x :: l)) : Z l :=
  fun y hy => h y (List.mem_cons_of_mem x hy)

theorem NZ_tl : ∀ l : List Nat, NZ l → NZ (tl l)
  | [], _ => trivial
  | _ :: l, h => by
    rcases h with ⟨_, h⟩ | h
    · exact h
    · exact Z_NZ l (Z_tail h)

theorem NZ_cons {x : Nat} {l : List Nat} (hx : 1 ≤ x) (hl : NZ l) : NZ (x :: l) := Or.inl ⟨hx, hl⟩

theorem NZ_hd_tl : ∀ l : List Nat, NZ l → NZ (hd l :: tl l)
  | [], _ => Or.inr (fun y hy => by simp [hd, tl] at hy; exact hy)
  | _ :: _, h => h

theorem hd_cons (a : Nat) (l : List Nat) : hd (a :: l) = a := rfl
theorem tl_cons (a : Nat) (l : List Nat) : tl (a :: l) = l := rfl

/-- The invariant of every frame after the first. -/
def Inv : Ph → Prop
  | .E L R => NZ L ∧ ∃ m R', R = m :: 0 :: R' ∧ 1 ≤ m ∧ NZ R'
  | .C L R => ∃ a b L', L = a :: b :: L' ∧ 1 ≤ b ∧ NZ L' ∧ NZ (tl R)
  | .B L R => 5 ≤ hd L ∧ NZ (tl L) ∧ NZ R
  | .F _ _ => False

theorem inv_E (L R : List Nat) (p' : Ph) (hi : Inv (.E L R)) (h : next (.E L R) = some p') : Inv p' := by
  obtain ⟨hL, m, R', rfl, hm, hR'⟩ := hi
  simp only [next, hd_cons, tl_cons] at h
  match m, hm, h with
  | 1, _, h =>
    simp only [nextE, Option.some.injEq] at h; subst h
    exact ⟨0, hd L + 2, tl L, rfl, by omega, NZ_tl L hL, NZ_tl R' hR'⟩
  | m + 2, _, h =>
    simp only [nextE, Option.some.injEq] at h; subst h
    exact ⟨m, hd L + 2, tl L, rfl, by omega, NZ_tl L hL, hR'⟩

theorem inv_C (L R : List Nat) (p' : Ph) (hi : Inv (.C L R)) (h : next (.C L R) = some p') : Inv p' := by
  obtain ⟨a, b, L', rfl, hb, hL', hR⟩ := hi
  simp only [next, hd_cons, tl_cons] at h
  generalize hr : hd R = r at h
  match a, h with
  | 0, h =>
    simp only [nextC, Option.some.injEq] at h; subst h
    exact ⟨_, b, L', rfl, hb, hL', NZ_tl _ hR⟩
  | 1, h =>
    simp only [nextC, Option.some.injEq] at h; subst h
    exact ⟨hL', b, _ :: _, rfl, hb, NZ_cons (by omega) hR⟩
  | 2, h =>
    match r, h with
    | 0, h =>
      simp only [nextC, Option.some.injEq] at h; subst h
      exact ⟨by simp only [hd]; omega, hL', hR⟩
    | _ + 1, h => simp [nextC] at h
  | a + 3, h =>
    simp only [nextC, Option.some.injEq] at h; subst h
    exact ⟨_, a + 2, b :: L', rfl, by omega, NZ_cons hb hL', NZ_tl _ hR⟩

theorem inv_B (L R : List Nat) (p' : Ph) (hi : Inv (.B L R)) (h : next (.B L R) = some p') : Inv p' := by
  obtain ⟨ha, hL, hR⟩ := hi
  simp only [next] at h
  have hL2 := NZ_hd_tl _ hL
  have hR2 := NZ_tl _ (NZ_tl R hR)
  generalize hd L = a at h ha
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 5 := ⟨a - 5, by omega⟩
  generalize hd R = r at h
  match r, h with
  | 0, h =>
    simp only [nextB, Option.some.injEq] at h; subst h
    exact ⟨_, a + 5, _, rfl, by omega, hL2, NZ_tl _ hR2⟩
  | r + 1, h =>
    simp only [nextB, Option.some.injEq] at h; subst h
    exact ⟨_, a + 5, _, rfl, by omega, hL2, hR2⟩

/-- **`Inv` is preserved by the block map.** -/
theorem inv_next : ∀ p p', Inv p → next p = some p' → Inv p'
  | .E L R, p', hi, h => inv_E L R p' hi h
  | .C L R, p', hi, h => inv_C L R p' hi h
  | .B L R, p', hi, h => inv_B L R p' hi h
  | .F _ _, _, hi, _ => hi.elim

theorem next_start : next start = some (.C [0, 1, 0] []) := rfl

theorem inv_one : Inv (.C [0, 1, 0] []) :=
  ⟨0, 1, [0], rfl, by omega, Or.inr (fun y hy => by simp at hy; exact hy), trivial⟩

/-- Every frame of the run after the first satisfies `Inv`. -/
theorem inv_orbit (k : Nat) (p : Ph) (h : iterF next (k + 1) start = some p) : Inv p := by
  simp only [iterF, next_start, Option.bind_some] at h
  exact iterF_good next Inv inv_next k _ p inv_one h

/-- **No frame of the run is an F frame.** -/
theorem no_F (k : Nat) (L R : List Nat) (h : iterF next k start = some (.F L R)) : False := by
  cases k with
  | zero => simp [iterF, start] at h
  | succ k => exact inv_orbit k _ h

/-- **No frame of the run is a critical B frame**: every B frame after the first has at least five 1s left of
the head. -/
theorem B_left_ge5 (k : Nat) (L R : List Nat) (h : iterF next (k + 1) start = some (.B L R)) : 5 ≤ hd L :=
  (inv_orbit k _ h).1

theorem no_B_critical (k : Nat) (L R : List Nat) (h : iterF next k start = some (.B L R)) :
    ¬ (hd L = 1 ∧ 3 ≤ hd R) := by
  cases k with
  | zero =>
    simp only [iterF, start, Option.some.injEq, Ph.B.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [hd]
  | succ k => have := B_left_ge5 k L R h; omega

/-- The only critical frames the run can reach are `C (2 :: L) (r + 1 :: R)`. -/
theorem critical_is_C (k : Nat) (p : Ph) (h : iterF next k start = some p) (hc : Critical p) :
    ∃ L R, p = .C L R ∧ hd L = 2 ∧ 1 ≤ hd R := by
  match p, h, hc with
  | .C L R, _, hc => exact ⟨L, R, rfl, hc⟩
  | .B L R, h, hc => exact (no_B_critical k L R h hc).elim
  | .F L R, h, _ => exact (no_F k L R h).elim

/-- **The machine halts from blank tape iff the block map, from `B [1] []`, reaches a frame
`C (2 :: L) (r + 1 :: R)`**: the tape `... 0 1 1 C> 0 1 ...`. -/
theorem halts_iff_C :
    HaltsFromBlank ↔ ∃ k L R, iterF next k start = some (.C L R) ∧ hd L = 2 ∧ 1 ≤ hd R := by
  rw [halts_iff_critical]
  constructor
  · rintro ⟨k, p, h, hc⟩
    obtain ⟨L, R, rfl, h2⟩ := critical_is_C k p h hc
    exact ⟨k, L, R, h, h2⟩
  · rintro ⟨k, L, R, h, h2⟩
    exact ⟨k, .C L R, h, h2⟩

/-- From an E frame satisfying `Inv` the block map never goes straight to a critical frame. -/
theorem E_next_not_critical (L R : List Nat) (p' : Ph) (hi : Inv (.E L R)) (h : next (.E L R) = some p') :
    ¬ Critical p' := by
  obtain ⟨_, m, R', rfl, hm, _⟩ := hi
  simp only [next, hd_cons, tl_cons] at h
  match m, hm, h with
  | 1, _, h =>
    simp only [nextE, Option.some.injEq] at h; subst h
    simp [Critical, hd]
  | m + 2, _, h =>
    simp only [nextE, Option.some.injEq] at h; subst h
    simp [Critical, hd]

/-- **A critical frame of the run comes right after a B or C frame**, never after an E (or F) frame: the machine
can only halt while the head is moving right, in a B or C frame. -/
theorem critical_after_BC (k : Nat) (p p' : Ph) (h : iterF next k start = some p) (h' : next p = some p')
    (hc : Critical p') : (∃ L R, p = .B L R) ∨ (∃ L R, p = .C L R) := by
  cases k with
  | zero =>
    simp only [iterF, Option.some.injEq] at h; subst h
    exact Or.inl ⟨[1], [], rfl⟩
  | succ k =>
    have hi := inv_orbit k p h
    match p, hi with
    | .E L R, hi => exact (E_next_not_critical L R p' hi h' hc).elim
    | .C L R, _ => exact Or.inr ⟨L, R, rfl⟩
    | .B L R, _ => exact Or.inl ⟨L, R, rfl⟩
    | .F _ _, hi => exact hi.elim

end H15414
