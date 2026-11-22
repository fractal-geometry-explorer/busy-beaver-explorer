import Invariant

/-!
# 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA: halting is decided at the start of a sweep

By `Invariant.lean` the only critical frame the run can reach is `C (2 :: L) (r + 1 :: R)`, and it is reached
from a B or C frame.  This file follows the head as it moves right through C frames (a **sweep**) and shows that
whether the sweep halts is a property of the frame it starts from.

`bad c R` says that the C frames from `C (c :: L) R` (any `L`) reach the critical frame before leaving state C.
Reading the list: from `c = 0` or `c ≥ 3` each step moves one block to the left list (`C (r + 1 :: …) R`), so the
sweep walks along `R` until the first block of 0 or 1 cells: a 0 turns the head round (state E), a 1 halts iff
the next block is not empty.

A sweep starts at a B frame (`B L (r + 1 :: R)` goes to `C (r :: …) R`; `B L (0 :: R)` cannot start a halting
sweep) or at an E frame `E L (1 :: 0 :: R)` (which goes to `C (0 :: …) R`).  `SweepStart p` says that `p` starts
a sweep that halts.

* `halts_iff_sweep` (kernel only): **the machine halts from blank tape iff the run reaches a frame that starts
  a halting sweep.**  In words: iff at some B frame the blocks right of the head are `r₀, r₁, r₂, …` with
  either `r₀ = 3` and `r₁ ≥ 1`, or `r₀ ≠ 2` and the first block among `r₁, r₂, …` with fewer than two 1s is a
  block of exactly one 1 followed by a non-empty block (or the same at an E frame `E L (1 :: 0 :: R)`, with the
  walk along `R` starting at once).
-/

namespace H15414

open TM

/-- The sweep from `C (c :: L) R` reaches the critical frame. -/
def bad : Nat → List Nat → Bool
  | 0, [] => false
  | 0, r :: R => bad (r + 1) R
  | 1, _ => false
  | 2, [] => false
  | 2, r :: _ => decide (1 ≤ r)
  | _ + 3, [] => false
  | _ + 3, r :: R => bad (r + 1) R

theorem bad_one : ∀ R, bad 1 R = false
  | [] => rfl
  | _ :: _ => rfl

theorem bad_zero_cons (c : Nat) (R : List Nat) : bad c (0 :: R) = false := by
  match c with
  | 0 => simp [bad, bad_one]
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => simp [bad, bad_one]

theorem bad_hd_tl (c : Nat) : ∀ R, bad c (hd R :: tl R) = bad c R
  | [] => by
    show bad c [0] = bad c []
    rw [bad_zero_cons]
    match c with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | _ + 3 => rfl
  | _ :: _ => rfl

theorem bad_Z_zero : ∀ R, Z R → bad 0 R = false
  | [], _ => rfl
  | x :: R, h => by
    have : x = 0 := h x (List.mem_cons_self ..)
    subst this; exact bad_zero_cons 0 R

/-- One step of a sweep keeps `bad`. -/
theorem bad_C_C (c : Nat) (L R : List Nat) (c' : Nat) (L' R' : List Nat)
    (h : next (.C (c :: L) R) = some (.C (c' :: L') R')) : bad c' R' = bad c R := by
  simp only [next, hd_cons, tl_cons] at h
  match c, R, h with
  | 0, [], h =>
    simp only [hd, tl, nextC, Option.some.injEq, Ph.C.injEq, List.cons.injEq] at h
    obtain ⟨⟨rfl, -⟩, rfl⟩ := h; rfl
  | 0, r :: R, h =>
    simp only [hd, tl, nextC, Option.some.injEq, Ph.C.injEq, List.cons.injEq] at h
    obtain ⟨⟨rfl, -⟩, rfl⟩ := h; rfl
  | 1, R, h => simp [nextC] at h
  | 2, [], h => simp [hd, tl, nextC] at h
  | 2, 0 :: R, h => simp [hd, tl, nextC] at h
  | 2, (_ + 1) :: R, h => simp [hd, tl, nextC] at h
  | a + 3, [], h =>
    simp only [hd, tl, nextC, Option.some.injEq, Ph.C.injEq, List.cons.injEq] at h
    obtain ⟨⟨rfl, -⟩, rfl⟩ := h; rfl
  | a + 3, r :: R, h =>
    simp only [hd, tl, nextC, Option.some.injEq, Ph.C.injEq, List.cons.injEq] at h
    obtain ⟨⟨rfl, -⟩, rfl⟩ := h; rfl

/-- A halting sweep gets to the critical frame. -/
theorem bad_reaches : ∀ (n : Nat) (c : Nat) (L R : List Nat), R.length ≤ n → bad c R = true →
    ∃ k q, iterF next k (.C (c :: L) R) = some q ∧ next q = none
  | n, c, L, R, hn, hb => by
    match c, R, hb with
    | 0, r :: R, hb =>
      cases n with
      | zero => simp at hn
      | succ n =>
        obtain ⟨k, q, hq, hq'⟩ := bad_reaches n (r + 1) (hd L :: tl L) R (by simp at hn; omega) hb
        exact ⟨k + 1, q, by simpa [iterF, next, nextC, hd, tl] using hq, hq'⟩
    | 2, r :: R, hb =>
      have : 1 ≤ r := by simpa [bad] using hb
      obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      exact ⟨0, _, rfl, by simp [next, nextC, hd, tl]⟩
    | a + 3, r :: R, hb =>
      cases n with
      | zero => simp at hn
      | succ n =>
        obtain ⟨k, q, hq, hq'⟩ := bad_reaches n (r + 1) ((a + 2) :: hd L :: tl L) R (by simp at hn; omega) hb
        exact ⟨k + 1, q, by simpa [iterF, next, nextC, hd, tl] using hq, hq'⟩
    | 0, [], hb => simp [bad] at hb
    | 1, _, hb => simp [bad_one] at hb
    | 2, [], hb => simp [bad] at hb
    | _ + 3, [], hb => simp [bad] at hb

theorem iterF_add_some {α : Type} (nx : α → Option α) : ∀ (k : Nat) (x y : α), iterF nx k x = some y →
    ∀ n, iterF nx (k + n) x = iterF nx n y
  | 0, x, y, h, n => by simp only [iterF, Option.some.injEq] at h; subst h; simp
  | k + 1, x, y, h, n => by
    simp only [iterF] at h
    cases hx : nx x with
    | none => simp [hx] at h
    | some x' =>
      rw [hx] at h
      simp only [Option.bind_some] at h
      rw [show k + 1 + n = (k + n) + 1 by omega]
      simp only [iterF, hx, Option.bind_some]
      exact iterF_add_some nx k x' y h n

/-- The frame starts a sweep that halts. -/
def SweepStart : Ph → Prop
  | .B _ R => 1 ≤ hd R ∧ bad (hd R - 1) (tl R) = true
  | .E _ R => hd R = 1 ∧ bad 0 (tl (tl R)) = true
  | _ => False

/-- The frame after a halting sweep start is a C frame that sweeps to the critical frame. -/
theorem start_next (p : Ph) (hi : Inv p) (hs : SweepStart p) :
    ∃ c L R, next p = some (.C (c :: L) R) ∧ bad c R = true := by
  match p, hi, hs with
  | .B L R, hi, hs =>
    obtain ⟨ha, -, -⟩ := hi
    obtain ⟨hr, hb⟩ := hs
    simp only [next]
    generalize hd L = a at ha
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 5 := ⟨a - 5, by omega⟩
    generalize hR : hd R = r at hr hb
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    refine ⟨r, _, _, rfl, ?_⟩
    rw [bad_hd_tl]; simpa using hb
  | .E L R, hi, hs =>
    obtain ⟨-, m, R', rfl, -, -⟩ := hi
    obtain ⟨hm, hb⟩ := hs
    simp only [hd_cons] at hm; subst hm
    exact ⟨0, _, R', rfl, hb⟩

/-- `C` frames of the run (after the first frame) do not sweep to the critical frame, as long as no frame of the
run starts a halting sweep. -/
def CSafe : Ph → Prop
  | .C (c :: _) R => bad c R = false
  | _ => True

theorem safe_step (p p' : Ph) (hi : Inv p) (hc : CSafe p) (hs : ¬ SweepStart p) (h : next p = some p') :
    CSafe p' := by
  match p, hi, hc, hs with
  | .C L R, hi, hc, _ =>
    obtain ⟨c, b, L', rfl, -, -, -⟩ := hi
    match p', h with
    | .C (c' :: L'') R', h => show bad c' R' = false; rw [bad_C_C c _ R c' L'' R' h]; exact hc
    | .C [] _, _ => trivial
    | .E _ _, _ => trivial
    | .B _ _, _ => trivial
    | .F _ _, _ => trivial
  | .E L R, hi, _, hs =>
    obtain ⟨-, m, R', rfl, hm, -⟩ := hi
    simp only [next, hd_cons, tl_cons] at h
    match m, hm, h with
    | 1, _, h =>
      simp only [nextE, Option.some.injEq] at h; subst h
      show bad 0 R' = false
      cases hb : bad 0 R'
      · rfl
      · exact (hs ⟨rfl, hb⟩).elim
    | m + 2, _, h =>
      simp only [nextE, Option.some.injEq] at h; subst h
      exact bad_zero_cons m R'
  | .B L R, hi, _, hs =>
    obtain ⟨ha, -, hR⟩ := hi
    simp only [next] at h
    generalize hd L = a at h ha
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 5 := ⟨a - 5, by omega⟩
    cases hr : hd R with
    | zero =>
      rw [hr] at h
      simp only [nextB, Option.some.injEq] at h; subst h
      -- the right list is blank
      have hz : Z R := by
        cases R with
        | nil => intro y hy; simp at hy
        | cons x R =>
          simp only [hd] at hr; subst hr
          rcases hR with ⟨h1, _⟩ | hz
          · omega
          · exact hz
      have hz2 : Z (tl R) := by
        cases R with
        | nil => intro y hy; simp [tl] at hy
        | cons x R => exact Z_tail hz
      have hs0 : hd (tl R) = 0 := by
        cases ht : tl R with
        | nil => rfl
        | cons y _ => rw [ht] at hz2; exact hz2 y (List.mem_cons_self ..)
      show bad (hd (tl R)) (tl (tl R)) = false
      rw [hs0]
      apply bad_Z_zero
      cases ht : tl R with
      | nil => intro y hy; simp [tl] at hy
      | cons y R2 => rw [ht] at hz2; simp only [tl]; exact Z_tail hz2
    | succ r =>
      rw [hr] at h
      simp only [nextB, Option.some.injEq] at h; subst h
      show bad r (hd (tl R) :: tl (tl R)) = false
      rw [bad_hd_tl]
      cases hb : bad r (tl R)
      · rfl
      · exact (hs ⟨by omega, by simpa [hr] using hb⟩).elim
  | .F _ _, hi, _, _ => exact hi.elim

/-- **The machine halts from blank tape iff the run reaches a frame that starts a sweep that halts**: a B frame
`B L R` with `hd R ≥ 1` and `bad (hd R - 1) (tl R)`, or an E frame `E L (1 :: 0 :: R)` with `bad 0 R`. -/
theorem halts_iff_sweep : HaltsFromBlank ↔ ∃ k p, iterF next k start = some p ∧ SweepStart p := by
  constructor
  · intro hh
    obtain ⟨k, L, R, hk, h2, h1⟩ := (halts_iff_C).1 hh
    refine Classical.byContradiction fun hno => ?_
    have hno' : ∀ j p, iterF next j start = some p → ¬ SweepStart p :=
      fun j p hj hs => hno ⟨j, p, hj, hs⟩
    let Good : Ph → Prop := fun p => Inv p ∧ CSafe p ∧ ∃ j, iterF next (j + 1) start = some p
    have good : ∀ p p', Good p → next p = some p' → Good p' := by
      rintro p p' ⟨hi, hc, j, hj⟩ hn
      refine ⟨inv_next p p' hi hn, safe_step p p' hi hc (hno' _ p hj) hn, j + 1, ?_⟩
      rw [iterF_succ next (j + 1) start p hj, hn]
    have g1 : Good (.C [0, 1, 0] []) := ⟨inv_one, rfl, 0, rfl⟩
    cases k with
    | zero => simp [iterF, start] at hk
    | succ k =>
      have hk' : iterF next k (.C [0, 1, 0] []) = some (.C L R) := by
        simpa [iterF, next_start] using hk
      obtain ⟨_, hc, _⟩ := iterF_good next Good good k _ _ g1 hk'
      match L, R, h2, h1, hc with
      | 2 :: _, r :: _, _, h1, hc =>
        simp only [hd] at h1
        simp [CSafe, bad] at hc
        omega
  · rintro ⟨k, p, hk, hs⟩
    have hi : Inv p := by
      cases k with
      | zero =>
        simp only [iterF, start, Option.some.injEq] at hk; subst hk
        simp [SweepStart, hd] at hs
      | succ k => exact inv_orbit k p hk
    obtain ⟨c, L, R, hn, hb⟩ := start_next p hi hs
    obtain ⟨n, q, hq, hq'⟩ := bad_reaches R.length c L R (Nat.le_refl _) hb
    refine (halts_iff).2 ⟨k + 1 + n, q, ?_, hq'⟩
    rw [iterF_add_some next (k + 1) start (.C (c :: L) R) (by rw [iterF_succ next k start p hk, hn]) n]
    exact hq

end H15414
