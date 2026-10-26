import BB6.Blk

/-!
# Contact conditions in general, and the tape around a point

The events proved so far ask for a stripe cell before the gap and after the marker met.  The mark model allows
marks of different values to touch (`M G`, `B W`, `M W`, …: a stripe of even length may be empty), and the machine
rules only read the *values* of the neighbouring cells, so the events hold as soon as those values are right:

* `oneBefore g msL`: cell g − 1 reads 1 — a stripe cell, or the last cell of a 1-mark touching g;
* `zeroAfter p W msR`: cell p + 2 reads 0 — a stripe cell, blank, or the first cell of a 0-mark touching p + 2;
* `zeroBefore r msL`: cell r − 1 reads 0 — a stripe cell, or the last cell of a 0-mark touching r.

The two bookkeeping lemmas `buildL_add` and `build_sub` move the point of a tape builder across stripe cells, for
any number of them, keeping track of the parity of the cell at the point.
-/

namespace BB6

theorem cons_tail_eq {a : Bool} {s t : Tape} (h : cons a s = cons a t) : s = t :=
  funext fun n => congrFun h (n + 1)

/-- Cell g − 1 reads 1: the first mark to the left ends before g, or ends at g and is a 1-mark. -/
def oneBefore (g : Nat) : List Mark → Prop
  | [] => 1 ≤ g
  | m :: _ => m.p + mlen m.t < g ∨ (m.p + mlen m.t = g ∧ mval m.t = true)

/-- Cell r − 1 reads 0: the first mark to the left ends before r, or ends at r and is a 0-mark. -/
def zeroBefore (r : Nat) : List Mark → Prop
  | [] => True
  | m :: _ => m.p + mlen m.t < r ∨ (m.p + mlen m.t = r ∧ mval m.t = false)

/-- Cell p + 2 reads 0 (p + 1 being the last cell of a 1-mark): the next mark starts after p + 2, or at p + 2 and is
a 0-mark, or there is none and p + 2 ≤ W. -/
def zeroAfter (p W : Nat) : List Mark → Prop
  | [] => p + 2 ≤ W
  | m :: _ => p + 2 < m.p ∨ (p + 2 = m.p ∧ mval m.t = false)

theorem mlen_ge (t : MarkT) : 2 ≤ mlen t := by cases t <;> decide

theorem oneBefore_pos {g : Nat} {msL : List Mark} (h : oneBefore g msL) : 1 ≤ g := by
  cases msL with
  | nil => exact h
  | cons m _ => have := mlen_ge m.t; simp only [oneBefore] at h; omega

theorem stripeBefore_oneBefore {g : Nat} {msL : List Mark} (h : stripeBefore g msL) : oneBefore g msL := by
  cases msL <;> simp only [stripeBefore, oneBefore] at h ⊢ <;> omega

theorem oneBefore_endsBy {g : Nat} {msL : List Mark} (h : oneBefore g msL) : endsBy g msL := by
  cases msL <;> simp only [oneBefore, endsBy] at h ⊢ <;> omega

theorem zeroBefore_endsBy {r : Nat} {msL : List Mark} (h : zeroBefore r msL) : endsBy r msL := by
  cases msL <;> simp only [zeroBefore, endsBy] at h ⊢ <;> omega

theorem stripeBefore_endsBy' {g : Nat} {msL : List Mark} (h : stripeBefore g msL) : endsBy (g - 1) msL := by
  cases msL <;> simp only [stripeBefore, endsBy] at h ⊢ <;> omega

theorem endsBy_mono {g g' : Nat} {msL : List Mark} (h : endsBy g msL) (hg : g ≤ g') : endsBy g' msL := by
  cases msL <;> simp only [endsBy] at h ⊢ <;> omega

theorem stripeAfter_zeroAfter {p W : Nat} {msR : List Mark} (h : stripeAfter p W msR) : zeroAfter p W msR := by
  cases msR <;> simp only [stripeAfter, zeroAfter] at h ⊢ <;> omega

theorem zeroAfter_startsAt {p W : Nat} {msR : List Mark} (h : zeroAfter p W msR) : startsAt (p + 2) W msR := by
  cases msR <;> simp only [zeroAfter, startsAt] at h ⊢ <;> omega

theorem startsAt_mono {q q' W : Nat} {msR : List Mark} (h : startsAt q W msR) (hq : q' ≤ q) : startsAt q' W msR := by
  cases msR <;> simp only [startsAt] at h ⊢ <;> omega

theorem startsAt_strictAfter {q W : Nat} {msR : List Mark} (h : startsAt (q + 1) W msR) : strictAfter q W msR := by
  cases msR <;> simp only [startsAt, strictAfter] at h ⊢ <;> omega

/-- One stripe cell off the left tape: if cell p is a stripe cell, the tape left of p + 1 is that cell and the tape
left of p. -/
theorem buildL_succ (msL : List Mark) (b : Bool) (p : Nat) (h : endsBy p msL) :
    buildL b (p + 1) msL = cons (!b) (buildL (!b) p msL) := by
  cases msL with
  | nil =>
    show stripe (!b) (p + 1) blank = cons (!b) (stripe (!!b) p blank)
    rfl
  | cons m ms =>
    simp only [endsBy] at h
    have e : p + 1 - (m.p + mlen m.t) = (p - (m.p + mlen m.t)) + 1 := by omega
    show stripe (!b) (p + 1 - (m.p + mlen m.t)) _ = cons (!b) (stripe (!!b) (p - (m.p + mlen m.t)) _)
    rw [e]
    rfl

/-- `m` stripe cells off the left tape. -/
theorem buildL_add (msL : List Mark) (b : Bool) (g m : Nat) (h : endsBy g msL) :
    buildL b (g + m) msL = stripe (!b) m (buildL (if m % 2 = 0 then b else !b) g msL) := by
  induction m generalizing b with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, buildL_succ msL b (g + m) (endsBy_mono h (Nat.le_add_right g m)), ih, stripe_succ, Bool.not_not]
    rcases Nat.mod_two_eq_zero_or_one m with h2 | h2
    · have h3 : (m + 1) % 2 = 1 := by omega
      simp [h2, h3]
    · have h3 : (m + 1) % 2 = 0 := by omega
      simp [h2, h3]

/-- `m` stripe cells off the right tape: moving the start point left by `m` cells of stripe. -/
theorem build_sub (msR : List Mark) (b : Bool) (q W m : Nat) (h : startsAt q W msR) (hm : m ≤ q) :
    build b (q - m) msR W = stripe (!b) m (build (if m % 2 = 0 then b else !b) q msR W) := by
  induction m generalizing b with
  | zero => simp
  | succ m ih =>
    have hs : strictAfter (q - (m + 1)) W msR := by
      cases msR <;> simp only [startsAt, strictAfter] at h ⊢ <;> omega
    have e : q - (m + 1) + 1 = q - m := by omega
    rw [build_step msR b (q - (m + 1)) W hs, e, ih (!b) (by omega), stripe_succ, Bool.not_not]
    rcases Nat.mod_two_eq_zero_or_one m with h2 | h2
    · have h3 : (m + 1) % 2 = 1 := by omega
      simp [h2, h3]
    · have h3 : (m + 1) % 2 = 0 := by omega
      simp [h2, h3]

/-- The tape left of a point with a 1 before it starts with that 1. -/
theorem oneBefore_tail {g : Nat} {msL : List Mark} (h : oneBefore g msL) : ∃ L', buildL false g msL = cons true L' := by
  cases msL with
  | nil =>
    simp only [oneBefore] at h
    obtain ⟨n, hn⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
    subst hn
    exact ⟨stripe false n blank, rfl⟩
  | cons m ms =>
    simp only [oneBefore] at h
    rcases h with h | ⟨he, hv⟩
    · obtain ⟨n, hn⟩ : ∃ n, g - (m.p + mlen m.t) = n + 1 := ⟨g - (m.p + mlen m.t) - 1, by omega⟩
      refine ⟨stripe false n (app (mcells m.t).reverse (buildL (mval m.t) m.p ms)), ?_⟩
      show stripe (!false) (g - (m.p + mlen m.t)) _ = _
      rw [hn]
      rfl
    · have h0 : g - (m.p + mlen m.t) = 0 := by omega
      have hb : buildL false g (m :: ms) = app (mcells m.t).reverse (buildL (mval m.t) m.p ms) := by
        show stripe (!false) (g - (m.p + mlen m.t)) _ = _
        rw [h0, stripe_zero]
      rw [hb]
      cases ht : m.t <;> simp [mval, ht] at hv <;> exact ⟨_, rfl⟩

/-- The tape left of a point with a 0 before it starts with that 0. -/
theorem zeroBefore_tail {r : Nat} {msL : List Mark} (h : zeroBefore r msL) : ∃ L', buildL true r msL = cons false L' := by
  cases msL with
  | nil =>
    cases r with
    | zero => exact ⟨blank, cons_false_blank.symm⟩
    | succ n => exact ⟨stripe true n blank, rfl⟩
  | cons m ms =>
    simp only [zeroBefore] at h
    rcases h with h | ⟨he, hv⟩
    · obtain ⟨n, hn⟩ : ∃ n, r - (m.p + mlen m.t) = n + 1 := ⟨r - (m.p + mlen m.t) - 1, by omega⟩
      refine ⟨stripe true n (app (mcells m.t).reverse (buildL (mval m.t) m.p ms)), ?_⟩
      show stripe (!true) (r - (m.p + mlen m.t)) _ = _
      rw [hn]
      rfl
    · have h0 : r - (m.p + mlen m.t) = 0 := by omega
      have hb : buildL true r (m :: ms) = app (mcells m.t).reverse (buildL (mval m.t) m.p ms) := by
        show stripe (!true) (r - (m.p + mlen m.t)) _ = _
        rw [h0, stripe_zero]
      rw [hb]
      cases ht : m.t <;> simp [mval, ht] at hv <;> exact ⟨_, rfl⟩

/-- The tape right of a 1-mark ending at p + 1, with a 0 at p + 2, starts with that 0. -/
theorem zeroAfter_tail {p W : Nat} {msR : List Mark} (h : zeroAfter p W msR) :
    ∃ R', build true (p + 2) msR W = cons false R' := by
  cases msR with
  | nil =>
    simp only [zeroAfter] at h
    cases Nat.lt_or_ge (p + 2) W with
    | inl hlt =>
      obtain ⟨n, hn⟩ : ∃ n, W - (p + 2) = n + 1 := ⟨W - (p + 2) - 1, by omega⟩
      refine ⟨stripe true n blank, ?_⟩
      show stripe (!true) (W - (p + 2)) blank = _
      rw [hn]
      rfl
    | inr hge =>
      have hW : W - (p + 2) = 0 := by omega
      refine ⟨blank, ?_⟩
      show stripe (!true) (W - (p + 2)) blank = _
      rw [hW, stripe_zero, cons_false_blank]
  | cons m ms =>
    simp only [zeroAfter] at h
    rcases h with h | ⟨he, hv⟩
    · obtain ⟨n, hn⟩ : ∃ n, m.p - (p + 2) = n + 1 := ⟨m.p - (p + 2) - 1, by omega⟩
      refine ⟨stripe true n (app (mcells m.t) (build (mval m.t) (m.p + mlen m.t) ms W)), ?_⟩
      show stripe (!true) (m.p - (p + 2)) _ = _
      rw [hn]
      rfl
    · have h0 : m.p - (p + 2) = 0 := by omega
      have hb : build true (p + 2) (m :: ms) W = app (mcells m.t) (build (mval m.t) (m.p + mlen m.t) ms W) := by
        show stripe (!true) (m.p - (p + 2)) _ = _
        rw [h0, stripe_zero]
      rw [hb]
      cases ht : m.t <;> simp [mval, ht] at hv <;> exact ⟨_, rfl⟩

/-- The packet's left tape after k ≥ 1 half-turns: `(01)^k` and then what was left of the gap's first cell. -/
theorem buildL_odd_shift (msL : List Mark) (g k : Nat) (L' : Tape) (h : endsBy g msL)
    (hL : buildL false g msL = cons true L') :
    buildL true (g + (2 * k + 1)) msL = rep (k + 1) [false, true] L' := by
  rw [buildL_add msL true g (2 * k + 1) h, if_neg (by omega), Bool.not_true, hL, stripe_false_odd, rep_cons2]

/-- The left tape at an even distance beyond the gap's first cell, read with a 0 at the point. -/
theorem buildL_even_shift (msL : List Mark) (g k : Nat) (L' : Tape) (h : endsBy g msL)
    (hL : buildL false g msL = cons true L') :
    buildL false (g + 2 * k) msL = rep k [true, false] (cons true L') := by
  rw [buildL_add msL false g (2 * k) h, if_pos (by omega), Bool.not_false, hL, stripe_even, Bool.not_true]

/-- Right of a 1-mark ending at p + 1 with a 0 at p + 2: moving the start 2k + 1 cells left reads `(10)^(k+1)` and
then what followed that 0. -/
theorem build_odd_shift (msR : List Mark) (p W k : Nat) (R' : Tape) (hs : startsAt (p + 2) W msR)
    (hR : build true (p + 2) msR W = cons false R') (hk : 2 * k + 1 ≤ p + 2) :
    build false (p + 2 - (2 * k + 1)) msR W = rep (k + 1) [true, false] R' := by
  rw [build_sub msR false (p + 2) W (2 * k + 1) hs hk, if_neg (by omega), Bool.not_false, hR, stripe_true_odd, rep_cons2]

theorem stripe_five_rep (n : Nat) (s : Tape) :
    stripe true (2 * n + 4) (cons true s) = cons true (cons false (cons true (cons false (cons true (rep n [false, true] s))))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) + 4 = (2 * n + 4) + 1 + 1 by omega, stripe_succ, stripe_succ, Bool.not_true, Bool.not_false, ih]
    rfl

end BB6
