import Bits

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: frontiers of the transient (first cases of `py/sym_law.py`)

The case analysis of `py/sym_law.py` feeds the transient after a rebuild the counter's bits three at a time, lowest
first, and stops it between two groups at a *frontier*: the pass machine in mid-sweep (phase A or C, no 1s left to
read on the right) with the zone's last gap still *open*, since the bits above may add to it.  In Lean the open gap is
`openZ u bs`: the gap `u` plus whatever the bits `bs` above add to it, then the gaps of those bits.  A 0 bit closes the
gap (`openZ_false`), a 1 bit adds 4 to it (`openZ_true`).

This file states the frontier moves for all values of the parameters, every list beyond the front (`X`, the
history) and every counter above (`bs`), and proves those of the 516 cases that are pure moves of the pass machine:
the zero group on the shapes in phase C and on G, and every nonzero group on the shape `C, 0, 17 + 12n, digit`,
where the transient ends.  The cases with moments (regular sub-rounds taken as arithmetic on the list's time left)
and with loops over runs come next; see the README.
-/

namespace H4320

open TM

/-! ## The open gap -/

/-- The zone from a gap `u` that the bits `bs` (lowest first) still add to. -/
def openZ (u : Nat) (bs : List Bool) : List Nat := (u + ((zoneOf bs).headD 3 - 3)) :: (zoneOf bs).tail

theorem zoneOf_cons : ∀ bs : List Bool, ∃ g gs, zoneOf bs = g :: gs ∧ 3 ≤ g
  | [] => ⟨3, [], rfl, Nat.le_refl 3⟩
  | false :: bs => ⟨3, zoneOf bs, rfl, Nat.le_refl 3⟩
  | true :: bs => by
    obtain ⟨g, gs, hz, hg⟩ := zoneOf_cons bs
    exact ⟨g + 4, gs, by simp [zoneOf, hz], by omega⟩

theorem openZ_three (bs : List Bool) : openZ 3 bs = zoneOf bs := by
  obtain ⟨g, gs, hz, hg⟩ := zoneOf_cons bs
  simp only [openZ, hz, List.headD, List.tail]; congr 1; omega

theorem openZ_false (u : Nat) (bs : List Bool) : openZ u (false :: bs) = u :: openZ 3 bs := by
  rw [openZ_three]; simp [openZ, zoneOf]

theorem openZ_true (u : Nat) (bs : List Bool) : openZ u (true :: bs) = openZ (u + 4) bs := by
  obtain ⟨g, gs, hz, hg⟩ := zoneOf_cons bs
  simp only [openZ, zoneOf, hz, List.headD, List.tail]; congr 1; omega

/-- The open gap is `u` plus a part `g` that only the bits above decide, then the gaps `gs` of those bits. -/
theorem openZ_eq (bs : List Bool) : ∃ g gs, ∀ u, openZ u bs = (g + u) :: gs := by
  obtain ⟨g, gs, hz, hg⟩ := zoneOf_cons bs
  refine ⟨g - 3, gs, fun u => ?_⟩
  simp only [openZ, hz, List.headD, List.tail]; congr 1; omega

/-! ## Reaching one sweep state from another -/

/-- The machine goes from the sweep state `s` to the sweep state `t`. -/
def Reach (s t : PS) : Prop := ∃ n, steps n s.cfg = some t.cfg

theorem Reach.refl (s : PS) : Reach s s := ⟨0, rfl⟩

theorem Reach.next {s s' t : PS} {n : Nat} (h : pstep s = .next s' n) (h' : Reach s' t) : Reach s t := by
  obtain ⟨m, hm⟩ := h'
  exact ⟨n + m, steps_seq trans (pstep_next s s' n h) hm⟩

/-- The machine goes from the sweep state `s` to the moment `(bs, l, us)` (a sub-round ends there). -/
def ReachM (s : PS) (bs : List Nat) (l : Nat) (us : List Nat) : Prop := ∃ n, steps n s.cfg = some (gcfg bs l us)

theorem ReachM.next {s s' : PS} {n : Nat} {bs : List Nat} {l : Nat} {us : List Nat} (h : pstep s = .next s' n)
    (h' : ReachM s' bs l us) : ReachM s bs l us := by
  obtain ⟨m, hm⟩ := h'
  exact ⟨n + m, steps_seq trans (pstep_next s s' n h) hm⟩

theorem ReachM.done {s : PS} {n : Nat} {bs : List Nat} {l : Nat} {us : List Nat} (h : pstep s = .done bs l us n) :
    ReachM s bs l us := ⟨n, pstep_done s bs l us n h⟩

end H4320
