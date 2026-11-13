import CursorRules

/-!
# The left-end (cursor) phase as a theorem for every list of units

At the moments the head reaches a new cell at the left end in state A, the tape in this phase is a list of
*units* `(01)^n 0 0110` followed by a *cursor* and an untouched rest `R`:

    F1 x bs c d R  =  A> (01)^x 0 0110  (01)^(b_1+2) 0 0110 ... (01)^(b_k+2) 0 0110  (01)^c (10)^d 0110  R
    F2 x bs c d R  =  A> (01)^x 0 0110  (01)^(b_1+2) 0 0110 ... (01)^(b_k+2) 0 0110  (01)^c 0 (01)^d 0 0110  R

(the head reads the first cell; blank tape on the left). One round trip goes right over the units, turns at the
cursor, goes back and turns at the left end:

* `F1 (x+2) bs (c+2) (d+2) R` reaches `F2 (x+1) bs (c+4) (d+1) R` (`tripF1`),
* `F2 (x+2) bs (c+2) (d+2) R` reaches `F1 (x+1) bs (c+6) (d+1) R` (`tripF2`),

whatever the list `bs` and the rest `R` are: the first unit loses one `01`, the cursor's left part gains three per
trip on average and its right part loses one. `cursor_iter` iterates the two.
-/

namespace H14847

open TM

/-- A unit `(01)^n 0 0110` in front of `s` (reading order). -/
def Un (n : Nat) (s : Tape) : Tape :=
  rep n [false, true] (cons false (cons false (cons true (cons true (cons false s)))))

/-- The units `(01)^(b+2) 0 0110`, `b ∈ bs`, in front of `s`. -/
def UL : List Nat → Tape → Tape
  | [], s => s
  | b :: bs, s => Un (b + 2) (UL bs s)

/-- The cursor `(01)^c (10)^d 0110` in front of `R`. -/
def C1 (c d : Nat) (R : Tape) : Tape :=
  rep c [false, true] (rep d [true, false] (cons false (cons true (cons true (cons false R)))))

/-- The cursor `(01)^c 0 (01)^d 0 0110` in front of `R`. -/
def C2 (c d : Nat) (R : Tape) : Tape :=
  rep c [false, true] (cons false (rep d [false, true] (cons false (cons false (cons true (cons true (cons false R)))))))

def F1 (x : Nat) (bs : List Nat) (c d : Nat) (R : Tape) : Config := ⟨blank, Un x (UL bs (C1 c d R)), .A⟩
def F2 (x : Nat) (bs : List Nat) (c d : Nat) (R : Tape) : Config := ⟨blank, Un x (UL bs (C2 c d R)), .A⟩

/-- A unit after the head has moved right over it: `(10)^n 1 1 0 1 0`, stored nearest cell first. -/
def Vn (n : Nat) (L : Tape) : Tape :=
  cons false (cons true (cons false (cons true (cons true (rep n [false, true] L)))))

/-- The units `bs` after the right-moving pass, the last one nearest the head. -/
def VL : List Nat → Tape → Tape
  | [], L => L
  | b :: bs, L => VL bs (Vn (b + 2) L)

/-- A unit after the head has moved left over it: `(10)^b 0110 0101 0`. -/
def Zn (b : Nat) (s : Tape) : Tape :=
  rep b [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false
    (cons true (cons false s)))))))))

def ZL : List Nat → Tape → Tape
  | [], s => s
  | b :: bs, s => Zn b (ZL bs s)

theorem passR : ∀ (bs : List Nat) (L R : Tape),
    ∃ n, steps n ⟨L, UL bs R, .A⟩ = some ⟨VL bs L, R, .A⟩
  | [], L, R => ⟨0, rfl⟩
  | b :: bs, L, R => by
    obtain ⟨n, hn⟩ := passR bs (Vn (b + 2) L) R
    exact ⟨2 * (b + 2) + 15 + n, steps_seq trans (unitR (b + 2) L (UL bs R)) hn⟩

theorem passL : ∀ (bs : List Nat) (L R : Tape),
    ∃ n, steps n ⟨VL bs L, cons true R, .A⟩ = some ⟨L, cons true (ZL bs R), .A⟩
  | [], L, R => ⟨0, rfl⟩
  | b :: bs, L, R => by
    obtain ⟨n, hn⟩ := passL bs (Vn (b + 2) L) R
    exact ⟨n + (2 * b + 9), steps_seq trans hn (unitL b L (ZL bs R))⟩

/-- `0 (10)^n = (01)^n 0`. -/
theorem sh0 (n : Nat) (s : Tape) : cons false (rep n [true, false] s) = rep n [false, true] (cons false s) :=
  rep_rotate n [false] [true, false] [false, true] rfl s

/-- `1 (01)^n = (10)^n 1`. -/
theorem sh1 (n : Nat) (s : Tape) : cons true (rep n [false, true] s) = rep n [true, false] (cons true s) :=
  rep_rotate n [true] [false, true] [true, false] rfl s

/-- Re-reading the tape after a round trip: `0 1 0 1 0` followed by the moved units is the units again. -/
theorem shiftL : ∀ (bs : List Nat) (s : Tape),
    cons false (cons true (cons false (cons true (cons false (ZL bs s))))) =
      UL bs (cons false (cons true (cons false (cons true (cons false s)))))
  | [], s => rfl
  | b :: bs, s => by
    simp only [ZL, UL, Zn, Un]
    rw [← shiftL bs s, sh0]
    rfl

/-- The first unit, re-read after the turn at the left end: it has lost one `01`. -/
theorem shiftX (x : Nat) (s : Tape) :
    cons false (cons true (cons false (Zn x s))) = Un (x + 1) (cons false (cons true (cons false (cons true
      (cons false s))))) := by
  simp only [Zn, Un]
  rw [sh0]
  rfl


theorem VL_shape : ∀ (bs : List Nat) (n : Nat) (L : Tape), ∃ m L', VL bs (Vn n L) = Vn m L'
  | [], n, L => ⟨n, L, rfl⟩
  | b :: bs, n, L => VL_shape bs (b + 2) (Vn n L)

theorem tailC1 (c d : Nat) (R : Tape) :
    cons false (cons true (cons false (cons true (cons false (cons true (rep (c + 1) [false, true] (cons false
      (cons false (rep (d + 1) [true, false] (cons false (cons true (cons true (cons false R))))))))))))) =
      C2 (c + 4) (d + 1) R := by
  simp only [C2]
  rw [sh0]
  rfl

theorem tailC2 (c d : Nat) (R : Tape) :
    cons false (cons true (cons false (cons true (cons false (cons true (rep (c + 2) [false, true] (cons false
      (cons true (cons true (rep d [false, true] (cons false (cons false (cons true (cons true (cons false
      R))))))))))))))) = C1 (c + 6) (d + 1) R := by
  simp only [C1]
  rw [sh1 d, ← rep_app_comm d [true, false],
    show ∀ s : Tape, rep (c + 2) [false, true] (cons false (cons true s)) = rep (c + 3) [false, true] s by
      intro s; exact rep_app_comm _ _ s]
  rfl


/-- One round trip from the cursor form `F1` (kernel). -/
theorem tripF1 (x : Nat) (bs : List Nat) (c d : Nat) (R : Tape) :
    ∃ n, steps n (F1 (x + 2) bs (c + 2) (d + 2) R) = some (F2 (x + 1) bs (c + 4) (d + 1) R) := by
  have h1 := unitR (x + 2) blank (UL bs (C1 (c + 2) (d + 2) R))
  obtain ⟨n2, h2⟩ := passR bs (Vn (x + 2) blank) (C1 (c + 2) (d + 2) R)
  obtain ⟨m, L', e⟩ := VL_shape bs (x + 2) blank
  have h3 := turnC1 c d (rep m [false, true] L') R
  rw [show cons false (cons true (cons false (cons true (cons true (rep m [false, true] L'))))) =
    VL bs (Vn (x + 2) blank) by rw [e]; rfl] at h3
  obtain ⟨n4, h4⟩ := passL bs (Vn (x + 2) blank)
    (cons true (rep (c + 1) [false, true] (cons false (cons false (rep (d + 1) [true, false] (cons false (cons true
      (cons true (cons false R)))))))))
  have h5 := unitL x blank (ZL bs (cons true (rep (c + 1) [false, true] (cons false (cons false (rep (d + 1)
    [true, false] (cons false (cons true (cons true (cons false R))))))))))
  have h6 := edgeL (Zn x (ZL bs (cons true (rep (c + 1) [false, true] (cons false (cons false (rep (d + 1)
    [true, false] (cons false (cons true (cons true (cons false R)))))))))))
  rw [shiftX, shiftL, tailC1] at h6
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4
    (steps_seq trans h5 h6))))⟩

/-- One round trip from the cursor form `F2` (kernel). -/
theorem tripF2 (x : Nat) (bs : List Nat) (c d : Nat) (R : Tape) :
    ∃ n, steps n (F2 (x + 2) bs (c + 2) (d + 2) R) = some (F1 (x + 1) bs (c + 6) (d + 1) R) := by
  have h1 := unitR (x + 2) blank (UL bs (C2 (c + 2) (d + 2) R))
  obtain ⟨n2, h2⟩ := passR bs (Vn (x + 2) blank) (C2 (c + 2) (d + 2) R)
  obtain ⟨m, L', e⟩ := VL_shape bs (x + 2) blank
  have h3 := turnC2 c d (rep m [false, true] L') R
  rw [show cons false (cons true (cons false (cons true (cons true (rep m [false, true] L'))))) =
    VL bs (Vn (x + 2) blank) by rw [e]; rfl] at h3
  obtain ⟨n4, h4⟩ := passL bs (Vn (x + 2) blank)
    (cons true (rep (c + 2) [false, true] (cons false (cons true (cons true (rep d [false, true] (cons false
      (cons false (cons true (cons true (cons false R)))))))))))
  have h5 := unitL x blank (ZL bs (cons true (rep (c + 2) [false, true] (cons false (cons true (cons true
    (rep d [false, true] (cons false (cons false (cons true (cons true (cons false R))))))))))))
  have h6 := edgeL (Zn x (ZL bs (cons true (rep (c + 2) [false, true] (cons false (cons true (cons true
    (rep d [false, true] (cons false (cons false (cons true (cons true (cons false R)))))))))))))
  rw [shiftX, shiftL, tailC2] at h6
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4
    (steps_seq trans h5 h6))))⟩

/-- Two round trips: `F1 (x+3) bs (c+2) (d+3) R` reaches `F1 (x+1) bs (c+8) (d+1) R` (kernel). -/
theorem cursor2 (x : Nat) (bs : List Nat) (c d : Nat) (R : Tape) :
    ∃ n, steps n (F1 (x + 3) bs (c + 2) (d + 3) R) = some (F1 (x + 1) bs (c + 8) (d + 1) R) := by
  obtain ⟨n1, h1⟩ := tripF1 (x + 1) bs c (d + 1) R
  obtain ⟨n2, h2⟩ := tripF2 x bs (c + 2) d R
  exact ⟨n1 + n2, steps_seq trans h1 h2⟩

/-- `j` double trips: `F1 (x+2j+1) bs (c+2) (d+2j+1) R` reaches `F1 (x+1) bs (c+6j+2) (d+1) R` (kernel). -/
theorem cursor_iter (bs : List Nat) (R : Tape) : ∀ (j x c d : Nat),
    ∃ n, steps n (F1 (x + 2 * j + 1) bs (c + 2) (d + 2 * j + 1) R) = some (F1 (x + 1) bs (c + 6 * j + 2) (d + 1) R)
  | 0, x, c, d => ⟨0, rfl⟩
  | j + 1, x, c, d => by
    obtain ⟨n1, h1⟩ := cursor2 (x + 2 * j) bs c (d + 2 * j) R
    obtain ⟨n2, h2⟩ := cursor_iter bs R j x (c + 6) d
    have e1 : x + 2 * (j + 1) + 1 = x + 2 * j + 3 := by omega
    have e2 : d + 2 * (j + 1) + 1 = d + 2 * j + 3 := by omega
    have e3 : c + 6 * (j + 1) + 2 = c + 6 + 6 * j + 2 := by omega
    have e4 : c + 8 = c + 6 + 2 := by omega
    rw [e1, e2, e3]
    rw [e4] at h1
    exact ⟨n1 + n2, steps_seq trans h1 h2⟩

end H14847
