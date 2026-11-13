import FrontierRules
import Cursor

/-!
# The left-end phase as a local rewriting system

`tripGen`: if the head, standing just right of a passed unit (left context `1 1 0 1 0`), turns at the word `In` and
leaves `1 1 Out` behind, then for every first unit `(01)^(x+2) 0 0110` and every list `bs` of units
`(01)^(b+2) 0 0110` the whole round trip from the left end takes

    A> (01)^(x+2) 0 0110  units(bs)  In     to     A> (01)^(x+1) 0 0110  units(bs)  0 1 0 1 0 1 Out .

The `trip_*` theorems apply it to each frontier rule of `FrontierRules.lean` (written by `py/gen_frontier.py`). The
`te*`/`se*` rules there are already whole round trips (no unit before the frontier).
-/

namespace H14847

open TM

/-- The left context `1 1 0 1 0` (stored nearest cell first) in front of `L`. -/
def Vc (L : Tape) : Tape := cons false (cons true (cons false (cons true (cons true L))))

theorem tripGen (In Out : Tape)
    (hturn : ∀ L, ∃ n, steps n ⟨Vc L, In, .A⟩ = some ⟨Vc L, cons true (cons true Out), .A⟩)
    (x : Nat) (bs : List Nat) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs In), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true
        Out))))))), .A⟩ := by
  have h1 := unitR (x + 2) blank (UL bs In)
  obtain ⟨n2, h2⟩ := passR bs (Vn (x + 2) blank) In
  obtain ⟨m, L', e⟩ := VL_shape bs (x + 2) blank
  obtain ⟨n3, h3⟩ := hturn (rep m [false, true] L')
  rw [show Vc (rep m [false, true] L') = VL bs (Vn (x + 2) blank) by rw [e]; rfl] at h3
  obtain ⟨n4, h4⟩ := passL bs (Vn (x + 2) blank) (cons true Out)
  have h5 := unitL x blank (ZL bs (cons true Out))
  have h6 := edgeL (Zn x (ZL bs (cons true Out)))
  rw [shiftX, shiftL] at h6
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4
    (steps_seq trans h5 h6))))⟩

/-- One round trip at the frontier `(01)^a+3 1` for every list of units (rule `tuG1`). -/
theorem trip_tuG1 (x a : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (rep (a + 3) [false, true] (cons true (S)))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (rep (a + 2) [true, false] (S)))))))))), .A⟩ :=
  tripGen (rep (a + 3) [false, true] (cons true (S))) (cons false (rep (a + 2) [true, false] (S))) (fun L => ⟨_, tuG1 a L S⟩) x bs

/-- One round trip at the frontier `(01)^a+3 0 0 1 0 1` for every list of units (rule `tuG2`). -/
theorem trip_tuG2 (x a : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons true (S)))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (rep (a + 3) [false, true] (cons false (cons true (cons true (S)))))))))))), .A⟩ :=
  tripGen (rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons true (S))))))) (rep (a + 3) [false, true] (cons false (cons true (cons true (S))))) (fun L => ⟨_, tuG2 a L S⟩) x bs

/-- One round trip at the frontier `(01)^a+3 0 0 1 0 0 1` for every list of units (rule `tuK`). -/
theorem trip_tuK (x a : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons true (S))))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (S))))))))))))), .A⟩ :=
  tripGen (rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons true (S)))))))) (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (S)))))) (fun L => ⟨_, tuK a L S⟩) x bs

/-- One round trip at the frontier `(01)^a+3 0 0 0 1` for every list of units (rule `tuH`). -/
theorem trip_tuH (x a : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (rep (a + 3) [false, true] (cons false (cons false (cons false (cons true (S))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (rep a [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons true (S))))))))))))))))), .A⟩ :=
  tripGen (rep (a + 3) [false, true] (cons false (cons false (cons false (cons true (S)))))) (cons false (rep a [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons true (S)))))))))) (fun L => ⟨_, tuH a L S⟩) x bs

/-- One round trip at the frontier `(01)^a+3 0 0 0 0` for every list of units (rule `tuX0`). -/
theorem trip_tuX0 (x a : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (rep (a + 3) [false, true] (cons false (cons false (cons false (cons false (S))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (rep a [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (S))))))))))))))))), .A⟩ :=
  tripGen (rep (a + 3) [false, true] (cons false (cons false (cons false (cons false (S)))))) (cons false (rep a [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (S)))))))))) (fun L => ⟨_, tuX0 a L S⟩) x bs

/-- One round trip at the frontier `(01)^a+3 0 0 1 0 0 0` for every list of units (rule `tuX1`). -/
theorem trip_tuX1 (x a : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons false (S))))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons false (S))))))))))))), .A⟩ :=
  tripGen (rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons false (S)))))))) (rep (a + 3) [false, true] (cons false (cons true (cons false (cons false (S)))))) (fun L => ⟨_, tuX1 a L S⟩) x bs

/-- One round trip at the frontier `0 1 1` for every list of units (rule `suG11`). -/
theorem trip_suG11 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons true (cons true (S))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (S))))))))), .A⟩ :=
  tripGen (cons false (cons true (cons true (S)))) (cons false (S)) (fun L => ⟨_, suG11 L S⟩) x bs

/-- One round trip at the frontier `0 1 0 1 1` for every list of units (rule `suG12`). -/
theorem trip_suG12 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons true (cons false (cons true (cons true (S))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (S))))))))))), .A⟩ :=
  tripGen (cons false (cons true (cons false (cons true (cons true (S)))))) (cons false (cons true (cons false (S)))) (fun L => ⟨_, suG12 L S⟩) x bs

/-- One round trip at the frontier `0 0 1 0 1` for every list of units (rule `suG20`). -/
theorem trip_suG20 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons false (cons true (cons false (cons true (S))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (S))))))))))), .A⟩ :=
  tripGen (cons false (cons false (cons true (cons false (cons true (S)))))) (cons false (cons true (cons true (S)))) (fun L => ⟨_, suG20 L S⟩) x bs

/-- One round trip at the frontier `0 1 0 0 1 0 1` for every list of units (rule `suG21`). -/
theorem trip_suG21 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons true (cons false (cons false (cons true (cons false (cons true (S))))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (S))))))))))))), .A⟩ :=
  tripGen (cons false (cons true (cons false (cons false (cons true (cons false (cons true (S)))))))) (cons false (cons true (cons false (cons true (cons true (S)))))) (fun L => ⟨_, suG21 L S⟩) x bs

/-- One round trip at the frontier `0 1 0 1 0 0 1 0 1` for every list of units (rule `suG22`). -/
theorem trip_suG22 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons true (S))))))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (S))))))))))))))), .A⟩ :=
  tripGen (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons true (S)))))))))) (cons false (cons true (cons false (cons true (cons false (cons true (cons true (S)))))))) (fun L => ⟨_, suG22 L S⟩) x bs

/-- One round trip at the frontier `0 0 1 0 0 1` for every list of units (rule `suK0`). -/
theorem trip_suK0 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons false (cons true (cons false (cons false (cons true (S)))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (S)))))))))))), .A⟩ :=
  tripGen (cons false (cons false (cons true (cons false (cons false (cons true (S))))))) (cons false (cons true (cons false (cons true (S))))) (fun L => ⟨_, suK0 L S⟩) x bs

/-- One round trip at the frontier `0 1 0 0 1 0 0 1` for every list of units (rule `suK1`). -/
theorem trip_suK1 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (S)))))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (S)))))))))))))), .A⟩ :=
  tripGen (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (S))))))))) (cons false (cons true (cons false (cons true (cons false (cons true (S))))))) (fun L => ⟨_, suK1 L S⟩) x bs

/-- One round trip at the frontier `0 1 0 1 0 0 1 0 0 1` for every list of units (rule `suK2`). -/
theorem trip_suK2 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (S)))))))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (S)))))))))))))))), .A⟩ :=
  tripGen (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (S))))))))))) (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (S))))))))) (fun L => ⟨_, suK2 L S⟩) x bs

/-- One round trip at the frontier `0 0 1 0 0 0` for every list of units (rule `suX10`). -/
theorem trip_suX10 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons false (cons true (cons false (cons false (cons false (S)))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (S)))))))))))), .A⟩ :=
  tripGen (cons false (cons false (cons true (cons false (cons false (cons false (S))))))) (cons false (cons true (cons false (cons false (S))))) (fun L => ⟨_, suX10 L S⟩) x bs

/-- One round trip at the frontier `0 1 0 0 1 0 0 0` for every list of units (rule `suX11`). -/
theorem trip_suX11 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (S)))))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (S)))))))))))))), .A⟩ :=
  tripGen (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (S))))))))) (cons false (cons true (cons false (cons true (cons false (cons false (S))))))) (fun L => ⟨_, suX11 L S⟩) x bs

/-- One round trip at the frontier `0 1 0 1 0 0 1 0 0 0` for every list of units (rule `suX12`). -/
theorem trip_suX12 (x : Nat) (bs : List Nat) (S : Tape) :
    ∃ n, steps n ⟨blank, Un (x + 2) (UL bs (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (S)))))))))))), .A⟩ =
      some ⟨blank, Un (x + 1) (UL bs (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (S)))))))))))))))), .A⟩ :=
  tripGen (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (S))))))))))) (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (S))))))))) (fun L => ⟨_, suX12 L S⟩) x bs

end H14847
