import VisitW57000

/-! Rounds 1 to 57000: the checker takes the word after 0 rounds to the word after 57000 rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg1 : segFrom 57000 [true] l57000 n57000 = true := by native_decide

end VisitLaw.Run
