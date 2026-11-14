import VisitW57000
import VisitW80600

/-! Rounds 57001 to 80600: the checker takes the word after 57000 rounds to the word after 80600 rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg2 : seg 23600 l57000 n57000 l80600 n80600 = true := by native_decide

end VisitLaw.Run
