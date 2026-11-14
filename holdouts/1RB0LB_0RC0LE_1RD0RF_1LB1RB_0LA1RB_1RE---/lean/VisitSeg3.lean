import VisitW80600
import VisitW98700

/-! Rounds 80601 to 98700: the checker takes the word after 80600 rounds to the word after 98700 rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg3 : seg 18100 l80600 n80600 l98700 n98700 = true := by native_decide

end VisitLaw.Run
