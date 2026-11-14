import VisitW98700
import VisitW114000

/-! Rounds 98701 to 114000: the checker takes the word after 98700 rounds to the word after 114000 rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg4 : seg 15300 l98700 n98700 l114000 n114000 = true := by native_decide

end VisitLaw.Run
