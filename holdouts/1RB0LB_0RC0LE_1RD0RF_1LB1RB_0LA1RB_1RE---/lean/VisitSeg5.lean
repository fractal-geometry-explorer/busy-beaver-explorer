import VisitW114000
import VisitW127400

/-! Rounds 114001 to 127400: the checker takes the word after 114000 rounds to the word after 127400 rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg5 : seg 13400 l114000 n114000 l127400 n127400 = true := by native_decide

end VisitLaw.Run
