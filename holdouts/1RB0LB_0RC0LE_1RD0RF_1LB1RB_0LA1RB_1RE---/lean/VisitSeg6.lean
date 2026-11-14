import VisitW127400
import VisitW139600

/-! Rounds 127401 to 139600: the checker takes the word after 127400 rounds to the word after 139600 rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg6 : seg 12200 l127400 n127400 l139600 n139600 = true := by native_decide

end VisitLaw.Run
