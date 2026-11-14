import VisitW150800
import VisitW156100

/-! Rounds 150801 to 156100: the checker takes the word after 150800 rounds to the word after 156100 rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg9 : seg 5300 l150800 n150800 l156100 n156100 = true := by native_decide

end VisitLaw.Run
