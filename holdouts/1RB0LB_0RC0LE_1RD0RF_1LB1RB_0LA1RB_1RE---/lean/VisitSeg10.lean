import VisitW156100
import VisitW161210

/-! Rounds 156101 to 161210: the checker takes the word after 156100 rounds to the word after 161210 rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg10 : seg 5110 l156100 n156100 l161210 n161210 = true := by native_decide

end VisitLaw.Run
