import VisitW139600
import VisitW145300

/-! Rounds 139601 to 145300: the checker takes the word after 139600 rounds to the word after 145300 rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg7 : seg 5700 l139600 n139600 l145300 n145300 = true := by native_decide

end VisitLaw.Run
