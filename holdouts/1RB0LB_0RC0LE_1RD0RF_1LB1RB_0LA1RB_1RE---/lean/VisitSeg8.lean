import VisitW145300
import VisitW150800

/-! Rounds 145301 to 150800: the checker takes the word after 145300 rounds to the word after 150800 rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg8 : seg 5500 l145300 n145300 l150800 n150800 = true := by native_decide

end VisitLaw.Run
