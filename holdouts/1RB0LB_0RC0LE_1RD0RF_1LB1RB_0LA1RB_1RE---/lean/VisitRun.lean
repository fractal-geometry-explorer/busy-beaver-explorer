import VisitSeg1
import VisitSeg2
import VisitSeg3
import VisitSeg4
import VisitSeg5
import VisitSeg6
import VisitSeg7
import VisitSeg8
import VisitSeg9
import VisitSeg10

/-! `check 161210 [true] = true`: the 10 segments chained (`iter_add`), then the halting round 161211 (`native_decide`). -/

namespace VisitLaw.Run

theorem last : hscan fuelR 0 0 (true :: false :: dec l161210 n161210) = true := by native_decide

theorem reach57000 : iter 57000 [true] = some (dec l57000 n57000) := segFrom_sound seg1

theorem reach80600 : iter 80600 [true] = some (dec l80600 n80600) := by
  have h := iter_add (b := 23600) reach57000
  rw [show 23600 + 57000 = 80600 from rfl] at h
  exact h.trans (seg_sound seg2)

theorem reach98700 : iter 98700 [true] = some (dec l98700 n98700) := by
  have h := iter_add (b := 18100) reach80600
  rw [show 18100 + 80600 = 98700 from rfl] at h
  exact h.trans (seg_sound seg3)

theorem reach114000 : iter 114000 [true] = some (dec l114000 n114000) := by
  have h := iter_add (b := 15300) reach98700
  rw [show 15300 + 98700 = 114000 from rfl] at h
  exact h.trans (seg_sound seg4)

theorem reach127400 : iter 127400 [true] = some (dec l127400 n127400) := by
  have h := iter_add (b := 13400) reach114000
  rw [show 13400 + 114000 = 127400 from rfl] at h
  exact h.trans (seg_sound seg5)

theorem reach139600 : iter 139600 [true] = some (dec l139600 n139600) := by
  have h := iter_add (b := 12200) reach127400
  rw [show 12200 + 127400 = 139600 from rfl] at h
  exact h.trans (seg_sound seg6)

theorem reach145300 : iter 145300 [true] = some (dec l145300 n145300) := by
  have h := iter_add (b := 5700) reach139600
  rw [show 5700 + 139600 = 145300 from rfl] at h
  exact h.trans (seg_sound seg7)

theorem reach150800 : iter 150800 [true] = some (dec l150800 n150800) := by
  have h := iter_add (b := 5500) reach145300
  rw [show 5500 + 145300 = 150800 from rfl] at h
  exact h.trans (seg_sound seg8)

theorem reach156100 : iter 156100 [true] = some (dec l156100 n156100) := by
  have h := iter_add (b := 5300) reach150800
  rw [show 5300 + 150800 = 156100 from rfl] at h
  exact h.trans (seg_sound seg9)

theorem reach161210 : iter 161210 [true] = some (dec l161210 n161210) := by
  have h := iter_add (b := 5110) reach156100
  rw [show 5110 + 156100 = 161210 from rfl] at h
  exact h.trans (seg_sound seg10)

/-- After 161210 rounds from the word `1` the next round halts. -/
theorem check_run : check 161210 [true] = true := check_of reach161210 last

end VisitLaw.Run
