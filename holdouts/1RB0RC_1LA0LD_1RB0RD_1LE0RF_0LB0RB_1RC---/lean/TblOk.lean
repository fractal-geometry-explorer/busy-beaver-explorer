import Block

/-! The block table is right: every entry is what `mkEntry` computes (`native_decide`, about 20 s). -/

namespace H32641

theorem tblOk : tbl.all entryOk = true := by native_decide

end H32641
