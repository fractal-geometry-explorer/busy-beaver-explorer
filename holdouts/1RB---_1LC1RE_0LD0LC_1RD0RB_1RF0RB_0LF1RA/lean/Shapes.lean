import Machine

/-! # Configurations of 1RB---_1LC1RE_0LD0LC_1RD0RB_1RF0RB_0LF1RA that halt

Each is a finite configuration (cells listed nearest the head first) whose run is evaluated on the
list simulator of `tools/lean/TM/Fin.lean`; written by `py/leanfiles.py`. -/

namespace H132322

open TM

/-- The all-ones left counter of 4 bits with the right block at the top bit: `1^10 0 1^10 E>0`. It halts after 746 steps. -/
theorem allones_4 : Halts trans (FCfg.toCfg (⟨[true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true], [], .E⟩ : FCfg St)) := by
  have h1 : TM.fsteps trans 746 (⟨[true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true], [], .E⟩ : FCfg St) = some (⟨[true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) := by decide +kernel
  have h2 : TM.fstep trans (⟨[true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) = none := by decide +kernel
  exact ⟨746, _, by rw [FCfg.steps_eq, h1]; rfl, by rw [FCfg.step_eq, h2]; rfl⟩

/-- The all-ones left counter of 5 bits with the right block at the top bit: `1^12 0 1^13 E>0`. It halts after 1514 steps. -/
theorem allones_5 : Halts trans (FCfg.toCfg (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true], [], .E⟩ : FCfg St)) := by
  have h1 : TM.fsteps trans 1514 (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true], [], .E⟩ : FCfg St) = some (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) := by decide +kernel
  have h2 : TM.fstep trans (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) = none := by decide +kernel
  exact ⟨1514, _, by rw [FCfg.steps_eq, h1]; rfl, by rw [FCfg.step_eq, h2]; rfl⟩

/-- The all-ones left counter of 6 bits with the right block at the top bit: `1^14 0 1^16 E>0`. It halts after 3050 steps. -/
theorem allones_6 : Halts trans (FCfg.toCfg (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true], [], .E⟩ : FCfg St)) := by
  have h1 : TM.fsteps trans 3050 (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true], [], .E⟩ : FCfg St) = some (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) := by decide +kernel
  have h2 : TM.fstep trans (⟨[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true], [true], .A⟩ : FCfg St) = none := by decide +kernel
  exact ⟨3050, _, by rw [FCfg.steps_eq, h1]; rfl, by rw [FCfg.step_eq, h2]; rfl⟩

end H132322
