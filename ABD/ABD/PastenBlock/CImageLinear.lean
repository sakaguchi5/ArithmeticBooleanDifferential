import Mathlib.Algebra.Module.Submodule.Range
import ABD.ABD.PastenBlock.CLinear

namespace ABD

/-- The set-level range of the linearized `c`-side adjustment map. -/
def ABCTriple.cLinearMapRange (T : ABCTriple) : Set ℤ :=
  Set.range T.cLinearMap

@[simp]
theorem ABCTriple.mem_cLinearMapRange_iff
    (T : ABCTriple) (target : ℤ) :
    target ∈ T.cLinearMapRange ↔
      ∃ xC : T.CTangent, T.cLinearForm xC = target := by
  unfold ABCTriple.cLinearMapRange
  constructor
  · intro h
    rcases h with ⟨xC, hxC⟩
    exact ⟨xC, by simpa using hxC⟩
  · intro h
    rcases h with ⟨xC, hxC⟩
    exact ⟨xC, by simpa using hxC⟩

/-- The previously defined `cImage` is exactly the set-level range of the
linearized `c`-side adjustment map. -/
theorem ABCTriple.cImage_eq_cLinearMapRange
    (T : ABCTriple) :
    T.cImage = T.cLinearMapRange := by
  ext target
  rw [T.mem_cImage_iff]
  rw [T.mem_cLinearMapRange_iff]

/-- The submodule range of the linearized `c`-side adjustment map. -/
noncomputable def ABCTriple.cLinearMapSubmoduleRange
    (T : ABCTriple) : Submodule ℤ ℤ :=
  LinearMap.range T.cLinearMap

@[simp]
theorem ABCTriple.mem_cLinearMapSubmoduleRange_iff
    (T : ABCTriple) (target : ℤ) :
    target ∈ T.cLinearMapSubmoduleRange ↔
      ∃ xC : T.CTangent, T.cLinearForm xC = target := by
  unfold ABCTriple.cLinearMapSubmoduleRange
  change (∃ xC : T.CTangent, T.cLinearMap xC = target) ↔
    ∃ xC : T.CTangent, T.cLinearForm xC = target
  rfl

/-- The set-level `cImage` is also the carrier of the submodule range. -/
theorem ABCTriple.cImage_eq_cLinearMapSubmoduleRange_carrier
    (T : ABCTriple) :
    T.cImage = (T.cLinearMapSubmoduleRange : Set ℤ) := by
  ext target
  rw [T.mem_cImage_iff]
  change (∃ xC, T.cLinearForm xC = target) ↔
    target ∈ T.cLinearMapSubmoduleRange
  rw [T.mem_cLinearMapSubmoduleRange_iff]

end ABD
