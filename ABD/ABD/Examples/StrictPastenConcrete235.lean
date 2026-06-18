/-
Copyright (c) 2026 NOIZ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NOIZ
-/
import ABD.ABD.Examples.PastenConcrete235
import ABD.ABD.Lattice.PastenT

namespace ABD.Examples

/-- The concrete tangent on the canonical support of `2 + 3 = 5` has nonzero
Pasten Wronskian. -/
theorem kernelTangent235OnTriple_wronskian :
    ABD.WronskianOn twoThreeFiveTriple.support kernelTangent235OnTriple
      twoThreeFiveTriple.a twoThreeFiveTriple.b = -3 := by
  unfold ABD.WronskianOn
  rw [
    kernelTangent235OnTriple_formalDeriv_two,
    kernelTangent235OnTriple_formalDeriv_three
  ]
  simp [twoThreeFiveTriple]

/-- The concrete tangent is nondegenerate in Pasten's Wronskian sense. -/
theorem kernelTangent235OnTriple_pastenNondegenerate :
    twoThreeFiveTriple.PastenNondegenerate kernelTangent235OnTriple := by
  unfold ABD.ABCTriple.PastenNondegenerate
  exact ABD.pastenNondegenerate_of_wronskian_eq
    kernelTangent235OnTriple_wronskian (by decide)

/-- The concrete tangent belongs to the explicit `PastenT` attached to `2 + 3 = 5`. -/
theorem kernelTangent235OnTriple_mem_pastenT :
    kernelTangent235OnTriple ∈ ABD.PastenT twoThreeFiveTriple := by
  exact kernelTangent235OnTriple_additive

/-- The `2 + 3 = 5` example as a strict Pasten-respecting small candidate. -/
def strictSmallPastenCandidate235 :
    ABD.SmallStrictPastenCandidate twoThreeFiveTriple 1 where
  x := kernelTangent235OnTriple
  mem_T := kernelTangent235OnTriple_mem_pastenT
  nondegenerate := kernelTangent235OnTriple_pastenNondegenerate
  small := kernelTangent235OnTriple_small_one

/-- Existence form for the strict Pasten-respecting concrete example. -/
theorem exists_strictSmallPastenCandidate235 :
    ∃ h : ABD.SmallStrictPastenCandidate twoThreeFiveTriple 1,
      h.x = kernelTangent235OnTriple := by
  exact ⟨strictSmallPastenCandidate235, rfl⟩

end ABD.Examples
