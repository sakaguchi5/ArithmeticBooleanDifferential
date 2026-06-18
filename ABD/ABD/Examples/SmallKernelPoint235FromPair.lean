/- Copyright (c) 2026 NOIZ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NOIZ -/
import ABD.ABD.Examples.TwoThreeFive
import ABD.ABD.Lattice.KernelPointConstruction

namespace ABD.Examples

/-- The two support directions `2` and `3` inside the toy support `{2, 3, 5}`. -/
def supportPair235_23 : ABD.SupportPair S235 where
  left := ⟨2, by simp [S235]⟩
  right := ⟨3, by simp [S235]⟩
  ne := by decide

/-- The generic pre-Siegel construction applied to the toy equation `2 + 3 = 5`.

The resulting sigma package contains both the coefficient-derived bound and the
small nondegenerate kernel point.  Which branch is chosen is intentionally left
to the generic construction: if the left unit coefficient is zero it uses the
unit tangent, otherwise it uses the two-coordinate point.
-/
def smallKernelPoint235FromPair :
    Σ B : ℤ, ABD.SmallAdditiveKernelPoint S235 2 3 5 B :=
  ABD.smallAdditiveKernelPoint_of_supportPair S235 2 3 5 supportPair235_23

end ABD.Examples
