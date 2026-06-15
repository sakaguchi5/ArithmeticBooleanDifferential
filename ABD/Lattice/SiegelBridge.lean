import ABD.Lattice.CoordinateBridge

namespace ABD

/-- The additive constraint in the shape expected before connecting to a
Siegel-lemma/matrix layer: a single integer linear equation on the tangent
coordinates of the triple support. -/
def SiegelLinearEquation (T : ABCTriple) (x : Tangent T.support) : Prop :=
  AdditiveLinearForm T.support x T.a T.b T.c = 0

/-- The Siegel-bridge equation is exactly the additive condition already proved
in the Differential layer. -/
theorem siegelLinearEquation_iff_additiveOn
    (T : ABCTriple) (x : Tangent T.support) :
    SiegelLinearEquation T x ↔ AdditiveOn T.support x T.a T.b T.c := by
  unfold SiegelLinearEquation
  exact (additiveOn_iff_linearForm_zero T.support x T.a T.b T.c).symm

/-- A Pasten candidate provides a point satisfying the Siegel-bridge linear
equation. -/
theorem PastenCandidate.siegelLinearEquation
    (T : ABCTriple) (h : PastenCandidate T) :
    SiegelLinearEquation T h.x := by
  exact (siegelLinearEquation_iff_additiveOn T h.x).mpr h.additive

end ABD
