import ABD.Differential.TripleCandidate
import ABD.Lattice.Nondegenerate
import ABD.Lattice.Nonzero
import ABD.Lattice.Smallness

namespace ABD

/-- A Pasten-style derivative candidate in the ABD language.

Leibniz is not stored as a field: it should be supplied by the formal derivative
construction itself.  This structure records the additive kernel condition and
the current nondegeneracy placeholder. -/
structure PastenCandidate (T : ABCTriple) where
  x : Tangent T.support
  additive : AdditiveOn T.support x T.a T.b T.c
  nondegenerate : Nondegenerate T.support x

@[simp] theorem PastenCandidate.mem_kernel
    (T : ABCTriple) (h : PastenCandidate T) :
    h.x ∈ TripleAdditiveKernel T := by
  exact h.additive

/-- A bounded Pasten-style candidate.  The bound is intentionally the existing
coordinatewise `SmallTangent`; no norm or geometry-of-numbers machinery is
introduced yet. -/
structure SmallPastenCandidate (T : ABCTriple) (B : ℤ) where
  x : Tangent T.support
  additive : AdditiveOn T.support x T.a T.b T.c
  nondegenerate : Nondegenerate T.support x
  small : SmallTangent T.support x B

/-- Forget the smallness field. -/
def SmallPastenCandidate.toPastenCandidate
    {T : ABCTriple} {B : ℤ} (h : SmallPastenCandidate T B) :
    PastenCandidate T where
  x := h.x
  additive := h.additive
  nondegenerate := h.nondegenerate

end ABD
