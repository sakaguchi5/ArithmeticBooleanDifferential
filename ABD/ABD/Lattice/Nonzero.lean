import ABD.ABD.Lattice.TripleKernel
import ABD.ABD.Lattice.Nondegenerate

namespace ABD

/-- A nonzero point in the additive kernel of an additive triple.

At the current stage `Nondegenerate` is still the minimal `NonzeroTangent`
predicate.  Later this is the place where Pasten-style degenerate subspaces can
be excluded. -/
def NonzeroKernelPoint (T : ABCTriple) : Prop :=
  ∃ x : Tangent T.support,
    x ∈ TripleAdditiveKernel T ∧ Nondegenerate T.support x

end ABD
