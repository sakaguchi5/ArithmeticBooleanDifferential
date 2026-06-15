import ABD.Core.TripleSupport
import ABD.Lattice.Kernel

namespace ABD

/-- The additive kernel attached to an additive triple. -/
def TripleAdditiveKernel (T : ABCTriple) : Set (Tangent T.support) :=
  AdditiveKernel T.support T.a T.b T.c

@[simp] theorem mem_tripleAdditiveKernel_iff
    (T : ABCTriple) (x : Tangent T.support) :
    x ∈ TripleAdditiveKernel T ↔ AdditiveOn T.support x T.a T.b T.c := by
  rfl

end ABD
