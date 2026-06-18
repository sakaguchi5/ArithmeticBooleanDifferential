import ABD.ABD.Core.Triple

namespace ABD

/-- The Boolean prime-support attached to an additive triple. -/
def ABCTriple.support (T : ABCTriple) : Finset ℕ :=
  supp T.a ∪ (supp T.b ∪ supp T.c)

/-- Alias spelling for the support of an additive triple. -/
def ABCTriple.primeSupport (T : ABCTriple) : Finset ℕ :=
  T.support

@[simp] theorem ABCTriple.primeSupport_eq_support (T : ABCTriple) :
    T.primeSupport = T.support := by
  rfl

end ABD
