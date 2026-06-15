import ABD.Differential.FormalDerivative

namespace ABD

/-- Leibniz-rule predicate for the formal derivative reconstructed from a
finite Boolean support.

The full theorem that `formalDeriv` satisfies this predicate for all positive
inputs is the next arithmetic step.  At this layer we expose the target shape
without importing any lattice/smallness machinery. -/
def LeibnizOn (S : Finset ℕ) (x : Tangent S) (m n : ℕ) : Prop :=
  formalDeriv S x (m * n) =
    (m : ℤ) * formalDeriv S x n + (n : ℤ) * formalDeriv S x m

@[simp] theorem leibnizOn_zeroTangent (S : Finset ℕ) (m n : ℕ) :
    LeibnizOn S (zeroTangent S) m n := by
  simp [LeibnizOn]

end ABD
