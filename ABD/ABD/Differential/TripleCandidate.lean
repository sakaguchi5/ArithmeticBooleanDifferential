import ABD.ABD.Core.TripleSupport
import ABD.ABD.Differential.AdditiveConstraint
import ABD.ABD.Differential.Leibniz

namespace ABD

/-- Differential-level candidate on a selected additive triple.

This packages only the formal derivative direction and the additive constraint
`D(a) + D(b) = D(c)`.  Nondegeneracy and smallness are intentionally left to the
Lattice layer. -/
structure DifferentialCandidate (T : ABCTriple) where
  x : Tangent T.support
  additive : AdditiveOn T.support x T.a T.b T.c

/-- The additive condition of a differential candidate is equivalently the
vanishing of the associated linear form. -/
theorem DifferentialCandidate.linearForm_zero
    (T : ABCTriple) (h : DifferentialCandidate T) :
    AdditiveLinearForm T.support h.x T.a T.b T.c = 0 :=
  (additiveOn_iff_linearForm_zero T.support h.x T.a T.b T.c).mp h.additive

/-- The formal derivative associated to a differential candidate satisfies the
zero-tangent Leibniz test when the candidate is the zero tangent.

The general Leibniz theorem belongs in `Leibniz.lean`; this file only keeps the
triple-level packaging independent from Lattice. -/
@[simp] theorem zeroDifferentialCandidate_leibniz
    (T : ABCTriple) (m n : ℕ) :
    LeibnizOn T.support (zeroTangent T.support) m n := by
  simp

end ABD
