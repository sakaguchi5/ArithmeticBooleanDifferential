import ABD.ABD2.Regime.Core

namespace ABD2
namespace ABCTriple

/-- Stage 0 regime: every bound is accepted.

This is not a power-saving condition.  It is a wiring regime used to check that
finite cost witnesses can be routed through the regime interface. -/
def acceptAllRegime (T : ABCTriple) : T.Regime :=
{ accepts := fun _B => True }

/-- Every bound is accepted by `acceptAllRegime`. -/
theorem acceptAllRegime_accepts
    (T : ABCTriple) (B : ℤ) :
    T.acceptAllRegime.accepts B := by
  trivial

/-- `AcceptedBound` form of `acceptAllRegime_accepts`. -/
theorem acceptedBound_acceptAllRegime
    (T : ABCTriple) (B : ℤ) :
    T.AcceptedBound T.acceptAllRegime B := by
  exact T.acceptAllRegime_accepts B

end ABCTriple
end ABD2
