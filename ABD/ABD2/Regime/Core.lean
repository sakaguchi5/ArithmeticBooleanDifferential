import ABD.ABD2.Gauge.PowerSaving

namespace ABD2
namespace ABCTriple

/-- Regime-layer alias for readability.

The existing `BoundRegime` is the canonical object.  The files under
`ABD2/Regime` do not redefine it; they only provide concrete examples and
stage-by-stage acceptance predicates for later E-level estimates. -/
abbrev Regime (T : ABCTriple) : Type :=
  T.BoundRegime

/-- A bound is accepted by a regime when it satisfies the regime's acceptance
predicate.  This wrapper gives the Regime layer a stable vocabulary without
changing the underlying definition. -/
def AcceptedBound (T : ABCTriple) (R : T.Regime) (B : ℤ) : Prop :=
  R.accepts B

/-- `AcceptedBound` is definitionally the same as `R.accepts B`. -/
theorem acceptedBound_iff
    (T : ABCTriple) (R : T.Regime) (B : ℤ) :
    T.AcceptedBound R B ↔ R.accepts B := by
  rfl

/-- Constructor for an accepted bound. -/
theorem acceptedBound_of_accepts
    (T : ABCTriple) {R : T.Regime} {B : ℤ}
    (h : R.accepts B) :
    T.AcceptedBound R B := by
  exact h

/-- Destructor for an accepted bound. -/
theorem accepts_of_acceptedBound
    (T : ABCTriple) {R : T.Regime} {B : ℤ}
    (h : T.AcceptedBound R B) :
    R.accepts B := by
  exact h

end ABCTriple
end ABD2
