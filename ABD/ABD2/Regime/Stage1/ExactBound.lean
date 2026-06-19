import ABD.ABD2.Regime.Core

namespace ABD2
namespace ABCTriple

/-- Stage 1 regime: only one exact bound is accepted.

This is useful after a construction produces a specific bound `B₀`; the regime
records that exact bound without yet proving that it is power-saving. -/
def exactBoundRegime (T : ABCTriple) (B₀ : ℤ) : T.Regime :=
{ accepts := fun B => B = B₀ }

/-- The distinguished bound is accepted by its exact-bound regime. -/
theorem exactBoundRegime_accepts_self
    (T : ABCTriple) (B₀ : ℤ) :
    (T.exactBoundRegime B₀).accepts B₀ := by
  rfl

/-- If a bound is equal to the distinguished bound, it is accepted. -/
theorem exactBoundRegime_accepts_of_eq
    (T : ABCTriple) {B B₀ : ℤ}
    (h : B = B₀) :
    (T.exactBoundRegime B₀).accepts B := by
  exact h

/-- Accepted bounds in an exact-bound regime are exactly equal to the chosen bound. -/
theorem exactBoundRegime_accepts_iff
    (T : ABCTriple) (B B₀ : ℤ) :
    (T.exactBoundRegime B₀).accepts B ↔ B = B₀ := by
  rfl

end ABCTriple
end ABD2
