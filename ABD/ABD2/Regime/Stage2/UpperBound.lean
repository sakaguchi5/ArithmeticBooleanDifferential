import ABD.ABD2.Regime.Core

namespace ABD2
namespace ABCTriple

/-- Stage 2 regime: every bound below a fixed ceiling is accepted.

This is the first inequality-based regime.  Later estimates can prove `B ≤ B₀`
in order to pass from a concrete cost witness to an accepted cost witness. -/
def upperBoundRegime (T : ABCTriple) (B₀ : ℤ) : T.Regime :=
{ accepts := fun B => B ≤ B₀ }

/-- The ceiling bound itself is accepted. -/
theorem upperBoundRegime_accepts_self
    (T : ABCTriple) (B₀ : ℤ) :
    (T.upperBoundRegime B₀).accepts B₀ := by
  exact le_rfl

/-- Any bound below the ceiling is accepted. -/
theorem upperBoundRegime_accepts_of_le
    (T : ABCTriple) {B B₀ : ℤ}
    (h : B ≤ B₀) :
    (T.upperBoundRegime B₀).accepts B := by
  exact h

/-- Accepted bounds in an upper-bound regime are exactly those below the ceiling. -/
theorem upperBoundRegime_accepts_iff
    (T : ABCTriple) (B B₀ : ℤ) :
    (T.upperBoundRegime B₀).accepts B ↔ B ≤ B₀ := by
  rfl

/-- Monotonicity of upper-bound regimes with respect to the ceiling. -/
theorem upperBoundRegime_accepts_of_accepts_of_ceiling_le
    (T : ABCTriple) {B B₀ B₁ : ℤ}
    (hB : (T.upperBoundRegime B₀).accepts B)
    (hceil : B₀ ≤ B₁) :
    (T.upperBoundRegime B₁).accepts B := by
  exact le_trans hB hceil

end ABCTriple
end ABD2
