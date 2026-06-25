import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step21BalancedTwoAdicDesyncCore

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- The standard prime-side killable registry.

This collects the prime-size families that should be removed before the final
balanced two-adic core is studied: bounded-prime fibers and finite prime-support
fibers.  These families need not be disjoint. -/
def StandardPrimeKillableRegistry
    (B : ℕ) (S : Finset ℕ) : Branch5Family T P :=
  Branch5Family.or (T := T) (P := P)
    (Branch5BoundedPrimeFamily (T := T) (P := P) B)
    (Branch5FinitePrimeSupportFamily (T := T) (P := P) S)

/-- The standard scale-side killable registry.

This removes the near-power/unbalanced region, and also the region that is both
exponent-asymmetric and scale-unbalanced. -/
def StandardScaleKillableRegistry
    (L C : ℕ) : Branch5Family T P :=
  Branch5Family.or (T := T) (P := P)
    (Branch5ScaleUnbalancedBy (T := T) (P := P) C)
    (Branch5AsymmetricUnbalancedBy (T := T) (P := P) L C)

/-- The standard killable registry for the Branch 5 residual hard core.

The point is bookkeeping: the registry is a single `Branch5Family` that can be
used as the `Killable` parameter in `BothOddResidualAfterKillable`.  It is not
meant to be maximal; later files can enlarge it by taking unions with additional
finite or empty families. -/
def StandardKillableRegistry
    (B L C : ℕ) (S : Finset ℕ) : Branch5Family T P :=
  Branch5Family.or (T := T) (P := P)
    (StandardPrimeKillableRegistry (T := T) (P := P) B S)
    (StandardScaleKillableRegistry (T := T) (P := P) L C)

/-- Extend a standard registry by one extra family. -/
def StandardKillableRegistry.withExtra
    (B L C : ℕ) (S : Finset ℕ)
    (Extra : Branch5Family T P) : Branch5Family T P :=
  Branch5Family.or (T := T) (P := P)
    (StandardKillableRegistry (T := T) (P := P) B L C S)
    Extra

/-- Membership helper: bounded-prime candidates are in the standard registry. -/
theorem mem_standardKillableRegistry_of_boundedPrime
    {B L C : ℕ} {S : Finset ℕ}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (h : Branch5BoundedPrimeFamily (T := T) (P := P) B F K) :
    StandardKillableRegistry (T := T) (P := P) B L C S F K := by
  exact Or.inl (Or.inl h)

/-- Membership helper: finite-prime-support candidates are in the standard registry. -/
theorem mem_standardKillableRegistry_of_finitePrimeSupport
    {B L C : ℕ} {S : Finset ℕ}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (h : Branch5FinitePrimeSupportFamily (T := T) (P := P) S F K) :
    StandardKillableRegistry (T := T) (P := P) B L C S F K := by
  exact Or.inl (Or.inr h)

/-- Membership helper: scale-unbalanced candidates are in the standard registry. -/
theorem mem_standardKillableRegistry_of_scaleUnbalanced
    {B L C : ℕ} {S : Finset ℕ}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (h : Branch5ScaleUnbalancedBy (T := T) (P := P) C F K) :
    StandardKillableRegistry (T := T) (P := P) B L C S F K := by
  exact Or.inr (Or.inl h)

/-- Membership helper: asymmetric-unbalanced candidates are in the standard registry. -/
theorem mem_standardKillableRegistry_of_asymmetricUnbalanced
    {B L C : ℕ} {S : Finset ℕ}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (h : Branch5AsymmetricUnbalancedBy (T := T) (P := P) L C F K) :
    StandardKillableRegistry (T := T) (P := P) B L C S F K := by
  exact Or.inr (Or.inr h)

/-- Membership helper for an extra registered family. -/
theorem mem_standardKillableRegistry_withExtra_of_extra
    {B L C : ℕ} {S : Finset ℕ}
    {Extra : Branch5Family T P}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (h : Extra F K) :
    StandardKillableRegistry.withExtra
      (T := T) (P := P) B L C S Extra F K := by
  exact Or.inr h

/-- Membership helper for the base standard registry inside an extension. -/
theorem mem_standardKillableRegistry_withExtra_of_standard
    {B L C : ℕ} {S : Finset ℕ}
    {Extra : Branch5Family T P}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (h : StandardKillableRegistry (T := T) (P := P) B L C S F K) :
    StandardKillableRegistry.withExtra
      (T := T) (P := P) B L C S Extra F K := by
  exact Or.inl h

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
