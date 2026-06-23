import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step10ElementaryNumberTheory

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Remaining exponent-coprime target for the pure two-power frontier.

Mathematically this asks for `gcd(u,v)=1` in the model
`p^u + q^v = 2^w`.  This is separated from the mod-8 layer because its usual
proof route uses factorization of `X^d + Y^d` or primitive-divisor style input,
rather than the `{2}` C-surplus identification from Steps 8--9. -/
def ExponentCoprimeGoal (F : NormalForm T P) : Prop :=
  Nat.Coprime F.u F.v

/-- Collected elementary targets beyond the already-realized support/radical,
coefficient, and `{2}` C-surplus layers. -/
structure HardElementaryGoals (F : NormalForm T P) where
  elementary : F.ElementaryConstraintsGoal
  exponent_coprime : F.ExponentCoprimeGoal

/-- Wrapper extracting exponent coprimality from the remaining elementary package. -/
theorem exponentCoprime_of_hardElementaryGoals
    (F : NormalForm T P)
    (H : HardElementaryGoals F) :
    F.ExponentCoprimeGoal :=
  H.exponent_coprime

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
