import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step17BothOddResidualCore

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Final hard-core input to be proved later.

After all external non-both-odd branch inputs have been installed, this is the
remaining mathematical target: the full residual both-odd hard core should be
contradictory. -/
axiom bothOddResidualHardCore_contradiction_goal
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    False

/-- If the final both-odd hard core is contradictory, then the pure two-power
normal form has no surviving desync package under the external branch closures. -/
theorem contradiction_of_externalBranchClosureAxioms
    (F : NormalForm T P) (E : ExternalBranchClosureAxioms F) :
    False :=
  F.bothOddResidualHardCore_contradiction_goal
    (F.bothOddResidualHardCore_of_externalBranchClosureAxioms E)

/-- Canonical no-survivor theorem using the named external branch inputs. -/
theorem contradiction_of_externalBranchInputs
    (F : NormalForm T P) :
    False :=
  F.contradiction_of_externalBranchClosureAxioms F.externalBranchClosureAxioms

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
