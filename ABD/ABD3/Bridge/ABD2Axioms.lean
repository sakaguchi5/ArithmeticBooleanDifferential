import ABD.ABD3.Views.All

namespace ABD3

/- ABD2 bridge namespace.

ABD3 may rely on ABD2-proven reduction/bridge facts as external axioms, while
keeping the new radical-small analysis itself axiom-free.  The core forbidden
move is to assume the new hard implication
`RadicalSmall -> D1 or D2`; that is deliberately not present here. -/
namespace ABD2Bridge

/-- Abstract ABD2 triple object.  Concrete synchronization with ABD2 can be added
later without polluting the ABD3 core. -/
axiom ABD2Triple : Type

/-- An ABD2 triple can be viewed as ABD3 `ABCData`. -/
axiom toABCData : ABD2Triple → ABCData

/-- ABD2's rational power-saving data can be viewed as ABD3 `PowerData`. -/
axiom toPowerData : Type

/-- Placeholder for ABD2-proven bridge conclusions.

This records only the permitted kind of bridge: once common-scalar coverage is
available, ABD2 knows how to route it to its power-saving candidate machinery.
It does not assert the coverage itself. -/
axiom ABD2PowerSavingCandidate : ABD2Triple → Prop

/-- Permitted bridge axiom: ABD2 reduction from common-scalar coverage to its
power-saving candidate conclusion. -/
axiom coverage_to_ABD2PowerSavingCandidate
    (U : ABD2Triple)
    (P : PowerData)
    (I : (toABCData U).CommonScalarCostInterface) :
    (toABCData U).CommonScalarCoverageVia P I →
      ABD2PowerSavingCandidate U

end ABD2Bridge
end ABD3
