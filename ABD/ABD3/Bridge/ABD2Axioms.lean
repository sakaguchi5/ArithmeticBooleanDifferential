import ABD.ABD3.Core.All

namespace ABD3

/- ABD2 imported facts namespace.

This namespace is only a cache of mathematical facts already proved in ABD2,
restated in ABD3 vocabulary so that ABD3 does not reprove them.

It must not contain the new hard implication
`RadicalSmall -> D1/D2 coverage`, nor any theorem that turns ABD3 analysis into
an ABD2 final power-saving candidate. -/
namespace ABD2Facts

/-- Abstract ABD2 triple object.  Concrete synchronization with ABD2 can be added
later without polluting the ABD3 core. -/
axiom ABD2Triple : Type

/-- An ABD2 triple can be viewed as ABD3 `ABCData`. -/
axiom toABCData : ABD2Triple → ABCData

/-- Abstract ABD2 power-data object.  This exists only so ABD3 can import
ABD2-proven facts without rebuilding ABD2's internal power-data layer. -/
axiom ABD2PowerData : Type

/-- ABD2's rational power-saving data can be viewed as ABD3 `PowerData`. -/
axiom toPowerData : ABD2PowerData → PowerData

end ABD2Facts
end ABD3
