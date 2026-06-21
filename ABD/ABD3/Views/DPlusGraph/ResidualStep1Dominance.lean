import ABD.ABD3.Views.DPlusGraph.PortMassDecomposition

namespace ABD3

namespace ABCData

/-- Step 1 of the residual C-port argument.

D+ dominance is read in graph language: radical-smallness gives total C-port
mass dominance over the negative deficit product. -/
theorem residual_step1_cPortMassDominatesDeficit_of_radicalSmall
    (T : ABCData) (P : PowerData)
    (hsmall : T.RadicalSmall P) :
    T.CPortMassDominatesDeficit P := by
  exact T.theoremDPlus_as_cPortMassDominance P hsmall

/-- Step 1, equivalence form.  This is useful when the downstream argument wants
`CPortMassDominatesDeficit` as the normal form rather than `RadicalSmall`. -/
theorem residual_step1_radicalSmall_iff_cPortMassDominatesDeficit
    (T : ABCData) (P : PowerData) :
    T.RadicalSmall P ↔ T.CPortMassDominatesDeficit P := by
  exact T.theoremDPlus_iff_cPortMassDominance P

end ABCData

end ABD3
