import ABD.ABD3.Views.BlockProduct

namespace ABD3
namespace ABCData

/-- A/B radical tax in the rational-power inequality. -/
def ABRadicalTax (T : ABCData) (P : PowerData) : ℤ :=
  ((T.radA : ℤ) ^ P.N) * ((T.radB : ℤ) ^ P.N)

/-- C-side squarefree tax in the rational-power inequality. -/
def CRadicalTax (T : ABCData) (P : PowerData) : ℤ :=
  ((T.radC : ℤ) ^ P.N)

/-- C-side height reward in the rational-power inequality. -/
def CHeightReward (T : ABCData) (P : PowerData) : ℤ :=
  ((T.C : ℤ) ^ P.M)

/-- Tax view of the block-powered radical-small inequality. -/
def BlockTaxDominatedByCHeight (T : ABCData) (P : PowerData) : Prop :=
  T.ABRadicalTax P * T.CRadicalTax P < T.CHeightReward P

/-- The tax view unfolds to the same expression as the block-powered radical-small view. -/
theorem blockTaxDominatedByCHeight_iff_blockPowerRadicalSmall
    (T : ABCData) (P : PowerData) :
    T.BlockTaxDominatedByCHeight P ↔ T.BlockPowerRadicalSmall P := by
  rfl

/-- View name for the heuristic reading:
A/B radical tax plus C squarefree tax is dominated by C height. -/
def TaxSurplusView (T : ABCData) (P : PowerData) : Prop :=
  T.BlockTaxDominatedByCHeight P

end ABCData
end ABD3
