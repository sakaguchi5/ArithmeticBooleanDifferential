import ABD.ABD3.Core.All

namespace ABD3
namespace ABCData

/-- Radical-small view obtained by replacing `radABC` with the block radical product. -/
def BlockProductRadicalSmall (T : ABCData) (P : PowerData) : Prop :=
  (((T.blockRadicalProduct : ℕ) : ℤ) ^ P.N) < ((T.C : ℤ) ^ P.M)

/-- Radical-small view in which each block radical is powered separately. -/
def BlockPowerRadicalSmall (T : ABCData) (P : PowerData) : Prop :=
  ((T.radA : ℤ) ^ P.N) * ((T.radB : ℤ) ^ P.N) * ((T.radC : ℤ) ^ P.N) <
    ((T.C : ℤ) ^ P.M)

/-- If the Boolean support radical splits as a block product, the raw radical-small
predicate is the block-product radical-small predicate. -/
theorem radicalSmall_iff_blockProductRadicalSmall
    (T : ABCData) (P : PowerData)
    (hprod : T.BlockRadicalProductView) :
    T.RadicalSmall P ↔ T.BlockProductRadicalSmall P := by
  unfold RadicalSmall RadicalSmallInt BlockProductRadicalSmall BlockRadicalProductView at *
  rw [hprod]

/-- The block-product view explicitly records the intended first decomposition. -/
def BlockProductView (T : ABCData) (P : PowerData) : Prop :=
  T.BlockRadicalProductView ∧ T.BlockProductRadicalSmall P

/-- The fully powered block view records the later target form
`radA^N * radB^N * radC^N < C^M`. -/
def BlockPowerView (T : ABCData) (P : PowerData) : Prop :=
  T.BlockRadicalProductView ∧ T.BlockPowerRadicalSmall P

end ABCData
end ABD3
