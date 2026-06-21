import ABD.ABD3.Views.SurplusProductDominance

namespace ABD3

namespace ABCData

/-- The positive C-surplus ports visible to the D+ product.

A port is recorded when its positive surplus exponent is nonzero.  The carrier is
`supportABC` rather than only `supportC`, because D+ is stated over the full ABC
support.  Later refinement can prove that positive ports are genuinely C-side
ports under the appropriate support/valuation facts. -/
def CSurplusPorts (T : ABCData) (P : PowerData) : Finset ℕ :=
  T.supportABC.filter (fun p => 0 < T.PositiveSurplusExpAt P p)

/-- Membership normal form for positive surplus ports. -/
theorem mem_cSurplusPorts_iff
    (T : ABCData) (P : PowerData) (p : ℕ) :
    p ∈ T.CSurplusPorts P ↔
      p ∈ T.supportABC ∧ 0 < T.PositiveSurplusExpAt P p := by
  simp [CSurplusPorts]

/-- A named predicate for positive C-surplus ports. -/
def IsPositiveCPort (T : ABCData) (P : PowerData) (p : ℕ) : Prop :=
  p ∈ T.CSurplusPorts P

/-- D+ positive surplus mass, read in graph language as the total C-port mass.

This is intentionally definitionally the existing D+ product.  The point of this
layer is not to reprove D+, but to expose its product as the mass carried by the
positive-surplus port family. -/
def CPortMassProduct (T : ABCData) (P : PowerData) : ℕ :=
  T.PositiveSurplusProduct P

/-- The deficit product, named as the opposing mass in the D+ graph view. -/
def DeficitMassProduct (T : ABCData) (P : PowerData) : ℕ :=
  T.NegativeDeficitProduct P

@[simp] theorem cPortMassProduct_eq_positiveSurplusProduct
    (T : ABCData) (P : PowerData) :
    T.CPortMassProduct P = T.PositiveSurplusProduct P := rfl

@[simp] theorem deficitMassProduct_eq_negativeDeficitProduct
    (T : ABCData) (P : PowerData) :
    T.DeficitMassProduct P = T.NegativeDeficitProduct P := rfl

/-- D+ dominance, rephrased as C-port mass beating deficit mass. -/
def CPortMassDominatesDeficit (T : ABCData) (P : PowerData) : Prop :=
  (T.DeficitMassProduct P : ℤ) < (T.CPortMassProduct P : ℤ)

/-- The graph-language D+ dominance is definitionally the existing D+ dominance. -/
theorem cPortMassDominatesDeficit_iff_surplusProductDominatesDeficit
    (T : ABCData) (P : PowerData) :
    T.CPortMassDominatesDeficit P ↔ T.SurplusProductDominatesDeficit P := by
  rfl

/-- Theorem D+ in C-port language. -/
theorem theoremDPlus_as_cPortMassDominance
    (T : ABCData) (P : PowerData) :
    T.RadicalSmall P → T.CPortMassDominatesDeficit P := by
  intro hsmall
  exact T.theoremDPlus P hsmall

/-- The full D+ equivalence in C-port language. -/
theorem theoremDPlus_iff_cPortMassDominance
    (T : ABCData) (P : PowerData) :
    T.RadicalSmall P ↔ T.CPortMassDominatesDeficit P := by
  rw [T.theoremDPlus_iff P]
  rfl

/-- The total C-port mass is positive. -/
theorem cPortMass_pos (T : ABCData) (P : PowerData) :
    0 < T.CPortMassProduct P := by
  simpa [CPortMassProduct] using T.posSurplus_pos P

/-- The deficit mass is positive. -/
theorem deficitMass_pos (T : ABCData) (P : PowerData) :
    0 < T.DeficitMassProduct P := by
  simpa [DeficitMassProduct] using T.negDeficit_pos P

end ABCData

end ABD3
