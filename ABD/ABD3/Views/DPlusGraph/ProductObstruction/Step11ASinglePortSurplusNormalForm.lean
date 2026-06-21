import ABD.ABD3.Views.DPlusGraph.ProductObstruction.Step10NoPortContradiction

namespace ABD3

namespace ABCData

/-- Product-obstruction route, Step 11A.

The single-port branch is normalized on the surplus-product side.  Step 8B
already reduces the branch to a unique C-surplus port `p`; this file records the
corresponding surplus exponent `s` and collapses the positive-surplus product to
`p ^ s`. -/
def ProductObstructionSinglePortSurplusNormalFormAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p s : ℕ) : Prop :=
  T.ProductObstructionSinglePortAt P G R p ∧
    T.ProductObstructionSinglePortProductShape P G R p ∧
      T.ProductObstructionSinglePortValuationShape P G R p ∧
        s = T.PositiveSurplusExpAt P p ∧
          0 < s ∧
            T.PositiveSurplusProduct P = p ^ s

/-- In the one-port branch, every positive-surplus exponent away from the unique
port vanishes. -/
theorem positiveSurplusExpAt_eq_zero_of_singlePortAt_ne
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p q : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p)
    (hqABC : q ∈ T.supportABC)
    (hqne : q ≠ p) :
    T.PositiveSurplusExpAt P q = 0 := by
  have hnotPort : q ∉ T.CSurplusPorts P := by
    intro hqPort
    have hqMemSingleton : q ∈ ({p} : Finset ℕ) := by
      simpa [h.2.1] using hqPort
    have hqeq : q = p := by
      simpa using hqMemSingleton
    exact hqne hqeq
  have hnotPos : ¬ 0 < T.PositiveSurplusExpAt P q := by
    intro hpos
    have hqPort : q ∈ T.CSurplusPorts P :=
      (T.mem_cSurplusPorts_iff P q).mpr ⟨hqABC, hpos⟩
    exact hnotPort hqPort
  exact Nat.eq_zero_of_not_pos hnotPos

/-- In the one-port branch, the positive-surplus product is exactly the unique
port power. -/
theorem positiveSurplusProduct_eq_pow_of_singlePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p) :
    T.PositiveSurplusProduct P = p ^ T.PositiveSurplusExpAt P p := by
  classical
  unfold PositiveSurplusProduct
  refine Finset.prod_eq_single p ?hzero ?hnotmem
  · intro q hqABC hqne
    have hzero : T.PositiveSurplusExpAt P q = 0 :=
      T.positiveSurplusExpAt_eq_zero_of_singlePortAt_ne P G R p q h hqABC hqne
    simp [hzero]
  · intro hpnot
    have hpABC : p ∈ T.supportABC :=
      ((T.mem_cSurplusPorts_iff P p).mp h.1).1
    exact False.elim (hpnot hpABC)

/-- The unique single-port witness supplies the surplus-product normal form at
that port. -/
theorem singlePortSurplusNormalFormAt_of_singlePortAt
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R p : ℕ)
    (h : T.ProductObstructionSinglePortAt P G R p) :
    T.ProductObstructionSinglePortSurplusNormalFormAt P G R p
      (T.PositiveSurplusExpAt P p) := by
  have hshape : T.ProductObstructionSinglePortProductShape P G R p :=
    T.productObstructionSinglePortProductShape_of_singlePortAt P G R p h
  have hval : T.ProductObstructionSinglePortValuationShape P G R p :=
    T.productObstructionSinglePortValuationShape_of_singlePortAt P G R p h
  have hpos : 0 < T.PositiveSurplusExpAt P p :=
    ((T.mem_cSurplusPorts_iff P p).mp h.1).2
  have hprod : T.PositiveSurplusProduct P = p ^ T.PositiveSurplusExpAt P p :=
    T.positiveSurplusProduct_eq_pow_of_singlePortAt P G R p h
  exact ⟨h, hshape, hval, rfl, hpos, hprod⟩

/-- Step 11A surplus normal form for the single-port branch. -/
def ProductObstructionSinglePortSurplusNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∃ p s,
    T.ProductObstructionSinglePortSurplusNormalFormAt P G R p s

/-- The Step 8B valuation normal form supplies the Step 11A surplus normal form. -/
theorem productObstructionSinglePortSurplusNormalForm_of_valuationNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionSinglePortValuationNormalForm P G R) :
    T.ProductObstructionSinglePortSurplusNormalForm P G R := by
  rcases h with ⟨p, hpAt, _hpShape, _hpVal⟩
  exact ⟨
    p,
    T.PositiveSurplusExpAt P p,
    T.singlePortSurplusNormalFormAt_of_singlePortAt P G R p hpAt⟩

/-- Forget the Step 11A surplus normal form back to the Step 8B valuation normal
form. -/
theorem productObstructionSinglePortValuationNormalForm_of_surplusNormalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ProductObstructionSinglePortSurplusNormalForm P G R) :
    T.ProductObstructionSinglePortValuationNormalForm P G R := by
  rcases h with ⟨p, s, hs⟩
  exact ⟨p, hs.1, hs.2.1, hs.2.2.1⟩

/-- Step 11A named target: the single-port valuation normal form can be upgraded
to the single-port surplus-product normal form. -/
def ProductObstructionStep11AGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.ProductObstructionSinglePortValuationNormalForm P G R →
    T.ProductObstructionSinglePortSurplusNormalForm P G R

/-- Step 11A is proved by collapsing the singleton positive-surplus product. -/
theorem productObstructionStep11AGoal_proved
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.ProductObstructionStep11AGoal P G R := by
  intro h
  exact T.productObstructionSinglePortSurplusNormalForm_of_valuationNormalForm P G R h

end ABCData

end ABD3
