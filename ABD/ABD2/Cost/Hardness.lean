import ABD.ABD2.Cost.Regime

namespace ABD2
namespace ABCTriple

/-- D1-entry predicate: the two-sided AB-cancellation cost has not been placed in
this regime.  Later D-files should refine this by image/gcd/Bezout/support-rank
causes. -/
def TwoSidedABCancellationHardness
    (T : ABCTriple) (R : T.BoundRegime) : Prop :=
  ¬ T.TwoSidedABCancellationCostInRegime R

/-- D2-entry predicate: the one-sided branch has base data, but the forced cost has
not been placed in the chosen gauge regime. -/
def OneSidedForcedCLiftHardness
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime) : Prop :=
  T.OneSidedABSupport ∧ T.HasGoodBasePoint P ∧
    ¬ T.OneSidedForcedCostInRegime P G R

/-- Branch-sensitive cost hardness: after B has split the problem, failure is now
classified as either two-sided AB-cancellation hardness or one-sided forced C-lift
hardness. -/
def BranchCostHardness
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime) : Prop :=
  T.TwoSidedABCancellationHardness R ∨
    T.OneSidedForcedCLiftHardness P G R

/-- If two-sided cost is in the regime, the two-sided hardness predicate is false. -/
theorem not_twoSidedABCancellationHardness_of_costInRegime
    (T : ABCTriple) (R : T.BoundRegime)
    (h : T.TwoSidedABCancellationCostInRegime R) :
    ¬ T.TwoSidedABCancellationHardness R := by
  intro hhard
  exact hhard h

/-- If one-sided forced cost is in the regime, the one-sided hardness predicate is
false. -/
theorem not_oneSidedForcedCLiftHardness_of_costInRegime
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.BoundRegime)
    (h : T.OneSidedForcedCostInRegime P G R) :
    ¬ T.OneSidedForcedCLiftHardness P G R := by
  intro hhard
  exact hhard.2.2 h

/-- If both branch costs are already in regime, then the branch-sensitive hardness
predicate is false. -/
theorem not_branchCostHardness_of_both_costsInRegime
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.BoundRegime)
    (h2 : T.TwoSidedABCancellationCostInRegime R)
    (h1 : T.OneSidedForcedCostInRegime P G R) :
    ¬ T.BranchCostHardness P G R := by
  intro hhard
  rcases hhard with htwo | hone
  · exact (T.not_twoSidedABCancellationHardness_of_costInRegime R h2) htwo
  · exact (T.not_oneSidedForcedCLiftHardness_of_costInRegime P G R h1) hone

end ABCTriple
end ABD2
