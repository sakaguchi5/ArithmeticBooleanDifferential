import ABD.ABD2.Cost.Hardness

namespace ABD2
namespace ABCTriple

/-- Normal form for D1 hardness: failing to be in a regime means that
no regime-accepted concrete bound realizes the two-sided AB-cancellation cost. -/
theorem twoSidedABCancellationHardness_iff_forall_accepted_not_cost
    (T : ABCTriple) (R : T.BoundRegime) :
    T.TwoSidedABCancellationHardness R ↔
      ∀ B : ℤ, R.accepts B → ¬ T.TwoSidedABCancellationCostAtMost B := by
  unfold ABCTriple.TwoSidedABCancellationHardness
  unfold ABCTriple.TwoSidedABCancellationCostInRegime
  constructor
  · intro hhard B hB hcost
    exact hhard ⟨B, hB, hcost⟩
  · intro hforall hreg
    rcases hreg with ⟨B, hB, hcost⟩
    exact hforall B hB hcost

/-- Normal form for failure of a fixed-target pure C-lift cost to be in a regime. -/
theorem not_pureForcedCLiftCostInRegime_iff_forall_accepted_not_cost
    (T : ABCTriple) (G : T.Gauge) (R : T.BoundRegime) (t : ℤ) :
    ¬ T.PureForcedCLiftCostInRegime G R t ↔
      ∀ B : ℤ, R.accepts B → ¬ T.GaugePureForcedCLiftCostAtMost G t B := by
  unfold ABCTriple.PureForcedCLiftCostInRegime
  constructor
  · intro hhard B hB hcost
    exact hhard ⟨B, hB, hcost⟩
  · intro hforall hreg
    rcases hreg with ⟨B, hB, hcost⟩
    exact hforall B hB hcost

/-- Normal form for D2 hardness: the one-sided structural hypotheses remain,
and every regime-accepted concrete bound fails to realize the gauge one-sided cost. -/
theorem oneSidedForcedCLiftHardness_iff_base_and_forall_accepted_not_cost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.BoundRegime) :
    T.OneSidedForcedCLiftHardness P G R ↔
      T.OneSidedABSupport ∧
        T.HasGoodBasePoint P ∧
          ∀ B : ℤ, R.accepts B → ¬ T.GaugeOneSidedForcedCostAtMost P G B := by
  unfold ABCTriple.OneSidedForcedCLiftHardness
  unfold ABCTriple.OneSidedForcedCostInRegime
  constructor
  · intro hhard
    rcases hhard with ⟨hside, hgood, hnot⟩
    refine ⟨hside, hgood, ?_⟩
    intro B hB hcost
    exact hnot ⟨B, hB, hcost⟩
  · intro h
    rcases h with ⟨hside, hgood, hforall⟩
    refine ⟨hside, hgood, ?_⟩
    intro hreg
    rcases hreg with ⟨B, hB, hcost⟩
    exact hforall B hB hcost

/-- Branch hardness in normal form: either every accepted bound fails on the
D1 cost, or the one-sided branch data is present and every accepted bound fails
on the D2 cost. -/
theorem branchCostHardness_iff_normalForm
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.BoundRegime) :
    T.BranchCostHardness P G R ↔
      (∀ B : ℤ, R.accepts B → ¬ T.TwoSidedABCancellationCostAtMost B) ∨
        (T.OneSidedABSupport ∧
          T.HasGoodBasePoint P ∧
            ∀ B : ℤ, R.accepts B → ¬ T.GaugeOneSidedForcedCostAtMost P G B) := by
  unfold ABCTriple.BranchCostHardness
  constructor
  · intro hhard
    rcases hhard with htwo | hone
    · exact Or.inl ((T.twoSidedABCancellationHardness_iff_forall_accepted_not_cost R).mp htwo)
    · exact Or.inr ((T.oneSidedForcedCLiftHardness_iff_base_and_forall_accepted_not_cost
       P G R).mp hone)
  · intro h
    rcases h with htwo | hone
    · exact Or.inl ((T.twoSidedABCancellationHardness_iff_forall_accepted_not_cost R).mpr htwo)
    · exact Or.inr ((T.oneSidedForcedCLiftHardness_iff_base_and_forall_accepted_not_cost
       P G R).mpr hone)

end ABCTriple
end ABD2
