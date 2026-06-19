import ABD.ABD2.Cost.HardnessNormalForm

namespace ABD2
namespace ABCTriple

/-- A scalar target forced by a one-sided good base point.

This definition intentionally remembers only the base-side production of the
nonzero target.  The C-lift size is separated into the next predicate. -/
def OneSidedForcedTarget
    (T : ABCTriple) (P : T.CImageProfile) (t : ℤ) : Prop :=
  t ≠ 0 ∧
    T.OneSidedABSupport ∧
      ∃ seed : T.FullTangent,
        T.GoodBasePoint P seed ∧
          T.abTarget seed = t

/-- Fixed-scalar version of the gauge one-sided forced cost.

This is the first D2 refinement: instead of saying merely that some one-sided
forced cost exists at bound `B`, we expose the forced scalar target `t`. -/
def GaugeOneSidedForcedTargetCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (t B : ℤ) : Prop :=
  t ≠ 0 ∧
    T.OneSidedABSupport ∧
      ∃ seed : T.FullTangent,
        ∃ lift : T.FullTangent,
          T.GoodBasePoint P seed ∧
            T.HasCLift seed lift ∧
              T.abTarget seed = t ∧
                T.cLinearForm lift = t ∧
                  G.small lift B

/-- A fixed-target one-sided forced cost forgets to a forced target. -/
theorem oneSidedForcedTarget_of_gaugeOneSidedForcedTargetCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {t B : ℤ}
    (h : T.GaugeOneSidedForcedTargetCostAtMost P G t B) :
    T.OneSidedForcedTarget P t := by
  rcases h with ⟨ht_ne, hside, seed, lift, hgood, _hclift, htarget, _hcLinear, _hsmall⟩
  exact ⟨ht_ne, hside, seed, hgood, htarget⟩

/-- A fixed-target one-sided forced cost forgets to the pure C-lift preimage
cost for the same scalar target. -/
theorem gaugePureForcedCLiftCostAtMost_of_gaugeOneSidedForcedTargetCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) {t B : ℤ}
    (h : T.GaugeOneSidedForcedTargetCostAtMost P G t B) :
    T.GaugePureForcedCLiftCostAtMost G t B := by
  rcases h with ⟨_ht_ne, _hside, _seed, lift, _hgood, _hclift, _htarget, hcLinear, hsmall⟩
  exact T.gaugePureForcedCLiftCostAtMost_of_witness G hcLinear hsmall

/-- The original gauge C2b cost is exactly the existence of a fixed forced
scalar target with the fixed-target C2b cost. -/
theorem gaugeOneSidedForcedCostAtMost_iff_exists_forcedTargetCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (B : ℤ) :
    T.GaugeOneSidedForcedCostAtMost P G B ↔
      ∃ t : ℤ, T.GaugeOneSidedForcedTargetCostAtMost P G t B := by
  unfold ABCTriple.GaugeOneSidedForcedCostAtMost
  unfold ABCTriple.GaugeOneSidedForcedTargetCostAtMost
  constructor
  · intro h
    rcases h with ⟨seed, lift, t, ht_ne, hside, hgood, hclift, htarget, hcLinear, hsmall⟩
    exact ⟨t, ht_ne, hside, seed, lift, hgood, hclift, htarget, hcLinear, hsmall⟩
  · intro h
    rcases h with ⟨t, ht_ne, hside, seed, lift, hgood, hclift, htarget, hcLinear, hsmall⟩
    exact ⟨seed, lift, t, ht_ne, hside, hgood, hclift, htarget, hcLinear, hsmall⟩

/-- At a fixed concrete bound, failure of the one-sided gauge C2b cost is
equivalent to failure for every forced scalar target. -/
theorem not_gaugeOneSidedForcedCostAtMost_iff_forall_target_not_cost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (B : ℤ) :
    ¬ T.GaugeOneSidedForcedCostAtMost P G B ↔
      ∀ t : ℤ, ¬ T.GaugeOneSidedForcedTargetCostAtMost P G t B := by
  rw [T.gaugeOneSidedForcedCostAtMost_iff_exists_forcedTargetCostAtMost P G B]
  constructor
  · intro hnot t ht
    exact hnot ⟨t, ht⟩
  · intro hforall h
    rcases h with ⟨t, ht⟩
    exact hforall t ht

/-- D2 hardness as forced-target failure: the one-sided base data is present,
and every accepted bound fails for every forced scalar target. -/
theorem oneSidedForcedCLiftHardness_iff_base_and_forall_accepted_forall_target_not_cost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.BoundRegime) :
    T.OneSidedForcedCLiftHardness P G R ↔
      T.OneSidedABSupport ∧
        T.HasGoodBasePoint P ∧
          ∀ B : ℤ,
            R.accepts B →
              ∀ t : ℤ, ¬ T.GaugeOneSidedForcedTargetCostAtMost P G t B := by
  constructor
  · intro hhard
    have hnorm :=
      (T.oneSidedForcedCLiftHardness_iff_base_and_forall_accepted_not_cost P G R).mp hhard
    rcases hnorm with ⟨hside, hgood, hforall⟩
    refine ⟨hside, hgood, ?_⟩
    intro B hB
    have hnot : ¬ T.GaugeOneSidedForcedCostAtMost P G B := hforall B hB
    exact (T.not_gaugeOneSidedForcedCostAtMost_iff_forall_target_not_cost P G B).mp hnot
  · intro h
    rcases h with ⟨hside, hgood, hforall⟩
    apply (T.oneSidedForcedCLiftHardness_iff_base_and_forall_accepted_not_cost P G R).mpr
    refine ⟨hside, hgood, ?_⟩
    intro B hB
    exact (T.not_gaugeOneSidedForcedCostAtMost_iff_forall_target_not_cost P G B).mpr (hforall B hB)

/-- A concrete forced-target C2b witness at an accepted bound defeats D2 hardness. -/
theorem not_oneSidedForcedCLiftHardness_of_forcedTargetCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.BoundRegime)
    {t B : ℤ}
    (hB : R.accepts B)
    (hcost : T.GaugeOneSidedForcedTargetCostAtMost P G t B) :
    ¬ T.OneSidedForcedCLiftHardness P G R := by
  intro hhard
  have hforall :=
    (T.oneSidedForcedCLiftHardness_iff_base_and_forall_accepted_forall_target_not_cost
      P G R).mp hhard
  exact hforall.2.2 B hB t hcost

/-- If some forced scalar target is realized at an accepted bound, then the
one-sided C2b cost lies in the regime. -/
theorem oneSidedForcedCostInRegime_of_forcedTargetCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) (R : T.BoundRegime)
    {t B : ℤ}
    (hB : R.accepts B)
    (hcost : T.GaugeOneSidedForcedTargetCostAtMost P G t B) :
    T.OneSidedForcedCostInRegime P G R := by
  exact T.oneSidedForcedCostInRegime_of_bound P G R hB
    ((T.gaugeOneSidedForcedCostAtMost_iff_exists_forcedTargetCostAtMost P G B).mpr ⟨t, hcost⟩)

end ABCTriple
end ABD2
