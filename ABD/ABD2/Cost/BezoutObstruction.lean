import ABD.ABD2.Cost.ImageObstruction

namespace ABD2
namespace ABCTriple

/-- Fixed-bound Bezout/preimage obstruction for a scalar C-target.

The target is admitted by the C-image profile, but no gauge-small C-preimage is
available at the concrete bound `B`.  Later arithmetic files should refine this
using explicit Bezout vectors, coefficient gcds, and kernel reduction. -/
def ScalarBezoutObstructionAtBound
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (t B : ℤ) : Prop :=
  T.ScalarCImageCompatible P t ∧
    ¬ T.GaugePureForcedCLiftCostAtMost G t B

/-- Regime-level Bezout/preimage obstruction for a scalar C-target.

The target is image-compatible, but it has no C-preimage whose gauge bound is
accepted by the chosen regime. -/
def ScalarBezoutObstructionInRegime
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime) (t : ℤ) : Prop :=
  T.ScalarCImageCompatible P t ∧
    ¬ T.PureForcedCLiftCostInRegime G R t

/-- Regime-level Bezout obstruction is the same as failure at every accepted
concrete bound, once image-compatibility is separated out. -/
theorem scalarBezoutObstructionInRegime_iff_compatible_and_forall_accepted_not_cost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime) (t : ℤ) :
    T.ScalarBezoutObstructionInRegime P G R t ↔
      T.ScalarCImageCompatible P t ∧
        ∀ B : ℤ,
          R.accepts B → ¬ T.GaugePureForcedCLiftCostAtMost G t B := by
  unfold ABCTriple.ScalarBezoutObstructionInRegime
  constructor
  · intro h
    exact ⟨h.1,
      (T.not_pureForcedCLiftCostInRegime_iff_forall_accepted_not_cost G R t).mp h.2⟩
  · intro h
    exact ⟨h.1,
      (T.not_pureForcedCLiftCostInRegime_iff_forall_accepted_not_cost G R t).mpr h.2⟩

/-- A scalar target with an accepted gauge-pure C-lift has no regime-level Bezout
obstruction. -/
theorem not_scalarBezoutObstructionInRegime_of_pureForcedCLiftCostInRegime
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime) {t : ℤ}
    (hcost : T.PureForcedCLiftCostInRegime G R t) :
    ¬ T.ScalarBezoutObstructionInRegime P G R t := by
  intro hobs
  exact hobs.2 hcost

/-- A concrete accepted gauge-pure C-lift defeats the regime-level Bezout
obstruction. -/
theorem not_scalarBezoutObstructionInRegime_of_gaugePureForcedCLiftCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime) {t B : ℤ}
    (hB : R.accepts B)
    (hcost : T.GaugePureForcedCLiftCostAtMost G t B) :
    ¬ T.ScalarBezoutObstructionInRegime P G R t := by
  exact T.not_scalarBezoutObstructionInRegime_of_pureForcedCLiftCostInRegime
    P G R (T.pureForcedCLiftCostInRegime_of_bound G R hB hcost)

/-- A one-sided forced target whose scalar value is image-compatible but has no
regime-small C-preimage. -/
def OneSidedForcedTargetBezoutObstruction
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime) (t : ℤ) : Prop :=
  T.OneSidedForcedTarget P t ∧
    T.ScalarBezoutObstructionInRegime P G R t

/-- A fixed-target C2b witness at an accepted bound defeats the corresponding
forced-target Bezout obstruction. -/
theorem not_oneSidedForcedTargetBezoutObstruction_of_forcedTargetCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime) {t B : ℤ}
    (hB : R.accepts B)
    (hcost : T.GaugeOneSidedForcedTargetCostAtMost P G t B) :
    ¬ T.OneSidedForcedTargetBezoutObstruction P G R t := by
  intro hobs
  have hpure : T.GaugePureForcedCLiftCostAtMost G t B :=
    T.gaugePureForcedCLiftCostAtMost_of_gaugeOneSidedForcedTargetCostAtMost P G hcost
  exact hobs.2.2 (T.pureForcedCLiftCostInRegime_of_bound G R hB hpure)

/-- The profiled gcd itself is image-compatible.  This is the seed for later
explicit Bezout-witness constructions of a C-preimage of `P.gcd`. -/
theorem scalarCImageCompatible_gcd
    (T : ABCTriple) (P : T.CImageProfile) :
    T.ScalarCImageCompatible P P.gcd := by
  exact dvd_refl P.gcd

/-- A regime-small C-preimage of the profiled gcd is a small Bezout witness. -/
def RegimeSmallBezoutWitnessForGCD
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime) : Prop :=
  T.PureForcedCLiftCostInRegime G R P.gcd

/-- A small Bezout witness for the profiled gcd removes the gcd-target Bezout
obstruction. -/
theorem not_scalarBezoutObstructionInRegime_gcd_of_regimeSmallBezoutWitnessForGCD
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    (R : T.BoundRegime)
    (h : T.RegimeSmallBezoutWitnessForGCD P G R) :
    ¬ T.ScalarBezoutObstructionInRegime P G R P.gcd := by
  exact T.not_scalarBezoutObstructionInRegime_of_pureForcedCLiftCostInRegime
    P G R h

end ABCTriple
end ABD2
