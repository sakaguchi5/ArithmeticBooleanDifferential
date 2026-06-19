import ABD.ABD2.Cost.OneSidedHardness

namespace ABD2
namespace ABCTriple

/-- A scalar target is compatible with the profiled C-image when it is divisible by
`P.gcd`.

This is the D2-image layer: before asking for a small C-preimage, we first ask
whether the scalar target is even admitted by the C-image profile. -/
def ScalarCImageCompatible
    (T : ABCTriple) (P : T.CImageProfile) (t : ℤ) : Prop :=
  P.gcd ∣ t

/-- Image obstruction for a scalar target: the target is not admitted by the
profiled C-image. -/
def ScalarCImageObstruction
    (T : ABCTriple) (P : T.CImageProfile) (t : ℤ) : Prop :=
  ¬ T.ScalarCImageCompatible P t

@[simp]
theorem scalarCImageCompatible_iff_gcd_dvd
    (T : ABCTriple) (P : T.CImageProfile) (t : ℤ) :
    T.ScalarCImageCompatible P t ↔ P.gcd ∣ t := by
  rfl

@[simp]
theorem scalarCImageObstruction_iff_not_gcd_dvd
    (T : ABCTriple) (P : T.CImageProfile) (t : ℤ) :
    T.ScalarCImageObstruction P t ↔ ¬ P.gcd ∣ t := by
  rfl

/-- A forced target has an image obstruction if it is produced by a one-sided good
base point but is not admitted by the profiled C-image. -/
def ForcedTargetImageObstruction
    (T : ABCTriple) (P : T.CImageProfile) (t : ℤ) : Prop :=
  T.OneSidedForcedTarget P t ∧ T.ScalarCImageObstruction P t

/-- All one-sided forced targets are admitted by the C-image profile. -/
def AllForcedTargetsImageCompatible
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∀ t : ℤ, T.OneSidedForcedTarget P t → T.ScalarCImageCompatible P t

/-- No forced-target image obstruction is the same as image-compatibility for all
forced scalar targets. -/
theorem not_exists_forcedTargetImageObstruction_iff_all_forcedTargetsImageCompatible
    (T : ABCTriple) (P : T.CImageProfile) :
    (¬ ∃ t : ℤ, T.ForcedTargetImageObstruction P t) ↔
      T.AllForcedTargetsImageCompatible P := by
  unfold ABCTriple.ForcedTargetImageObstruction
  unfold ABCTriple.AllForcedTargetsImageCompatible
  unfold ABCTriple.ScalarCImageObstruction
  constructor
  · intro hno t hforced
    by_contra hnot
    exact hno ⟨t, hforced, hnot⟩
  · intro hall hbad
    rcases hbad with ⟨t, hforced, hobs⟩
    exact hobs (hall t hforced)

/-- A profile covers gauge-pure C-lift costs if every gauge-small C-preimage
witness lands in the scalar image predicted by the profile.

This is intentionally a separate bridge predicate: the later arithmetic theorem
`CImage = gcd · ℤ` should provide it. -/
def ProfileCoversGaugePureCLift
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge) : Prop :=
  ∀ {t B : ℤ},
    T.GaugePureForcedCLiftCostAtMost G t B → T.ScalarCImageCompatible P t

/-- If the profile covers gauge-pure C-lifts, an image-obstructed scalar target has
no gauge-pure C-lift at any fixed bound. -/
theorem not_gaugePureForcedCLiftCostAtMost_of_scalarCImageObstruction
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    {t B : ℤ}
    (hcover : T.ProfileCoversGaugePureCLift P G)
    (hobs : T.ScalarCImageObstruction P t) :
    ¬ T.GaugePureForcedCLiftCostAtMost G t B := by
  intro hcost
  exact hobs (hcover hcost)

/-- If the profile covers gauge-pure C-lifts, an image-obstructed scalar target has
no fixed-target one-sided forced cost at any fixed bound. -/
theorem not_gaugeOneSidedForcedTargetCostAtMost_of_scalarCImageObstruction
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    {t B : ℤ}
    (hcover : T.ProfileCoversGaugePureCLift P G)
    (hobs : T.ScalarCImageObstruction P t) :
    ¬ T.GaugeOneSidedForcedTargetCostAtMost P G t B := by
  intro hcost
  have hpure : T.GaugePureForcedCLiftCostAtMost G t B :=
    T.gaugePureForcedCLiftCostAtMost_of_gaugeOneSidedForcedTargetCostAtMost P G hcost
  exact hobs (hcover hpure)

/-- Image obstruction at a forced scalar target defeats the C2b fixed-target cost
at every bound, once the profile is known to cover gauge-pure C-lifts. -/
theorem forall_not_gaugeOneSidedForcedTargetCostAtMost_of_forcedTargetImageObstruction
    (T : ABCTriple) (P : T.CImageProfile) (G : T.Gauge)
    {t : ℤ}
    (hcover : T.ProfileCoversGaugePureCLift P G)
    (hobs : T.ForcedTargetImageObstruction P t) :
    ∀ B : ℤ, ¬ T.GaugeOneSidedForcedTargetCostAtMost P G t B := by
  intro B
  exact T.not_gaugeOneSidedForcedTargetCostAtMost_of_scalarCImageObstruction
    P G hcover hobs.2

end ABCTriple
end ABD2
