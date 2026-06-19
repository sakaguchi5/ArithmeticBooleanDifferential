import ABD.ABD2.Stratification.ValuationProfile
import ABD.ABD2.Fibration.BadSeedInclusion

namespace ABD2
namespace ABCTriple

/-- The profile-level bad pattern written as a base-locus statement:
the compatible AB-base is contained in the Wronskian-degenerate locus. -/
def WronskianZeroOnBase (T : ABCTriple) (V : T.ValuationProfile) : Prop :=
  T.ABBase V ≤ T.BaseWronskianKernel

/-- The complementary profile-level good pattern: the compatible AB-base contains
a point outside the Wronskian-degenerate locus. -/
def WronskianNonzeroOnBase (T : ABCTriple) (V : T.ValuationProfile) : Prop :=
  ¬ T.WronskianZeroOnBase V

/-- Unfolding of the bad-pattern base inclusion. -/
theorem wronskianZeroOnBase_iff_ABBase_le_BaseWronskianKernel
    (T : ABCTriple) (V : T.ValuationProfile) :
    T.WronskianZeroOnBase V ↔ T.ABBase V ≤ T.BaseWronskianKernel := by
  rfl

/-- Phase 3 profile reading: `BadSeed` is exactly Wronskian-vanishing on the
compatible AB-base. -/
theorem badSeed_iff_wronskianZeroOnBase
    (T : ABCTriple) (V : T.ValuationProfile) :
    T.BadSeed V ↔ T.WronskianZeroOnBase V := by
  unfold WronskianZeroOnBase
  exact T.badSeed_iff_ABBase_le_BaseWronskianKernel V

/-- The base obstruction is the same Wronskian-zero-on-base pattern. -/
theorem baseObstruction_iff_wronskianZeroOnBase
    (T : ABCTriple) (V : T.ValuationProfile) :
    T.BaseObstruction V ↔ T.WronskianZeroOnBase V := by
  unfold WronskianZeroOnBase
  exact T.baseObstruction_iff_ABBase_le_BaseWronskianKernel V

/-- The nonzero-on-base condition is exactly failure of `BadSeed`. -/
theorem wronskianNonzeroOnBase_iff_not_BadSeed
    (T : ABCTriple) (V : T.ValuationProfile) :
    T.WronskianNonzeroOnBase V ↔ ¬ T.BadSeed V := by
  constructor
  · intro hnonzero hbad
    exact hnonzero ((T.badSeed_iff_wronskianZeroOnBase V).1 hbad)
  · intro hnotbad hzero
    exact hnotbad ((T.badSeed_iff_wronskianZeroOnBase V).2 hzero)

/-- A good base point exists exactly when the profile is Wronskian-nonzero on the
compatible AB-base. -/
theorem hasGoodBasePoint_iff_wronskianNonzeroOnBase
    (T : ABCTriple) (V : T.ValuationProfile) :
    T.HasGoodBasePoint V ↔ T.WronskianNonzeroOnBase V := by
  constructor
  · intro hgood
    exact (T.wronskianNonzeroOnBase_iff_not_BadSeed V).2
      ((T.hasGoodBasePoint_iff_not_BadSeed V).1 hgood)
  · intro hnonzero
    exact (T.hasGoodBasePoint_iff_not_BadSeed V).2
      ((T.wronskianNonzeroOnBase_iff_not_BadSeed V).1 hnonzero)

/-- A support-stratified bad-seed pattern: the triple lies in the chosen support
stratum, and the chosen valuation profile is Wronskian-zero on the compatible
AB-base. -/
def BadSeedPatternInStratum
    (T : ABCTriple) (σ : SupportStratum) (V : T.ValuationProfile) : Prop :=
  T.InSupportStratum σ ∧ T.WronskianZeroOnBase V

/-- A support-stratified good-seed pattern: the triple lies in the chosen support
stratum, and the chosen valuation profile has a nondegenerate compatible base
point. -/
def GoodSeedPatternInStratum
    (T : ABCTriple) (σ : SupportStratum) (V : T.ValuationProfile) : Prop :=
  T.InSupportStratum σ ∧ T.WronskianNonzeroOnBase V

/-- A realized support/valuation bad pattern.  This is the classification form
used after a valuation profile has been shown to describe the actual C-image. -/
def RealizedBadSeedPatternInStratum
    (T : ABCTriple) (σ : SupportStratum) (V : T.ValuationProfile) : Prop :=
  T.InSupportStratum σ ∧ T.ValuationProfileRealized V ∧ T.WronskianZeroOnBase V

/-- A realized support/valuation good pattern. -/
def RealizedGoodSeedPatternInStratum
    (T : ABCTriple) (σ : SupportStratum) (V : T.ValuationProfile) : Prop :=
  T.InSupportStratum σ ∧ T.ValuationProfileRealized V ∧ T.WronskianNonzeroOnBase V

/-- The stratified bad pattern is just `BadSeed` plus support-stratum membership. -/
theorem badSeedPatternInStratum_iff_inSupportStratum_and_BadSeed
    (T : ABCTriple) (σ : SupportStratum) (V : T.ValuationProfile) :
    T.BadSeedPatternInStratum σ V ↔ T.InSupportStratum σ ∧ T.BadSeed V := by
  constructor
  · intro h
    exact ⟨h.1, (T.badSeed_iff_wronskianZeroOnBase V).2 h.2⟩
  · intro h
    exact ⟨h.1, (T.badSeed_iff_wronskianZeroOnBase V).1 h.2⟩

/-- The stratified good pattern is just good-base existence plus support-stratum
membership. -/
theorem goodSeedPatternInStratum_iff_inSupportStratum_and_hasGoodBasePoint
    (T : ABCTriple) (σ : SupportStratum) (V : T.ValuationProfile) :
    T.GoodSeedPatternInStratum σ V ↔ T.InSupportStratum σ ∧ T.HasGoodBasePoint V := by
  constructor
  · intro h
    exact ⟨h.1, (T.hasGoodBasePoint_iff_wronskianNonzeroOnBase V).2 h.2⟩
  · intro h
    exact ⟨h.1, (T.hasGoodBasePoint_iff_wronskianNonzeroOnBase V).1 h.2⟩

/-- Realized bad patterns are exactly realized valuation profiles whose profile is
`BadSeed`, together with support-stratum membership. -/
theorem realizedBadSeedPatternInStratum_iff
    (T : ABCTriple) (σ : SupportStratum) (V : T.ValuationProfile) :
    T.RealizedBadSeedPatternInStratum σ V ↔
      T.InSupportStratum σ ∧ T.ValuationProfileRealized V ∧ T.BadSeed V := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, (T.badSeed_iff_wronskianZeroOnBase V).2 h.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, (T.badSeed_iff_wronskianZeroOnBase V).1 h.2.2⟩

/-- Realized good patterns are exactly realized valuation profiles with a good
base point, together with support-stratum membership. -/
theorem realizedGoodSeedPatternInStratum_iff
    (T : ABCTriple) (σ : SupportStratum) (V : T.ValuationProfile) :
    T.RealizedGoodSeedPatternInStratum σ V ↔
      T.InSupportStratum σ ∧ T.ValuationProfileRealized V ∧ T.HasGoodBasePoint V := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, (T.hasGoodBasePoint_iff_wronskianNonzeroOnBase V).2 h.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, (T.hasGoodBasePoint_iff_wronskianNonzeroOnBase V).1 h.2.2⟩

/-- On the canonical support stratum of `T`, the stratified bad pattern is just
the profile-level `BadSeed` predicate. -/
theorem badSeedPattern_self_iff_BadSeed
    (T : ABCTriple) (V : T.ValuationProfile) :
    T.BadSeedPatternInStratum T.supportStratum V ↔ T.BadSeed V := by
  constructor
  · intro h
    exact (T.badSeed_iff_wronskianZeroOnBase V).2 h.2
  · intro h
    exact ⟨T.inSupportStratum_self, (T.badSeed_iff_wronskianZeroOnBase V).1 h⟩

/-- On the canonical support stratum of `T`, the stratified good pattern is just
good-base existence. -/
theorem goodSeedPattern_self_iff_hasGoodBasePoint
    (T : ABCTriple) (V : T.ValuationProfile) :
    T.GoodSeedPatternInStratum T.supportStratum V ↔ T.HasGoodBasePoint V := by
  constructor
  · intro h
    exact (T.hasGoodBasePoint_iff_wronskianNonzeroOnBase V).2 h.2
  · intro h
    exact ⟨T.inSupportStratum_self, (T.hasGoodBasePoint_iff_wronskianNonzeroOnBase V).1 h⟩

/-- Canonical realized bad pattern = realized valuation profile plus `BadSeed`. -/
theorem realizedBadSeedPattern_self_iff
    (T : ABCTriple) (V : T.ValuationProfile) :
    T.RealizedBadSeedPatternInStratum T.supportStratum V ↔
      T.ValuationProfileRealized V ∧ T.BadSeed V := by
  constructor
  · intro h
    exact ⟨h.2.1, (T.badSeed_iff_wronskianZeroOnBase V).2 h.2.2⟩
  · intro h
    exact ⟨T.inSupportStratum_self, h.1,
      (T.badSeed_iff_wronskianZeroOnBase V).1 h.2⟩

/-- Canonical realized good pattern = realized valuation profile plus good-base
existence. -/
theorem realizedGoodSeedPattern_self_iff
    (T : ABCTriple) (V : T.ValuationProfile) :
    T.RealizedGoodSeedPatternInStratum T.supportStratum V ↔
      T.ValuationProfileRealized V ∧ T.HasGoodBasePoint V := by
  constructor
  · intro h
    exact ⟨h.2.1, (T.hasGoodBasePoint_iff_wronskianNonzeroOnBase V).2 h.2.2⟩
  · intro h
    exact ⟨T.inSupportStratum_self, h.1,
      (T.hasGoodBasePoint_iff_wronskianNonzeroOnBase V).1 h.2⟩

end ABCTriple
end ABD2
