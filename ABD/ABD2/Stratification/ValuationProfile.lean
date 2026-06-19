import ABD.ABD2.Stratification.SupportStratum
import ABD.ABD2.Reduction.ABCompatible
import ABD.ABD2.Reduction.RealizedProfile

namespace ABD2
namespace ABCTriple

/-- ABD2 currently records the valuation/coefficient information needed for the
C-image by a `CImageProfile`.  This alias names that object as the valuation layer
of the support-stratified fibration. -/
abbrev ValuationProfile (T : ABCTriple) : Type :=
  T.CImageProfile

/-- The gcd carried by the valuation profile. -/
def valuationGCD (T : ABCTriple) (V : T.ValuationProfile) : ℤ :=
  V.gcd

/-- Compatibility with the valuation profile: the AB target lies in the profiled
C-image lattice. -/
def CompatibleWithValuationProfile
    (T : ABCTriple) (V : T.ValuationProfile) (x : T.FullTangent) : Prop :=
  T.valuationGCD V ∣ T.abTarget x

@[simp]
theorem mem_ABCompatibleSubmodule_iff_compatibleWithValuationProfile
    (T : ABCTriple) (V : T.ValuationProfile) (x : T.FullTangent) :
    x ∈ T.ABCompatibleSubmodule V ↔
      T.CompatibleWithValuationProfile V x := by
  rfl

/-- A valuation profile is realized when it actually describes the C-image. -/
def ValuationProfileRealized (T : ABCTriple) (V : T.ValuationProfile) : Prop :=
  T.ProfileRealizesCImage V

end ABCTriple
end ABD2
