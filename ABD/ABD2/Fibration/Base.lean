import ABD.ABD2.Reduction.ABCompatible

namespace ABD2
namespace ABCTriple

/-- The AB-side base lattice of the ABD2 fibration.

This is only a conceptual alias for the existing compatible submodule: the base
points are full tangents whose A/B target is compatible with the chosen C-image
profile. -/
abbrev ABBase (T : ABCTriple) (P : T.CImageProfile) : Submodule ℤ T.FullTangent :=
  T.ABCompatibleSubmodule P

@[simp]
theorem mem_ABBase_iff
    (T : ABCTriple) (P : T.CImageProfile) (x : T.FullTangent) :
    x ∈ T.ABBase P ↔ P.gcd ∣ T.abTarget x := by
  rfl

/-- The Wronskian-degenerate locus in the AB base. -/
abbrev BaseWronskianKernel (T : ABCTriple) : Submodule ℤ T.FullTangent :=
  T.ABWronskianKernel

@[simp]
theorem mem_BaseWronskianKernel_iff
    (T : ABCTriple) (x : T.FullTangent) :
    x ∈ T.BaseWronskianKernel ↔ T.Wronskian x = 0 := by
  rfl

/-- A good base point is a compatible AB seed outside the Wronskian kernel. -/
def GoodBasePoint (T : ABCTriple) (P : T.CImageProfile) (x : T.FullTangent) : Prop :=
  x ∈ T.ABBase P ∧ x ∉ T.BaseWronskianKernel

@[simp]
theorem goodBasePoint_iff
    (T : ABCTriple) (P : T.CImageProfile) (x : T.FullTangent) :
    T.GoodBasePoint P x ↔
      x ∈ T.ABCompatibleSubmodule P ∧ x ∉ T.ABWronskianKernel := by
  rfl

/-- Existence of a good base point. -/
def HasGoodBasePoint (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∃ x : T.FullTangent, T.GoodBasePoint P x

/-- The fibration-language base condition is exactly the existing good-seed
condition. -/
theorem hasGoodBasePoint_iff_hasGoodABSeed
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasGoodBasePoint P ↔ T.HasGoodABSeed P := by
  rfl

/-- The qualitative base obstruction is precisely `BadSeed`. -/
theorem hasGoodBasePoint_iff_not_BadSeed
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasGoodBasePoint P ↔ ¬ T.BadSeed P := by
  exact (T.hasGoodBasePoint_iff_hasGoodABSeed P).trans
    (T.hasGoodABSeed_iff_not_BadSeed P)

end ABCTriple
end ABD2
