import ABD.ABD2.Reduction.ABCompatible
import ABD.ABD2.Reduction.CImage

namespace ABD2
namespace ABCTriple

/-- A full tangent vector is C-pure when its A/B masks vanish.

This keeps ABD2's C-image theorem genuinely mask-based: the C-image is represented
by vectors which carry only C-side information, while still living in the full
`ℤ^S` tangent module. -/
def IsCPure (T : ABCTriple) (x : T.FullTangent) : Prop :=
  T.maskA x = 0 ∧ T.maskB x = 0

/-- The C-image as the set of values attained by the C-linear form on C-pure
full tangents.

This is the ABD2 analogue of the old C-side image, but it is deliberately stated
inside the Boolean-mask full module rather than in a separate `CTangent` module. -/
def CImage (T : ABCTriple) : Set ℤ :=
  {target | ∃ x : T.FullTangent, T.IsCPure x ∧ T.cLinearForm x = target}

@[simp]
theorem mem_CImage_iff
    (T : ABCTriple) (target : ℤ) :
    target ∈ T.CImage ↔
      ∃ x : T.FullTangent, T.IsCPure x ∧ T.cLinearForm x = target := by
  rfl

/-- A C-image profile is correct when its gcd describes exactly the C-image.

The future `cCoeffGCDProfile` should be proved to satisfy this predicate. -/
def ProfileRealizesCImage (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∀ target : ℤ, target ∈ T.CImage ↔ P.gcd ∣ target

/-- Under a realized profile, profile-compatibility of a seed is exactly saying
that its AB target lies in the C-image. -/
theorem cProfileCompatible_iff_abTarget_mem_CImage
    (T : ABCTriple) (P : T.CImageProfile) (x : T.FullTangent)
    (hreal : T.ProfileRealizesCImage P) :
    T.CProfileCompatible P x ↔ T.abTarget x ∈ T.CImage := by
  unfold CProfileCompatible
  exact (hreal (T.abTarget x)).symm

/-- Membership in the AB-compatible submodule gives C-image membership, once the
profile is known to realize the C-image. -/
theorem abTarget_mem_CImage_of_mem_ABCompatibleSubmodule
    (T : ABCTriple) (P : T.CImageProfile) (x : T.FullTangent)
    (hreal : T.ProfileRealizesCImage P)
    (hx : x ∈ T.ABCompatibleSubmodule P) :
    T.abTarget x ∈ T.CImage := by
  exact (T.cProfileCompatible_iff_abTarget_mem_CImage P x hreal).1 hx

end ABCTriple
end ABD2
