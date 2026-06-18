import ABD.ABD2.Theorems.Theorem1
import ABD.ABD2.Theorems.Theorem2
import ABD.ABD2.Theorems.Theorem3

namespace ABD2
namespace ABCTriple

/-- ABD2 Theorem 1 index theorem: PastenT is block balance. -/
theorem Theorem123_Theorem1
    (T : ABCTriple) (x : T.FullTangent) :
    x ∈ T.PastenT ↔ T.BlockBalance x := by
  exact T.Theorem1_pastenT_iff_blockBalance x

/-- ABD2 Theorem 2 index theorem: Wronskian ignores the C block after A/B masks are
fixed. -/
theorem Theorem123_Theorem2
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) (x : T.FullTangent) :
    T.Wronskian (T.maskA x + T.maskB x + T.maskC x) =
      T.Wronskian (T.maskA x + T.maskB x) := by
  exact T.Theorem2_wronskian_ignores_C_mask hblocks x

/-- ABD2 Theorem 3 index theorem: the C-image is the multiples of the concrete
finite coefficient gcd. -/
theorem Theorem123_Theorem3
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose) :
    T.CImage = {target : ℤ | T.cCoeffFullGCD ∣ target} := by
  exact T.Theorem3_CImage_eq_cCoeffFullGCDMultiples hblocks

end ABCTriple
end ABD2
