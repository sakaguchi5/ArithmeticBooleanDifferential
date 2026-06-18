import ABD.ABD2.Pasten.PastenT

namespace ABD2
namespace ABCTriple

/-- Theorem 1, ABD2 surface form: Pasten additivity on the full Boolean support is
exactly the A/B/C block-balance equation. -/
theorem Theorem1_additiveOn_iff_blockBalance
    (T : ABCTriple) (x : T.FullTangent) :
    T.AdditiveOn x ↔ T.BlockBalance x := by
  exact T.additiveOn_iff_blockBalance x

/-- Theorem 1, membership form: the Pasten tangent set is the block-balance
predicate. -/
theorem Theorem1_pastenT_iff_blockBalance
    (T : ABCTriple) (x : T.FullTangent) :
    x ∈ T.PastenT ↔ T.BlockBalance x := by
  exact T.mem_PastenT_iff_blockBalance x

end ABCTriple
end ABD2
