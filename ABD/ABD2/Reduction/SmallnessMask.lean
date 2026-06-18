import ABD.ABD2.Reduction.SmallLiftData

namespace ABD2
namespace ABCTriple

/-- Boolean masking does not increase coordinatewise smallness, provided the
bound is nonnegative.

The nonnegativity assumption is needed because masked-out coordinates become
`0`, and `0` is inside `[-B, B]` exactly when `0 ≤ B`. -/
theorem supportMask_preserves_SmallTangent
    (T : ABCTriple) (M : Finset ℕ) {x : T.FullTangent} {B : ℤ}
    (hB : 0 ≤ B) (hx : T.SmallTangent x B) :
    T.SmallTangent (supportMask T.support M x) B := by
  intro p
  by_cases hp : p.1 ∈ M
  · simpa [supportMask, hp] using hx p
  · have hz : supportMask T.support M x p = 0 := by
      simp [supportMask, hp]
    constructor
    · rw [hz]
      exact neg_nonpos.mpr hB
    · rw [hz]
      exact hB

/-- The A-mask preserves coordinatewise smallness. -/
theorem maskA_preserves_SmallTangent
    (T : ABCTriple) {x : T.FullTangent} {B : ℤ}
    (hB : 0 ≤ B) (hx : T.SmallTangent x B) :
    T.SmallTangent (T.maskA x) B := by
  simpa [ABCTriple.maskA] using
    T.supportMask_preserves_SmallTangent T.supportA hB hx

/-- The B-mask preserves coordinatewise smallness. -/
theorem maskB_preserves_SmallTangent
    (T : ABCTriple) {x : T.FullTangent} {B : ℤ}
    (hB : 0 ≤ B) (hx : T.SmallTangent x B) :
    T.SmallTangent (T.maskB x) B := by
  simpa [ABCTriple.maskB] using
    T.supportMask_preserves_SmallTangent T.supportB hB hx

/-- The C-mask preserves coordinatewise smallness. -/
theorem maskC_preserves_SmallTangent
    (T : ABCTriple) {x : T.FullTangent} {B : ℤ}
    (hB : 0 ≤ B) (hx : T.SmallTangent x B) :
    T.SmallTangent (T.maskC x) B := by
  simpa [ABCTriple.maskC] using
    T.supportMask_preserves_SmallTangent T.supportC hB hx

end ABCTriple
end ABD2
