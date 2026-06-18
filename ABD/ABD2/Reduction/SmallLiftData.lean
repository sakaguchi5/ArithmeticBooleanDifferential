import ABD.ABD2.Reduction.StrictReduction

namespace ABD2
namespace ABCTriple

/-- Coordinatewise smallness on the full tangent module. -/
def SmallTangent (T : ABCTriple) (x : T.FullTangent) (B : ℤ) : Prop :=
  ∀ p : {p : ℕ // p ∈ T.support}, -B ≤ x p ∧ x p ≤ B

/-- A small block-lift datum: this is the clean ABD2 target for future work. -/
structure SmallBlockLiftData (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) where
  seed : T.FullTangent
  lift : T.FullTangent
  compatible : seed ∈ T.ABCompatibleSubmodule P
  nondegenerateSeed : seed ∉ T.ABWronskianKernel
  liftBalance : T.HasCLift seed lift
  small : T.SmallTangent lift B

/-- Routing theorem for small strict candidates. -/
theorem hasSmallStrictCandidate_of_smallBlockLiftData
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.SmallBlockLiftData P B) :
    ∃ x : T.FullTangent, T.StrictCandidate x ∧ T.SmallTangent x B := by
  refine ⟨h.lift, ?_, h.small⟩
  exact T.strictCandidate_of_goodSeed_and_cLift
    h.seed h.lift
    h.nondegenerateSeed h.liftBalance

end ABCTriple
end ABD2
