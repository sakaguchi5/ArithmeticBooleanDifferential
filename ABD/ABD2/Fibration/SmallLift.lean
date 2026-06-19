import ABD.ABD2.Fibration.Obstruction
import ABD.ABD2.Reduction.SmallBlockLift

namespace ABD2
namespace ABCTriple

/-- A small point in the C-fiber over a fixed seed. -/
def SmallFiberPoint
    (T : ABCTriple) (seed lift : T.FullTangent) (B : ℤ) : Prop :=
  lift ∈ T.FiberOver seed ∧ T.SmallTangent lift B

/-- The C-fiber over a seed contains a point satisfying the coordinate gauge `B`. -/
def HasSmallFiberOver
    (T : ABCTriple) (seed : T.FullTangent) (B : ℤ) : Prop :=
  ∃ lift : T.FullTangent, T.SmallFiberPoint seed lift B

/-- Fixed-seed small block lift = good base point + small fiber point. -/
theorem hasSmallBlockLiftForSeed_iff_goodBasePoint_and_smallFiber
    (T : ABCTriple) (P : T.CImageProfile) {seed : T.FullTangent} {B : ℤ} :
    T.HasSmallBlockLiftForSeed P seed B ↔
      T.GoodBasePoint P seed ∧ T.HasSmallFiberOver seed B := by
  constructor
  · intro h
    rcases h with ⟨hcompatible, hnondegenerate, lift, hlift, hsmall⟩
    exact ⟨⟨hcompatible, hnondegenerate⟩, ⟨lift, hlift, hsmall⟩⟩
  · intro h
    rcases h with ⟨⟨hcompatible, hnondegenerate⟩, ⟨lift, hlift, hsmall⟩⟩
    exact ⟨hcompatible, hnondegenerate, lift, hlift, hsmall⟩

/-- Existence of a small section over some good base point. -/
def SmallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) : Prop :=
  ∃ seed : T.FullTangent,
    T.GoodBasePoint P seed ∧ T.HasSmallFiberOver seed B

/-- Small section existence is the fibration reading of `HasSmallBlockLift`. -/
theorem smallSectionExists_iff_hasSmallBlockLift
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ} :
    T.SmallSectionExists P B ↔ T.HasSmallBlockLift P B := by
  constructor
  · intro h
    rcases h with ⟨seed, hseed⟩
    exact ⟨seed,
      (T.hasSmallBlockLiftForSeed_iff_goodBasePoint_and_smallFiber P).2 hseed⟩
  · intro h
    rcases h with ⟨seed, hseed⟩
    exact ⟨seed,
      (T.hasSmallBlockLiftForSeed_iff_goodBasePoint_and_smallFiber P).1 hseed⟩

/-- A small section gives a small strict candidate. -/
theorem hasSmallStrictCandidate_of_smallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.SmallSectionExists P B) :
    ∃ x : T.FullTangent, T.StrictCandidate x ∧ T.SmallTangent x B := by
  have hblock : T.HasSmallBlockLift P B :=
    (T.smallSectionExists_iff_hasSmallBlockLift P).1 h
  exact T.hasSmallStrictCandidate_of_hasSmallBlockLift P hblock

end ABCTriple
end ABD2
