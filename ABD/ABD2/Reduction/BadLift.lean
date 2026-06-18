import ABD.ABD2.Reduction.SmallBlockLift
import ABD.ABD2.Reduction.CLiftFiber

namespace ABD2
namespace ABCTriple

/-- A fixed seed is bad for the small-lift problem at bound `B` when it is a good
compatible seed but admits no small C-lift. -/
def BadLiftForSeed
    (T : ABCTriple) (P : T.CImageProfile) (seed : T.FullTangent) (B : ℤ) : Prop :=
  seed ∈ T.ABCompatibleSubmodule P ∧
    seed ∉ T.ABWronskianKernel ∧
      ¬ ∃ lift : T.FullTangent,
        T.HasCLift seed lift ∧ T.SmallTangent lift B

/-- Global bad-lift predicate: every compatible nondegenerate seed fails to have
a small C-lift at bound `B`. -/
def BadLift
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) : Prop :=
  ∀ seed : T.FullTangent,
    seed ∈ T.ABCompatibleSubmodule P →
      seed ∉ T.ABWronskianKernel →
        ¬ ∃ lift : T.FullTangent,
          T.HasCLift seed lift ∧ T.SmallTangent lift B

/-- A small block lift for a fixed seed rules out fixed-seed bad lift. -/
theorem not_BadLiftForSeed_of_hasSmallBlockLiftForSeed
    (T : ABCTriple) (P : T.CImageProfile) {seed : T.FullTangent} {B : ℤ}
    (h : T.HasSmallBlockLiftForSeed P seed B) :
    ¬ T.BadLiftForSeed P seed B := by
  intro hbad
  rcases h with ⟨_hcomp, _hnd, hexists⟩
  exact hbad.2.2 hexists

/-- `BadLift` is exactly the negation of global small-block-lift existence. -/
theorem badLift_iff_not_hasSmallBlockLift
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) :
    T.BadLift P B ↔ ¬ T.HasSmallBlockLift P B := by
  constructor
  · intro hbad hsmall
    rcases hsmall with ⟨seed, hseed⟩
    rcases hseed with ⟨hcomp, hnd, hexists⟩
    exact hbad seed hcomp hnd hexists
  · intro hnot seed hcomp hnd hexists
    apply hnot
    exact ⟨seed, hcomp, hnd, hexists⟩

/-- Existence of a small block lift rules out `BadLift`. -/
theorem not_BadLift_of_hasSmallBlockLift
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.HasSmallBlockLift P B) :
    ¬ T.BadLift P B := by
  intro hbad
  exact ((T.badLift_iff_not_hasSmallBlockLift P B).1 hbad) h

/-- Existence of a small block lift also rules out the seed-level bad pattern. -/
theorem not_BadSeed_of_hasSmallBlockLift
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.HasSmallBlockLift P B) :
    ¬ T.BadSeed P := by
  intro hbad
  rcases h with ⟨seed, hseed⟩
  rcases hseed with ⟨hcomp, hnd, _hexists⟩
  exact hnd (hbad hcomp)

end ABCTriple
end ABD2
