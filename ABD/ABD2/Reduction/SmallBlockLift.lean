import ABD.ABD2.Reduction.SmallnessMask
import ABD.ABD2.Reduction.CFiber

namespace ABD2
namespace ABCTriple

/-- Prop-level existence of a small block lift for a fixed seed.

`HasSmallBlockLiftForSeed T P seed B` means that `seed` is compatible with the
C-image profile `P`, is Wronskian-nondegenerate, and admits some C-lift whose
full tangent vector is coordinatewise bounded by `B`.

This is an existence condition, not a data package. Concrete witness data is
recorded by `SmallBlockLiftData`.
-/
def HasSmallBlockLiftForSeed
    (T : ABCTriple) (P : T.CImageProfile) (seed : T.FullTangent) (B : ℤ) : Prop :=
  seed ∈ T.ABCompatibleSubmodule P ∧
    seed ∉ T.ABWronskianKernel ∧
      ∃ lift : T.FullTangent,
        T.HasCLift seed lift ∧ T.SmallTangent lift B

/-- A fixed-seed small block-lift existence proof gives an existential datum.

The conclusion is Prop-valued, so we can destruct the existential lift witness
without using `Classical.choose`.
-/
theorem exists_smallBlockLiftData_of_hasSmallBlockLiftForSeed
    (T : ABCTriple) (P : T.CImageProfile) {seed : T.FullTangent} {B : ℤ}
    (h : T.HasSmallBlockLiftForSeed P seed B) :
    ∃ d : T.SmallBlockLiftData P B, d.seed = seed := by
  rcases h with ⟨hcompatible, hnondegenerate, lift, hlift, hsmall⟩
  refine ⟨
    { seed := seed
      lift := lift
      compatible := hcompatible
      nondegenerateSeed := hnondegenerate
      liftBalance := hlift
      small := hsmall },
    ?_⟩
  rfl

/-- A fixed-seed small block lift routes all the way to a small strict candidate. -/
theorem hasSmallStrictCandidate_of_hasSmallBlockLiftForSeed
    (T : ABCTriple) (P : T.CImageProfile) {seed : T.FullTangent} {B : ℤ}
    (h : T.HasSmallBlockLiftForSeed P seed B) :
    ∃ x : T.FullTangent, T.StrictCandidate x ∧ T.SmallTangent x B := by
  rcases h with ⟨hcompatible, hnondegenerate, lift, hlift, hsmall⟩
  exact T.hasSmallStrictCandidate_of_smallBlockLiftData P
    { seed := seed
      lift := lift
      compatible := hcompatible
      nondegenerateSeed := hnondegenerate
      liftBalance := hlift
      small := hsmall }

/-- Existence of some seed admitting a small block lift. -/
def HasSmallBlockLift
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) : Prop :=
  ∃ seed : T.FullTangent, T.HasSmallBlockLiftForSeed P seed B

/-- Existence of some small block lift gives a small strict candidate. -/
theorem hasSmallStrictCandidate_of_hasSmallBlockLift
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.HasSmallBlockLift P B) :
    ∃ x : T.FullTangent, T.StrictCandidate x ∧ T.SmallTangent x B := by
  rcases h with ⟨seed, hseed⟩
  exact T.hasSmallStrictCandidate_of_hasSmallBlockLiftForSeed P hseed

/-- HasSmallBlockLiftForSeed は SmallBlockLiftData の存在と同じ -/
theorem hasSmallBlockLiftForSeed_iff_exists_smallBlockLiftData_seed
    (T : ABCTriple) (P : T.CImageProfile) {seed : T.FullTangent} {B : ℤ} :
    T.HasSmallBlockLiftForSeed P seed B ↔
      ∃ d : T.SmallBlockLiftData P B, d.seed = seed := by
  constructor
  · exact T.exists_smallBlockLiftData_of_hasSmallBlockLiftForSeed P
  · intro h
    rcases h with ⟨d, hd⟩
    subst hd
    exact
      ⟨d.compatible, d.nondegenerateSeed, d.lift, d.liftBalance, d.small⟩

end ABCTriple
end ABD2
