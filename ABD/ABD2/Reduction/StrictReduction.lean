import ABD.ABD2.Reduction.ABCompatible

namespace ABD2
namespace ABCTriple

/-- Strict Pasten candidate in ABD2's full-mask presentation. -/
def StrictCandidate (T : ABCTriple) (x : T.FullTangent) : Prop :=
  x ∈ T.PastenT ∧ T.Nondegenerate x

/-- Existence of a strict candidate. -/
def HasStrictCandidate (T : ABCTriple) : Prop :=
  ∃ x : T.FullTangent, T.StrictCandidate x


/-- If a good AB seed has a concrete C-lift, then it builds a strict candidate.

This is the ABD2 routing theorem.  The arithmetic theorem that produces `lift`
from the profile divisibility is intentionally separated. -/
theorem strictCandidate_of_goodSeed_and_cLift
    (T : ABCTriple)
    (x lift : T.FullTangent)
    (hnd : x ∉ T.ABWronskianKernel)
    (hlift : T.HasCLift x lift) :
    T.StrictCandidate lift := by
  constructor
  · exact (T.mem_PastenT_iff_blockBalance lift).2
      (T.BlockBalance_of_HasCLift x lift hlift)
  · intro hzero
    apply hnd
    rw [T.mem_ABWronskianKernel_iff]
    have hW : T.Wronskian lift = T.Wronskian x :=
      T.Wronskian_congr_AB_masks lift x hlift.maskA_eq hlift.maskB_eq
    rw [← hW]
    exact hzero

/-- If there is a nondegenerate seed admitting a C-lift,
then a strict candidate exists. -/
theorem hasStrictCandidate_of_exists_goodSeed_and_cLift
    (T : ABCTriple)
    (h : ∃ x lift : T.FullTangent,
      x ∉ T.ABWronskianKernel ∧
      T.HasCLift x lift) :
    T.HasStrictCandidate := by
  rcases h with ⟨x, lift, hnd, hlift⟩
  exact ⟨lift, T.strictCandidate_of_goodSeed_and_cLift x lift hnd hlift⟩

/-- Every compatible AB seed admits a concrete C-lift. -/
def HasCLiftForCompatibleSeeds
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∀ x : T.FullTangent,
    x ∈ T.ABCompatibleSubmodule P →
      ∃ lift : T.FullTangent, T.HasCLift x lift

/-- A nondegenerate compatible seed plus a lifting principle gives a strict candidate. -/
theorem hasStrictCandidate_of_nonzero_compatible_seed
    (T : ABCTriple) (P : T.CImageProfile)
    (hliftAll : T.HasCLiftForCompatibleSeeds P)
    (hseed : ∃ x : T.FullTangent,
      x ∈ T.ABCompatibleSubmodule P ∧
      x ∉ T.ABWronskianKernel) :
    T.HasStrictCandidate := by
  rcases hseed with ⟨x, hxcomp, hnd⟩
  rcases hliftAll x hxcomp with ⟨lift, hlift⟩
  exact ⟨lift, T.strictCandidate_of_goodSeed_and_cLift x lift hnd hlift⟩

end ABCTriple
end ABD2
