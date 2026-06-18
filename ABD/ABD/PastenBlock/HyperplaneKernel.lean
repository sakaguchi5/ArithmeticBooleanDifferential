import ABD.ABD.PastenBlock.DirectSumEquiv
import ABD.ABD.PastenBlock.HyperplaneLinear

namespace ABD

/-- There exists an `a/b` seed avoiding the Wronskian-degenerate kernel. -/
def ABCTriple.HasABNondegenerateSeed (T : ABCTriple) : Prop :=
  ∃ z : T.ATangent × T.BTangent,
    T.restrictedABWronskian z.1 z.2 ≠ 0

/-- The Wronskian kernel is proper when there is an `a/b` nondegenerate seed. -/
theorem ABCTriple.ABWronskianHyperplaneSubmodule_ne_top_of_hasABNondegenerateSeed
    (T : ABCTriple) (hseed : T.HasABNondegenerateSeed) :
    T.ABWronskianHyperplaneSubmodule ≠ ⊤ := by
  intro htop
  rcases hseed with ⟨z, hz⟩
  have hzmem : z ∈ T.ABWronskianHyperplaneSubmodule := by
    have : z ∈ (⊤ : Submodule ℤ (T.ATangent × T.BTangent)) := by
      simp
    simp [htop,this]
  rw [T.mem_ABWronskianHyperplaneSubmodule_iff] at hzmem
  exact hz hzmem

/-- If the Wronskian kernel is not the whole `a/b` block space, then a
nondegenerate `a/b` seed exists. -/
theorem ABCTriple.hasABNondegenerateSeed_of_ABWronskianHyperplaneSubmodule_ne_top
    (T : ABCTriple)
    (hproper : T.ABWronskianHyperplaneSubmodule ≠ ⊤) :
    T.HasABNondegenerateSeed := by
  by_contra hno
  apply hproper
  ext z
  constructor
  · intro _
    simp
  · intro _
    rw [T.mem_ABWronskianHyperplaneSubmodule_iff]
    by_contra hz
    exact hno ⟨z, hz⟩

/-- Properness of the Wronskian kernel is equivalent to existence of a
nondegenerate `a/b` seed. -/
theorem ABCTriple.hasABNondegenerateSeed_iff_hyperplaneSubmodule_ne_top
    (T : ABCTriple) :
    T.HasABNondegenerateSeed ↔ T.ABWronskianHyperplaneSubmodule ≠ ⊤ := by
  constructor
  · exact T.ABWronskianHyperplaneSubmodule_ne_top_of_hasABNondegenerateSeed
  · exact T.hasABNondegenerateSeed_of_ABWronskianHyperplaneSubmodule_ne_top

/-- Full Pasten nondegeneracy is avoidance of the linear-map kernel on the
restricted `a/b` side. -/
theorem ABCTriple.pastenNondegenerate_iff_restrictAB_not_mem_hyperplaneSubmodule
    (T : ABCTriple) (x : Tangent T.support) :
    T.PastenNondegenerate x ↔
      (T.restrictA x, T.restrictB x) ∉ T.ABWronskianHyperplaneSubmodule := by
  rw [T.pastenNondegenerate_iff_restrictedABWronskian_ne_zero]
  rw [T.mem_ABWronskianHyperplaneSubmodule_iff]

/-- In block-normal form, a glued candidate is Pasten-nondegenerate exactly when
its `a/b` seed avoids the Wronskian kernel submodule. -/
theorem ABCTriple.glueBlocks_pastenNondegenerate_iff_ab_not_mem_hyperplaneSubmodule
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint) (x : T.TangentBlocks) :
    T.PastenNondegenerate (T.glueBlocks x) ↔
      (x.xA, x.xB) ∉ T.ABWronskianHyperplaneSubmodule := by
  rw [T.pastenNondegenerate_iff_restrictAB_not_mem_hyperplaneSubmodule]
  rw [T.restrictA_glueBlocks]
  rw [T.restrictB_glueBlocks hdisj]

/-- Theorem 2 in kernel form: a strict glued candidate is exactly block balance
plus avoidance of the `a/b` Wronskian kernel. -/
theorem ABCTriple.strictCandidate_iff_blockBalance_and_abKernelAvoidance
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint) (x : T.TangentBlocks) :
    (T.glueBlocks x ∈ PastenT T ∧ T.PastenNondegenerate (T.glueBlocks x)) ↔
      T.BlockBalance x ∧ (x.xA, x.xB) ∉ T.ABWronskianHyperplaneSubmodule := by
  rw [T.glueBlocks_mem_pastenT_iff_blockBalance hdisj]
  rw [T.glueBlocks_pastenNondegenerate_iff_ab_not_mem_hyperplaneSubmodule hdisj]

end ABD
