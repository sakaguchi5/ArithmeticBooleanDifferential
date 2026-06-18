import ABD.ABD.PastenBlock.HyperplaneKernel

namespace ABD

/-- Final wrapper for Theorem 1: for a primitive additive triple, Pasten's
additive condition is exactly the `S_a/S_b/S_c` block-balance equation under the
support-block direct-sum equivalence. -/
theorem ABCTriple.Theorem1_pastenT_iff_supportBlockBalance
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) (x : T.TangentBlocks) :
    (T.tangentBlocksEquiv (T.supportBlocksDisjoint_of_coprimeAB hcop)).symm x
        ∈ PastenT T ↔
      T.BlockBalance x := by
  exact T.pastenT_iff_blockBalance_of_coprimeAB hcop x

/-- Final wrapper for Theorem 2: for a primitive additive triple, a glued block
candidate is strict Pasten data exactly when it satisfies block balance and its
`a/b` seed avoids the Wronskian kernel hyperplane. -/
theorem ABCTriple.Theorem2_strictCandidate_iff_blockBalance_and_abKernelAvoidance
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) (x : T.TangentBlocks) :
    (T.glueBlocks x ∈ PastenT T ∧ T.PastenNondegenerate (T.glueBlocks x)) ↔
      T.BlockBalance x ∧ (x.xA, x.xB) ∉ T.ABWronskianHyperplaneSubmodule := by
  exact T.strictCandidate_iff_blockBalance_and_abKernelAvoidance
    (T.supportBlocksDisjoint_of_coprimeAB hcop) x

/-- Theorem 2 also records the exact meaning of “hyperplane”: the bad Wronskian
locus is the kernel of the restricted `S_a ⊕ S_b` Wronskian linear form. -/
theorem ABCTriple.Theorem2_hyperplane_is_kernel
    (T : ABCTriple) :
    T.ABWronskianHyperplane =
      (T.ABWronskianHyperplaneSubmodule : Set (T.ATangent × T.BTangent)) := by
  exact T.ABWronskianHyperplane_eq_submodule_carrier

/-- The properness/non-vacuity clause for Theorem 2: the Wronskian hyperplane is
proper exactly when a nondegenerate `a/b` seed exists. -/
theorem ABCTriple.Theorem2_hyperplane_proper_iff_hasABSeed
    (T : ABCTriple) :
    T.ABWronskianHyperplaneSubmodule ≠ ⊤ ↔ T.HasABNondegenerateSeed := by
  exact (T.hasABNondegenerateSeed_iff_hyperplaneSubmodule_ne_top).symm

end ABD
