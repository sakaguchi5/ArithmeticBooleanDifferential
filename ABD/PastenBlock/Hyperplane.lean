import ABD.PastenBlock.BlockDirectSum
import ABD.PastenBlock.WronskianSeparation

namespace ABD

/--
The Wronskian-degenerate hyperplane on the `S_a ⊕ S_b` side.

At this stage we represent the hyperplane by its kernel equation
`restrictedABWronskian = 0`.  This is the precise support-block content needed
for the SDC decomposition: the bad Wronskian locus lives only on the `a/b`
seed side and does not mention the `c`-adjustment block. -/
def ABCTriple.ABWronskianHyperplane (T : ABCTriple) :
    Set (T.ATangent × T.BTangent) :=
  {z | T.restrictedABWronskian z.1 z.2 = 0}

@[simp]
theorem ABCTriple.mem_ABWronskianHyperplane_iff
    (T : ABCTriple) (z : T.ATangent × T.BTangent) :
    z ∈ T.ABWronskianHyperplane ↔
      T.restrictedABWronskian z.1 z.2 = 0 := by
  rfl

/-- The complement of the hyperplane is exactly the `a/b` Wronskian
nondegenerate condition. -/
theorem ABCTriple.not_mem_ABWronskianHyperplane_iff
    (T : ABCTriple) (xA : T.ATangent) (xB : T.BTangent) :
    (xA, xB) ∉ T.ABWronskianHyperplane ↔
      T.ABWronskianNondegenerate xA xB := by
  unfold ABCTriple.ABWronskianHyperplane ABCTriple.ABWronskianNondegenerate
  simp

/-- Full Pasten degeneracy is exactly membership of the restricted `a/b` seed in
that Wronskian hyperplane. -/
theorem ABCTriple.pastenDegenerate_iff_restrictAB_mem_hyperplane
    (T : ABCTriple) (x : Tangent T.support) :
    ¬ T.PastenNondegenerate x ↔
      (T.restrictA x, T.restrictB x) ∈ T.ABWronskianHyperplane := by
  rw [T.pastenNondegenerate_iff_restrictedABWronskian_ne_zero]
  unfold ABCTriple.ABWronskianHyperplane
  simp

/-- Full Pasten nondegeneracy is exactly avoidance of the `a/b` Wronskian
hyperplane. -/
theorem ABCTriple.pastenNondegenerate_iff_restrictAB_not_mem_hyperplane
    (T : ABCTriple) (x : Tangent T.support) :
    T.PastenNondegenerate x ↔
      (T.restrictA x, T.restrictB x) ∉ T.ABWronskianHyperplane := by
  rw [T.pastenNondegenerate_iff_restrictedABWronskian_ne_zero]
  unfold ABCTriple.ABWronskianHyperplane
  simp

/-- In block-normal form, a glued candidate is Pasten-nondegenerate exactly when
its `a/b` seed avoids the Wronskian hyperplane. -/
theorem ABCTriple.glueBlocks_pastenNondegenerate_iff_ab_not_mem_hyperplane
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint) (x : T.TangentBlocks) :
    T.PastenNondegenerate (T.glueBlocks x) ↔
      (x.xA, x.xB) ∉ T.ABWronskianHyperplane := by
  rw [T.pastenNondegenerate_iff_restrictAB_not_mem_hyperplane]
  rw [T.restrictA_glueBlocks hdisj]
  rw [T.restrictB_glueBlocks hdisj]

/-- A full strict Pasten candidate decomposes into block balance plus avoidance
of the `a/b` Wronskian hyperplane. -/
theorem ABCTriple.strictCandidate_iff_blockBalance_and_ab_hyperplane_avoidance
    (T : ABCTriple) (hdisj : T.SupportBlocksDisjoint) (x : T.TangentBlocks) :
    (T.glueBlocks x ∈ PastenT T ∧ T.PastenNondegenerate (T.glueBlocks x)) ↔
      T.BlockBalance x ∧ (x.xA, x.xB) ∉ T.ABWronskianHyperplane := by
  rw [T.glueBlocks_mem_pastenT_iff_blockBalance hdisj]
  rw [T.glueBlocks_pastenNondegenerate_iff_ab_not_mem_hyperplane hdisj]

end ABD
