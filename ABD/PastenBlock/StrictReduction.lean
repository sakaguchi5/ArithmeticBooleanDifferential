import ABD.PastenBlock.ABCompatible
import ABD.PastenBlock.HyperplaneKernel

namespace ABD

/-- Strict Pasten candidates are exactly nondegenerate gcd-compatible `a/b` seeds,
under the usual primitive hypothesis.

This is the smallness-free second-stage normal form: Theorems 1--3 eliminate the
`c` block from the existence problem, leaving only a Wronskian-kernel avoidance
condition and one gcd divisibility condition on the `a/b` seed. -/
theorem ABCTriple.hasStrictPastenCandidate_iff_hasNondegenerateGCDCompatibleABSeed
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) :
    HasStrictPastenCandidate T ↔ T.HasNondegenerateGCDCompatibleABSeed := by
  constructor
  · intro h
    rcases h with ⟨x, hT, hnd⟩
    refine ⟨T.restrictA x, T.restrictB x, ?_, ?_⟩
    · exact (T.pastenNondegenerate_iff_restrictAB_not_mem_hyperplaneSubmodule x).1 hnd
    · have hadj : T.CAdjustable (T.restrictA x) (T.restrictB x) :=
        T.cAdjustable_of_mem_pastenT hT
      exact (T.cAdjustable_iff_cCoeffGCD_dvd_abSeedTarget
        (T.restrictA x) (T.restrictB x)).1 hadj
  · intro h
    rcases h with ⟨xA, xB, hnot, hdiv⟩
    rcases T.cAdjustmentLift_of_cCoeffGCD_dvd_abSeedTarget
        (xA := xA) (xB := xB) hdiv with ⟨lift⟩
    let blocks : T.TangentBlocks :=
      { xA := xA
        xB := xB
        xC := lift.xC }
    have hdisj : T.SupportBlocksDisjoint :=
      T.supportBlocksDisjoint_of_coprimeAB hcop
    have hbalance : T.BlockBalance blocks := by
      unfold ABCTriple.BlockBalance
      have hadj := lift.adjusts
      unfold ABCTriple.cLinearForm ABCTriple.abSeedTarget at hadj
      simpa [blocks] using hadj.symm
    have hmem : T.glueBlocks blocks ∈ PastenT T :=
      (T.glueBlocks_mem_pastenT_iff_blockBalance hdisj blocks).2 hbalance
    have hnd : T.PastenNondegenerate (T.glueBlocks blocks) :=
      (T.glueBlocks_pastenNondegenerate_iff_ab_not_mem_hyperplaneSubmodule
        hdisj blocks).2 (by simpa [blocks] using hnot)
    exact ⟨T.glueBlocks blocks, hmem, hnd⟩

/-- Equivalent form using the first bad-pattern predicate. -/
theorem ABCTriple.hasStrictPastenCandidate_iff_ABGCDWronskianNondegenerate
    (T : ABCTriple) (hcop : Nat.Coprime T.a T.b) :
    HasStrictPastenCandidate T ↔ T.ABGCDWronskianNondegenerate := by
  rw [T.hasStrictPastenCandidate_iff_hasNondegenerateGCDCompatibleABSeed hcop]
  exact T.hasNondegenerateGCDCompatibleABSeed_iff_not_ABGCDWronskianDegenerate

end ABD
