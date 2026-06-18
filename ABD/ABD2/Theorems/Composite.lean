import ABD.ABD2.Theorems.Theorem123

namespace ABD2
namespace ABCTriple

/-- ABD2 composite strengthening: under block decomposition and `1 < c`, the
existence of a strict candidate is equivalent to avoiding the concrete gcd-profile
bad seed. -/
theorem ABD2_composite_strictCandidate_iff_not_BadSeed
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.HasStrictCandidate ↔
      ¬ T.BadSeed ((T.Theorem3_cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  let W := T.Theorem3_cImageGCDWitness_of_one_lt_c hblocks hc
  exact W.hasStrictCandidate_iff_not_BadSeed hblocks

/-- Forward form of the ABD2 composite strengthening. -/
theorem ABD2_composite_hasStrictCandidate_of_not_BadSeed
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c)
    (hgood :
      ¬ T.BadSeed ((T.Theorem3_cImageGCDWitness_of_one_lt_c hblocks hc).profile)) :
    T.HasStrictCandidate := by
  exact ((T.ABD2_composite_strictCandidate_iff_not_BadSeed hblocks hc).2 hgood)

/-- Reverse obstruction form of the ABD2 composite strengthening. -/
theorem ABD2_composite_not_BadSeed_of_hasStrictCandidate
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c)
    (hstrict : T.HasStrictCandidate) :
    ¬ T.BadSeed ((T.Theorem3_cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  exact ((T.ABD2_composite_strictCandidate_iff_not_BadSeed hblocks hc).1 hstrict)

/-- Same composite criterion, expressed directly through the existing final theorem
from the reduction layer. -/
theorem ABD2_composite_matches_reduction_layer
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.HasStrictCandidate ↔
      ¬ T.BadSeed ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  exact T.hasStrictCandidate_iff_not_BadSeed_of_one_lt_c hblocks hc

end ABCTriple
end ABD2
