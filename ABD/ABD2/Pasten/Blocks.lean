import ABD.ABD2.Pasten.Triple

namespace ABD2
namespace ABCTriple

/-- Boolean block decomposition predicate for the three prime supports. -/
def SupportBlocksDecompose (T : ABCTriple) : Prop :=
  ThreeMaskDecomposition T.support T.supportA T.supportB T.supportC

/-- The cover part is definitional for the chosen full support. -/
theorem support_blocks_cover (T : ABCTriple) :
    T.supportA ∪ T.supportB ∪ T.supportC = T.support := by
  rfl

/-- If the block decomposition is available, every tangent splits into its
A/B/C masked components. -/
theorem tangent_eq_ABC_masks
    (T : ABCTriple) (h : T.SupportBlocksDecompose) (x : T.FullTangent) :
    x = T.maskA x + T.maskB x + T.maskC x := by
  exact tangent_eq_three_masks T.support T.supportA T.supportB T.supportC h x

/-- A conservative constructor for block decomposition.  In later arithmetic
files, primitive triples should be used to prove the three disjointness fields. -/
def supportBlocksDecomposeOfDisjoint
    (T : ABCTriple)
    (hAB : Disjoint T.supportA T.supportB)
    (hAC : Disjoint T.supportA T.supportC)
    (hBC : Disjoint T.supportB T.supportC) :
    T.SupportBlocksDecompose where
  cover := by rfl
  disjAB := hAB
  disjAC := hAC
  disjBC := hBC

end ABCTriple
end ABD2
