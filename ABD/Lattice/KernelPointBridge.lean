import ABD.Lattice.SupportPairCard
import ABD.Lattice.PastenKernelExistence

namespace ABD

/-- Convert a general small additive-kernel point on a triple support into the
existing triple-specialized small nondegenerate kernel point package. -/
def SmallAdditiveKernelPoint.toSmallNondegenerateKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : SmallAdditiveKernelPoint T.support T.a T.b T.c B) :
    SmallNondegenerateKernelPoint T B where
  x := h.x
  mem_kernel := by
    exact (mem_tripleAdditiveKernelSubmodule_iff T h.x).2
      ((mem_additiveKernelSubmodule_iff T.support h.x T.a T.b T.c).1 h.mem_kernel)
  nondegenerate := h.nondegenerate
  small := h.small

/-- Convert the existing triple-specialized small nondegenerate kernel point
package back to the general additive-kernel point package. -/
def SmallNondegenerateKernelPoint.toSmallAdditiveKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : SmallNondegenerateKernelPoint T B) :
    SmallAdditiveKernelPoint T.support T.a T.b T.c B where
  x := h.x
  mem_kernel := by
    exact (mem_additiveKernelSubmodule_iff T.support h.x T.a T.b T.c).2
      ((mem_tripleAdditiveKernelSubmodule_iff T h.x).1 h.mem_kernel)
  nondegenerate := h.nondegenerate
  small := h.small

/-- A bundled small nondegenerate kernel point gives the corresponding existence
predicate. -/
theorem SmallNondegenerateKernelPoint.hasSmallNondegenerateKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : SmallNondegenerateKernelPoint T B) :
    HasSmallNondegenerateKernelPoint T B := by
  exact ⟨h.x, h.mem_kernel, h.nondegenerate, h.small⟩

/-- A general small additive-kernel point on a triple support gives the existing
triple-specialized existence predicate. -/
theorem SmallAdditiveKernelPoint.hasSmallNondegenerateKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : SmallAdditiveKernelPoint T.support T.a T.b T.c B) :
    HasSmallNondegenerateKernelPoint T B := by
  exact h.toSmallNondegenerateKernelPoint.hasSmallNondegenerateKernelPoint

/-- A triple small kernel point produced by the pre-Siegel construction gives the
existing small nondegenerate kernel-point existence predicate. -/
theorem hasSmallNondegenerateKernelPoint_of_smallTripleKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : SmallTripleKernelPoint T B) :
    HasSmallNondegenerateKernelPoint T B := by
  exact h.hasSmallNondegenerateKernelPoint

/-- A triple small kernel point also gives the existing small Pasten-candidate
existence predicate. -/
theorem hasSmallPastenCandidate_of_smallTripleKernelPoint
    {T : ABCTriple} {B : ℤ}
    (h : SmallTripleKernelPoint T B) :
    HasSmallPastenCandidate T B := by
  exact hasSmallPastenCandidate_of_hasSmallNondegenerateKernelPoint
    (hasSmallNondegenerateKernelPoint_of_smallTripleKernelPoint h)

/-- The pre-Siegel construction from an explicit triple support pair, packaged in
the existing small nondegenerate kernel-point structure. -/
def smallNondegenerateKernelPoint_of_tripleSupportPair
    (T : ABCTriple) (P : TripleSupportPair T) :
    Σ B : ℤ, SmallNondegenerateKernelPoint T B := by
  let h := smallTripleKernelPoint_of_supportPair T P
  exact ⟨h.1, h.2.toSmallNondegenerateKernelPoint⟩

/-- Existence form of the triple-support-pair construction. -/
theorem exists_hasSmallNondegenerateKernelPoint_of_tripleSupportPair
    (T : ABCTriple) (P : TripleSupportPair T) :
    ∃ B : ℤ, HasSmallNondegenerateKernelPoint T B := by
  let h := smallNondegenerateKernelPoint_of_tripleSupportPair T P
  exact ⟨h.1, h.2.hasSmallNondegenerateKernelPoint⟩

/-- Pasten-candidate existence form of the triple-support-pair construction. -/
theorem exists_hasSmallPastenCandidate_of_tripleSupportPair
    (T : ABCTriple) (P : TripleSupportPair T) :
    ∃ B : ℤ, HasSmallPastenCandidate T B := by
  rcases exists_hasSmallNondegenerateKernelPoint_of_tripleSupportPair T P with
    ⟨B, hB⟩
  exact ⟨B, hasSmallPastenCandidate_of_hasSmallNondegenerateKernelPoint hB⟩

/-- If the support of a triple has cardinality at least two, the pre-Siegel
construction produces a small nondegenerate kernel point. -/
noncomputable def smallNondegenerateKernelPoint_of_tripleSupport_card_two
    (T : ABCTriple) (hcard : 2 ≤ T.support.card) :
    Σ B : ℤ, SmallNondegenerateKernelPoint T B :=
  smallNondegenerateKernelPoint_of_tripleSupportPair T
    (supportPairOfCardTwo T.support hcard)

/-- Existence form from the cardinality condition `2 ≤ T.support.card`. -/
theorem exists_hasSmallNondegenerateKernelPoint_of_tripleSupport_card_two
    (T : ABCTriple) (hcard : 2 ≤ T.support.card) :
    ∃ B : ℤ, HasSmallNondegenerateKernelPoint T B := by
  let h := smallNondegenerateKernelPoint_of_tripleSupport_card_two T hcard
  exact ⟨h.1, h.2.hasSmallNondegenerateKernelPoint⟩

/-- Pasten-candidate existence form from the cardinality condition
`2 ≤ T.support.card`. -/
theorem exists_hasSmallPastenCandidate_of_tripleSupport_card_two
    (T : ABCTriple) (hcard : 2 ≤ T.support.card) :
    ∃ B : ℤ, HasSmallPastenCandidate T B := by
  rcases exists_hasSmallNondegenerateKernelPoint_of_tripleSupport_card_two T hcard with
    ⟨B, hB⟩
  exact ⟨B, hasSmallPastenCandidate_of_hasSmallNondegenerateKernelPoint hB⟩

end ABD
