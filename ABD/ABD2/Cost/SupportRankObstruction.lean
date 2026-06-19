import ABD.ABD2.Cost.BezoutObstruction

namespace ABD2
namespace ABCTriple

/-- The two-sided AB rank regime: both AB support blocks are nonempty. -/
def HasTwoSidedABSupportRank (T : ABCTriple) : Prop :=
  T.supportA.Nonempty ∧ T.supportB.Nonempty

/-- The C-side rank regime: the C support block is nonempty. -/
def HasCSupportRank (T : ABCTriple) : Prop :=
  T.supportC.Nonempty

/-- AB support-rank boundary: neither the two-sided AB rank regime nor the
one-sided AB support regime applies.

This is the D3 boundary box.  It is intentionally broad: later files can split it
into `both empty`, primitive failure, support-decomposition failure, or other edge
cases. -/
def ABSupportRankBoundary (T : ABCTriple) : Prop :=
  ¬ T.HasTwoSidedABSupportRank ∧ ¬ T.OneSidedABSupport

/-- C support-rank obstruction: there is no nonempty C block on which a C-lift can
move. -/
def CSupportRankObstruction (T : ABCTriple) : Prop :=
  ¬ T.HasCSupportRank

/-- Combined support-rank obstruction for the cost-hardness layer. -/
def SupportRankObstruction (T : ABCTriple) : Prop :=
  T.ABSupportRankBoundary ∨ T.CSupportRankObstruction

/-- Having two-sided AB support rank removes the AB-boundary obstruction. -/
theorem not_ABSupportRankBoundary_of_hasTwoSidedABSupportRank
    (T : ABCTriple)
    (h : T.HasTwoSidedABSupportRank) :
    ¬ T.ABSupportRankBoundary := by
  intro hb
  exact hb.1 h

/-- Being in the one-sided AB regime removes the AB-boundary obstruction. -/
theorem not_ABSupportRankBoundary_of_oneSidedABSupport
    (T : ABCTriple)
    (h : T.OneSidedABSupport) :
    ¬ T.ABSupportRankBoundary := by
  intro hb
  exact hb.2 h

/-- Empty A and empty B support put the triple in the AB support-rank boundary. -/
theorem ABSupportRankBoundary_of_supportA_eq_empty_of_supportB_eq_empty
    (T : ABCTriple)
    (hA : T.supportA = ∅) (hB : T.supportB = ∅) :
    T.ABSupportRankBoundary := by
  have hAnot : ¬ T.supportA.Nonempty := by
    rw [hA]
    simp
  have hBnot : ¬ T.supportB.Nonempty := by
    rw [hB]
    simp
  constructor
  · intro htwo
    exact hAnot htwo.1
  · intro hside
    rcases hside with hleft | hright
    · exact hBnot hleft.2
    · exact hAnot hright.2

/-- Empty C support gives a C support-rank obstruction. -/
theorem CSupportRankObstruction_of_supportC_eq_empty
    (T : ABCTriple)
    (hC : T.supportC = ∅) :
    T.CSupportRankObstruction := by
  intro hnonempty
  simp [ABCTriple.HasCSupportRank, hC] at hnonempty

/-- Nonempty C support removes the C support-rank obstruction. -/
theorem not_CSupportRankObstruction_of_hasCSupportRank
    (T : ABCTriple)
    (h : T.HasCSupportRank) :
    ¬ T.CSupportRankObstruction := by
  intro hobs
  exact hobs h

/-- If the AB branch is not boundary and the C block has rank, then there is no
support-rank obstruction. -/
theorem not_supportRankObstruction_of_not_AB_boundary_of_hasCSupportRank
    (T : ABCTriple)
    (hAB : ¬ T.ABSupportRankBoundary)
    (hC : T.HasCSupportRank) :
    ¬ T.SupportRankObstruction := by
  intro h
  rcases h with hABobs | hCobs
  · exact hAB hABobs
  · exact hCobs hC

/-- Two-sided AB support plus nonempty C support removes the support-rank
obstruction. -/
theorem not_supportRankObstruction_of_twoSidedAB_and_C
    (T : ABCTriple)
    (hAB : T.HasTwoSidedABSupportRank)
    (hC : T.HasCSupportRank) :
    ¬ T.SupportRankObstruction := by
  exact T.not_supportRankObstruction_of_not_AB_boundary_of_hasCSupportRank
    (T.not_ABSupportRankBoundary_of_hasTwoSidedABSupportRank hAB) hC

/-- One-sided AB support plus nonempty C support removes the support-rank
obstruction. -/
theorem not_supportRankObstruction_of_oneSidedAB_and_C
    (T : ABCTriple)
    (hAB : T.OneSidedABSupport)
    (hC : T.HasCSupportRank) :
    ¬ T.SupportRankObstruction := by
  exact T.not_supportRankObstruction_of_not_AB_boundary_of_hasCSupportRank
    (T.not_ABSupportRankBoundary_of_oneSidedABSupport hAB) hC

end ABCTriple
end ABD2
