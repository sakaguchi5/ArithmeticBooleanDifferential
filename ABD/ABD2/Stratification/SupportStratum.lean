import ABD.ABD2.Pasten.Blocks

namespace ABD2

/-- A Boolean support stratum: the three prime-support blocks viewed as data. -/
structure SupportStratum where
  A : Finset ℕ
  B : Finset ℕ
  C : Finset ℕ

namespace SupportStratum

/-- The full support attached to a stratum. -/
def support (σ : SupportStratum) : Finset ℕ :=
  σ.A ∪ σ.B ∪ σ.C

/-- The stratum is orthogonally decomposed when the three support blocks cover the
full support and are pairwise disjoint. -/
def Decomposes (σ : SupportStratum) : Prop :=
  ThreeMaskDecomposition σ.support σ.A σ.B σ.C

end SupportStratum

namespace ABCTriple

/-- The support stratum canonically attached to an ABC triple. -/
def supportStratum (T : ABCTriple) : SupportStratum where
  A := T.supportA
  B := T.supportB
  C := T.supportC

/-- A triple realizes a specified support stratum. -/
def InSupportStratum (T : ABCTriple) (σ : SupportStratum) : Prop :=
  T.supportA = σ.A ∧ T.supportB = σ.B ∧ T.supportC = σ.C

@[simp]
theorem inSupportStratum_self (T : ABCTriple) :
    T.InSupportStratum T.supportStratum := by
  simp [InSupportStratum, supportStratum]

/-- Decomposition of the canonical stratum is exactly the existing block
hypothesis. -/
theorem supportStratum_decomposes_iff_supportBlocksDecompose
    (T : ABCTriple) :
    T.supportStratum.Decomposes ↔ T.SupportBlocksDecompose := by
  rfl

end ABCTriple
end ABD2
