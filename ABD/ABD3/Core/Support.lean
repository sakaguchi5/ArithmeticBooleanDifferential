import Mathlib.Data.Nat.Factorization.Basic
import ABD.ABD3.Core.ABCData
import ABD.ABD3.Core.BooleanSupport

namespace ABD3

/-- Prime support extracted from mathlib's factorization map. -/
def primeSupport (n : ℕ) : Support :=
  n.factorization.support

namespace ABCData

/-- A-side prime support. -/
def supportA (T : ABCData) : Support :=
  primeSupport T.A.val

/-- B-side prime support. -/
def supportB (T : ABCData) : Support :=
  primeSupport T.B.val

/-- C-side prime support. -/
def supportC (T : ABCData) : Support :=
  primeSupport T.C.val

/-- Full Boolean support of the triple. -/
def supportABC (T : ABCData) : Support :=
  T.supportA ∪ T.supportB ∪ T.supportC

/-- Boolean block-disjointness for the three prime supports. -/
def SupportBlocksDisjoint (T : ABCData) : Prop :=
  Support.PairwiseDisjoint3 T.supportA T.supportB T.supportC

/-- Boolean partition certificate for the triple support. -/
def SupportBlocksPartition (T : ABCData) : Prop :=
  Support.BlocksPartition T.supportA T.supportB T.supportC T.supportABC

/-- The full support is definitionally the union of the three block supports. -/
theorem supportABC_eq_union (T : ABCData) :
    T.supportABC = T.supportA ∪ T.supportB ∪ T.supportC := by
  rfl

/-- A partition is exactly block disjointness, since the union part is definitional. -/
theorem supportBlocksPartition_of_disjoint
    (T : ABCData) (h : T.SupportBlocksDisjoint) :
    T.SupportBlocksPartition := by
  exact ⟨rfl, h⟩

end ABCData
end ABD3
