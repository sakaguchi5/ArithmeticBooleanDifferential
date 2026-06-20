import Mathlib.Data.Finset.Basic

namespace ABD3

/-- ABD3 support objects: finite sets of prime directions.

The primality invariant is intentionally not stored here.  It is supplied by
`Nat.factorization.support` in `Support.lean`. -/
abbrev Support := Finset ℕ

namespace Support

/-- Boolean zero support. -/
def zero : Support := ∅

/-- Boolean OR of supports. -/
def bor (S T : Support) : Support := S ∪ T

/-- Boolean AND of supports. -/
def band (S T : Support) : Support := S ∩ T

/-- Relative complement of supports. -/
def diff (S T : Support) : Support := S \ T

/-- Symmetric-difference support, written in elementary Boolean operations. -/
def bxor (S T : Support) : Support := (S \ T) ∪ (T \ S)

/-- Boolean disjointness of two support blocks. -/
def Disjoint (S T : Support) : Prop := S ∩ T = ∅

/-- Pairwise disjointness for three support blocks. -/
def PairwiseDisjoint3 (A B C : Support) : Prop :=
  Disjoint A B ∧ Disjoint A C ∧ Disjoint B C

/-- A support partition of a full support into three Boolean blocks. -/
def BlocksPartition (A B C Full : Support) : Prop :=
  Full = A ∪ B ∪ C ∧ PairwiseDisjoint3 A B C

@[simp] theorem bor_def (S T : Support) : bor S T = S ∪ T := rfl
@[simp] theorem band_def (S T : Support) : band S T = S ∩ T := rfl
@[simp] theorem bxor_def (S T : Support) : bxor S T = (S \ T) ∪ (T \ S) := rfl
@[simp] theorem zero_def : zero = (∅ : Support) := rfl

end Support
end ABD3
