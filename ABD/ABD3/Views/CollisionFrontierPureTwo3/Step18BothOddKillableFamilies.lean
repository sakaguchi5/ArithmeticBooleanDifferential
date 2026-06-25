import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step17BothOddResidualCore

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- A family of Branch 5 residual hard-core candidates.

The point of this layer is not to partition the hard core once and for all.
Instead, later files can register many overlapping finite or empty families and
then study the residual candidates that avoid the registered families. -/
abbrev Branch5Family (T : ABCData) (P : PowerData) : Type :=
  (F : NormalForm T P) → BothOddResidualHardCore F → Prop

/-- A lightweight marker that a Branch 5 family is finite by external number
 theory input.

This intentionally does not try to formalize Lean's finite-type machinery for
all normal forms.  It is a local certificate layer: the mathematical content is
that the family can be discarded when proving finiteness of the frontier. -/
structure Branch5FiniteFamilyCertificate
    (Family : Branch5Family T P) : Prop where
  certified : True

/-- A certificate that a Branch 5 family is empty. -/
structure Branch5EmptyFamilyCertificate
    (Family : Branch5Family T P) : Prop where
  empty : ∀ (F : NormalForm T P) (K : BothOddResidualHardCore F),
    Family F K → False

/-- A fixed prime-pair fiber: the base primes are prescribed. -/
def Branch5FixedPrimePairFamily
    (p q : ℕ) : Branch5Family T P :=
  fun F _K => F.p = p ∧ F.q = q

/-- A bounded-prime family: at least one base prime lies below a fixed bound. -/
def Branch5BoundedPrimeFamily
    (B : ℕ) : Branch5Family T P :=
  fun F _K => F.p ≤ B ∨ F.q ≤ B

/-- A finite-support prime family: both base primes belong to a prescribed
finite set. -/
def Branch5FinitePrimeSupportFamily
    (S : Finset ℕ) : Branch5Family T P :=
  fun F _K => F.p ∈ S ∧ F.q ∈ S

/-- A concrete residue-signature fiber at modulus `m`.

The three residues are those stored in the arbitrary-modulus residue signature:
`p^u`, `q^v`, and `2^w` modulo `m`. -/
def Branch5ResidueSignatureFamily
    (m rp rq rrhs : ℕ) : Branch5Family T P :=
  fun _F K =>
    (K.residues.arbitrary m).signature.p_pow_residue = rp ∧
    (K.residues.arbitrary m).signature.q_pow_residue = rq ∧
    (K.residues.arbitrary m).signature.rhs_residue = rrhs

/-- A multiplicative unbalanced family.

`C` is a scale parameter.  For `1 < C`, this says that one source term is at
least `C` times the other source term.  This is the natural integer proxy for
`|u log p - v log q|` being large, avoiding real logarithms in the first API. -/
def Branch5ScaleUnbalancedBy
    (C : ℕ) : Branch5Family T P :=
  fun F _K =>
    1 < C ∧
      (F.p ^ F.u * C ≤ F.q ^ F.v ∨
       F.q ^ F.v * C ≤ F.p ^ F.u)

/-- A multiplicative balanced family.

For `1 < C`, the two source terms are within a factor `C` of each other. -/
def Branch5ScaleBalancedBy
    (C : ℕ) : Branch5Family T P :=
  fun F _K =>
    1 < C ∧
      F.p ^ F.u ≤ C * F.q ^ F.v ∧
      F.q ^ F.v ≤ C * F.p ^ F.u

/-- A crude exponent-asymmetry family.

Since PureTwo3 normalizes the prime order by `p < q`, this predicate records
that one exponent is much larger than the other.  It is deliberately independent
from the scale-balanced/unbalanced split: exponent asymmetry can occur on either
side of that split. -/
def Branch5ExponentAsymmetricBy
    (L : ℕ) : Branch5Family T P :=
  fun F _K =>
    1 < L ∧
      (L * F.v ≤ F.u ∨ L * F.u ≤ F.v)

/-- The part of the one-sided/asymmetric region that is also scale-unbalanced.
This is one of the plausible finite subfamilies. -/
def Branch5AsymmetricUnbalancedBy
    (L C : ℕ) : Branch5Family T P :=
  fun F K =>
    Branch5ExponentAsymmetricBy (T := T) (P := P) L F K ∧
    Branch5ScaleUnbalancedBy (T := T) (P := P) C F K

/-- Union of two registered families. -/
def Branch5Family.or
    (A B : Branch5Family T P) : Branch5Family T P :=
  fun F K => A F K ∨ B F K

/-- An indexed union of registered families. -/
def Branch5Family.iUnion
    {ι : Sort _} (A : ι → Branch5Family T P) : Branch5Family T P :=
  fun F K => ∃ i : ι, A i F K

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
