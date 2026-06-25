import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step18BothOddKillableFamilies

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- External input: each fixed prime-pair fiber is finite.

Mathematically this is the `S`-unit / Baker-type fixed-base exponential equation
input for `p^u + q^v = 2^w`. -/
axiom fixedPrimePair_finite_certificate
    (p q : ℕ) :
    Branch5FiniteFamilyCertificate
      (T := T) (P := P)
      (Branch5FixedPrimePairFamily (T := T) (P := P) p q)

/-- External input: if both base primes are restricted to a prescribed finite
set, the corresponding Branch 5 family is finite. -/
axiom finitePrimeSupport_finite_certificate
    (S : Finset ℕ) :
    Branch5FiniteFamilyCertificate
      (T := T) (P := P)
      (Branch5FinitePrimeSupportFamily (T := T) (P := P) S)

/-- External input: bounded-prime subfamilies are treated as finite killable
families.

This is deliberately external: a bound on one prime still leaves the other prime
variable, so the intended proof uses the same exponential-equation machinery as
the fixed/finitely-supported prime cases. -/
axiom boundedPrime_finite_certificate
    (B : ℕ) :
    Branch5FiniteFamilyCertificate
      (T := T) (P := P)
      (Branch5BoundedPrimeFamily (T := T) (P := P) B)

/-- A purely formal empty-family certificate for an impossible residue signature.

If the stored residues fail the required source congruence
`(rp+rq)%m = rrhs%m`, then no Branch 5 hard-core candidate can have that
signature.  Unlike the deeper finiteness inputs above, this one is already an
elementary consequence of the residue-signature API. -/
theorem impossibleResidueSignature_empty_certificate
    (m rp rq rrhs : ℕ)
    (hbad : (rp + rq) % m ≠ rrhs % m) :
    Branch5EmptyFamilyCertificate
      (T := T) (P := P)
      (Branch5ResidueSignatureFamily (T := T) (P := P) m rp rq rrhs) := by
  refine { empty := ?_ }
  intro F K hsig
  rcases hsig with ⟨hp, hq, hrhs⟩
  have hsum := (K.residues.arbitrary m).signature.hsum
  exact hbad (by simpa [hp, hq, hrhs] using hsum)

/-- External input: strongly unbalanced source terms form a finite killable
family once a scale parameter is fixed.

This is the near-power branch: one of `p^u`, `q^v` is much smaller than the
other, so the larger odd prime-power is very close to `2^w`. -/
axiom scaleUnbalanced_finite_certificate
    (C : ℕ) :
    Branch5FiniteFamilyCertificate
      (T := T) (P := P)
      (Branch5ScaleUnbalancedBy (T := T) (P := P) C)

/-- External input: the exponent-asymmetric and scale-unbalanced region is a
finite killable family. -/
axiom asymmetricUnbalanced_finite_certificate
    (L C : ℕ) :
    Branch5FiniteFamilyCertificate
      (T := T) (P := P)
      (Branch5AsymmetricUnbalancedBy (T := T) (P := P) L C)

/-- A finite-family certificate can be used as a generic marker that a candidate
belongs to a part of the frontier intended to be removed from the final residual
core.  This is a bookkeeping definition, not a mathematical theorem. -/
def Branch5CertifiedFinitePart
    (Family : Branch5Family T P)
    (_cert : Branch5FiniteFamilyCertificate (T := T) (P := P) Family) :
    Branch5Family T P :=
  Family

/-- An empty-family certificate removes a family by contradiction. -/
theorem false_of_emptyFamilyCertificate
    {Family : Branch5Family T P}
    (E : Branch5EmptyFamilyCertificate (T := T) (P := P) Family)
    (F : NormalForm T P) (K : BothOddResidualHardCore F) :
    Family F K → False :=
  E.empty F K

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
