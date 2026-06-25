import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step23UnbalancedComplementToBalanced

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- A unit-ratio congruence at modulus `2^k`.

The witness `qvInv` is intended to be an inverse of `q^v` modulo `2^k`; the
second field says that multiplying the source congruence by this inverse turns

`p^u + q^v ≡ 0`

into

`p^u * (q^v)⁻¹ ≡ -1`.

We use the equivalent natural-number form
`p^u * qvInv + 1 ≡ 0`. -/
structure Branch5TwoAdicUnitRatioAt
    (F : NormalForm T P) (k qvInv : ℕ) : Prop where
  inverse_qv :
    (F.q ^ F.v * qvInv) % (2 ^ k) = 1 % (2 ^ k)
  ratio_eq_neg_one :
    (F.p ^ F.u * qvInv + 1) % (2 ^ k) = 0

/-- The two-adic unit core at the natural precision `2^w`.

This is the first API layer where the additive congruence is replaced by a
multiplicative unit-ratio congruence.  It is still deliberately lightweight:
later files can replace the realization axiom below by a proof using odd-unit
invertibility modulo powers of two. -/
structure Branch5TwoAdicUnitCore
    (Killable : Branch5Family T P) (C : ℕ)
    (F : NormalForm T P) (K : BothOddResidualHardCore F) : Type where
  balanced_core :
    BalancedTwoAdicDesyncCore (T := T) (P := P) Killable C F K
  qv_inverse : ℕ
  unit_at_w : Branch5TwoAdicUnitRatioAt F F.w qv_inverse

/-- Realization input for the unit-ratio core.

Mathematically this should follow from:
* `q` odd, hence `q^v` is a unit modulo `2^w`;
* the source equation `p^u + q^v = 2^w`, hence
  `p^u + q^v ≡ 0 mod 2^w`;
* multiplication by the inverse of `q^v`.

For now it is an explicit small bridge to keep the next files focused on the
two-adic logarithmic analysis rather than modular-inverse plumbing. -/
axiom branch5TwoAdicUnitCore_of_balancedTwoAdicDesyncCore
    {Killable : Branch5Family T P} {C : ℕ}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (R : BalancedTwoAdicDesyncCore (T := T) (P := P) Killable C F K) :
    Branch5TwoAdicUnitCore (T := T) (P := P) Killable C F K

/-- Build the unit core automatically from a residual candidate avoiding the
standard killable registry. -/
noncomputable def branch5TwoAdicUnitCore_of_residualAfter_standardKillableRegistry
    {B L C : ℕ} {S : Finset ℕ}
    (F : NormalForm T P) (K : BothOddResidualHardCore F)
    (hC : 1 < C)
    (R : BothOddResidualAfterKillable
      (T := T) (P := P)
      (StandardKillableRegistry (T := T) (P := P) B L C S) F K) :
    Branch5TwoAdicUnitCore
      (T := T) (P := P)
      (StandardKillableRegistry (T := T) (P := P) B L C S) C F K :=
  branch5TwoAdicUnitCore_of_balancedTwoAdicDesyncCore
    (T := T) (P := P) F K
    (balancedTwoAdicDesyncCore_of_residualAfter_standardKillableRegistry
      (T := T) (P := P) (B := B) (L := L) (C := C) (S := S) F K hC R)

/-- The final target shape after the standard killable registry has been removed:
the surviving balanced core can be converted into a two-adic unit-ratio problem. -/
def Branch5TwoAdicUnitContradictionGoal
    (Killable : Branch5Family T P) (C : ℕ) : Prop :=
  ∀ (F : NormalForm T P) (K : BothOddResidualHardCore F),
    Branch5TwoAdicUnitCore (T := T) (P := P) Killable C F K → False

/-- Extract the inverse witness from the unit core. -/
def qvInverse_of_twoAdicUnitCore
    {Killable : Branch5Family T P} {C : ℕ}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (U : Branch5TwoAdicUnitCore (T := T) (P := P) Killable C F K) : ℕ :=
  U.qv_inverse

/-- The inverse witness really is an inverse of `q^v` modulo `2^w`. -/
theorem qv_inverse_spec_of_twoAdicUnitCore
    {Killable : Branch5Family T P} {C : ℕ}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (U : Branch5TwoAdicUnitCore (T := T) (P := P) Killable C F K) :
    (F.q ^ F.v * U.qv_inverse) % (2 ^ F.w) = 1 % (2 ^ F.w) :=
  U.unit_at_w.inverse_qv

/-- The unit ratio satisfies `p^u * (q^v)⁻¹ ≡ -1 mod 2^w`, encoded as
`p^u * inv + 1 ≡ 0`. -/
theorem ratio_eq_neg_one_of_twoAdicUnitCore
    {Killable : Branch5Family T P} {C : ℕ}
    {F : NormalForm T P} {K : BothOddResidualHardCore F}
    (U : Branch5TwoAdicUnitCore (T := T) (P := P) Killable C F K) :
    (F.p ^ F.u * U.qv_inverse + 1) % (2 ^ F.w) = 0 :=
  U.unit_at_w.ratio_eq_neg_one

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
