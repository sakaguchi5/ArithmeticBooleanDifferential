import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step6CoeffScales

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Explicit radical-small inequality in the pure two-power model:
`(2*p*q)^N < (2^w)^M`. -/
def ExplicitRadicalSmall (F : NormalForm T P) : Prop :=
  (((2 * F.p * F.q : ℕ) : ℤ) ^ P.N) < (((2 ^ F.w : ℕ) : ℤ) ^ P.M)

/-- In the pure two-power model, `RadicalSmall` is exactly
`(2*p*q)^N < (2^w)^M`. -/
theorem radicalSmall_iff_explicit (F : NormalForm T P) :
    T.RadicalSmall P ↔ F.ExplicitRadicalSmall := by
  unfold RadicalSmall RadicalSmallInt ExplicitRadicalSmall
  rw [F.radABC_eq_two_mul_p_mul_q, F.C_eq_two_pow]

/-- Forward direction of the explicit radical-small specialization. -/
theorem explicitRadicalSmall_of_radicalSmall
    (F : NormalForm T P) (hsmall : T.RadicalSmall P) :
    F.ExplicitRadicalSmall :=
  (F.radicalSmall_iff_explicit).mp hsmall

/-- Reverse direction of the explicit radical-small specialization. -/
theorem radicalSmall_of_explicitRadicalSmall
    (F : NormalForm T P) (hsmall : F.ExplicitRadicalSmall) :
    T.RadicalSmall P :=
  (F.radicalSmall_iff_explicit).mpr hsmall

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
