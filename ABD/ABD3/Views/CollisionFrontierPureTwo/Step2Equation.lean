import ABD.ABD3.Views.CollisionFrontierPureTwo.Step1NormalForm

namespace ABD3
namespace ABCData
namespace PureTwoPowerNormalForm

variable {T : ABCData} {P : PowerData}

/-- In the pure two-power model, the C-side value is exactly `2^w`. -/
theorem C_eq_two_pow (F : PureTwoPowerNormalForm T P) :
    T.C.val = 2 ^ F.w := by
  rw [F.N.ccore.hC]
  simp [w, F.hcore_two]

/-- The A-side value is `p^u`. -/
theorem A_eq_p_pow_u (F : PureTwoPowerNormalForm T P) :
    T.A.val = F.p ^ F.u := by
  simpa [p, u] using F.N.ab.Adata.hpow

/-- The B-side value is `q^v`. -/
theorem B_eq_q_pow_v (F : PureTwoPowerNormalForm T P) :
    T.B.val = F.q ^ F.v := by
  simpa [q, v] using F.N.ab.Bdata.hpow

/-- The source equation specialized to the minimal model:
`p^u + q^v = 2^w`. -/
theorem source_sum_eq_two_pow (F : PureTwoPowerNormalForm T P) :
    F.p ^ F.u + F.q ^ F.v = 2 ^ F.w := by
  rw [← F.A_eq_p_pow_u, ← F.B_eq_q_pow_v, T.h_add, F.C_eq_two_pow]

/-- Positivity of the A-base prime. -/
theorem p_pos (F : PureTwoPowerNormalForm T P) :
    0 < F.p :=
  F.p_prime.pos

/-- Positivity of the B-base prime. -/
theorem q_pos (F : PureTwoPowerNormalForm T P) :
    0 < F.q :=
  F.q_prime.pos


end PureTwoPowerNormalForm
end ABCData
end ABD3
