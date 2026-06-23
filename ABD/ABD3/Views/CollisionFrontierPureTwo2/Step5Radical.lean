import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step4Support

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- The radical of the full support is `2*p*q`. -/
theorem radABC_eq_two_mul_p_mul_q (F : NormalForm T P) :
    T.radABC = 2 * F.p * F.q := by
  have h2p : 2 ≠ F.p := F.p_ne_two.symm
  have h2q : 2 ≠ F.q := F.q_ne_two.symm
  have hpq : F.p ≠ F.q := F.p_ne_q
  change radOfSupport T.supportABC = 2 * F.p * F.q
  rw [F.supportABC_eq_three]
  simp [radOfSupport, h2p, h2q, hpq, Nat.mul_assoc]

/-- Block radical product specializes to `2*p*q` as well. -/
theorem blockRadicalProduct_eq_two_mul_p_mul_q (F : NormalForm T P) :
    T.blockRadicalProduct = 2 * F.p * F.q := by
  rw [← T.radABC_eq_blockRadicalProduct]
  exact F.radABC_eq_two_mul_p_mul_q

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
