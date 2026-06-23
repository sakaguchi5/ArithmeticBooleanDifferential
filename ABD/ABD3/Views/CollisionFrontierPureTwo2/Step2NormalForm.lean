import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step1PrimePowerLemmas
import ABD.ABD3.Views.DPlusGraph.Generators

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2

/-- Bottom-up pure two-power normal form.

This is the minimal single-port prime-power frontier

`A = p^u`, `B = q^v`, `C = 2^w`,

implemented as the existing rank `(1,1)` collision normal form plus the
specialization `r = 2`, `s = 1`, and the symmetry-breaking order `p < q`. -/
structure NormalForm (T : ABCData) (P : PowerData) where
  N : RankOneOneCollisionNormalForm T P
  hcore_two : N.ccore.r = 2
  hresidual_one : N.ccore.s = 1
  horder : N.ab.Adata.p < N.ab.Bdata.p

namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- A-side base prime. -/
def p (F : NormalForm T P) : ℕ :=
  F.N.ab.Adata.p

/-- B-side base prime. -/
def q (F : NormalForm T P) : ℕ :=
  F.N.ab.Bdata.p

/-- C-side core prime, equal to `2` in this model. -/
def r (F : NormalForm T P) : ℕ :=
  F.N.ccore.r

/-- A-side exponent. -/
def u (F : NormalForm T P) : ℕ :=
  F.N.ab.Adata.e

/-- B-side exponent. -/
def v (F : NormalForm T P) : ℕ :=
  F.N.ab.Bdata.e

/-- C-side two-adic exponent. -/
def w (F : NormalForm T P) : ℕ :=
  F.N.ccore.w

/-- The old one-place collision data obtained by forgetting the specialization. -/
def toOnePlaceCollisionData (F : NormalForm T P) :
    T.OnePlaceCollisionData :=
  F.N.toOnePlaceCollisionData

@[simp] theorem r_eq_two (F : NormalForm T P) :
    F.r = 2 := by
  simpa [r] using F.hcore_two

@[simp] theorem residual_eq_one (F : NormalForm T P) :
    F.N.ccore.s = 1 :=
  F.hresidual_one

@[simp] theorem toOnePlaceCollisionData_r
    (F : NormalForm T P) :
    F.toOnePlaceCollisionData.r = 2 := by
  simp [toOnePlaceCollisionData, RankOneOneCollisionNormalForm.toOnePlaceCollisionData,
    F.hcore_two]

@[simp] theorem toOnePlaceCollisionData_s
    (F : NormalForm T P) :
    F.toOnePlaceCollisionData.s = 1 := by
  simp [toOnePlaceCollisionData, RankOneOneCollisionNormalForm.toOnePlaceCollisionData]

@[simp] theorem p_prime (F : NormalForm T P) :
    Nat.Prime F.p := by
  simpa [p] using F.N.ab.Adata.hp

@[simp] theorem q_prime (F : NormalForm T P) :
    Nat.Prime F.q := by
  simpa [q] using F.N.ab.Bdata.hp

@[simp] theorem r_prime (F : NormalForm T P) :
    Nat.Prime F.r := by
  simpa [r] using F.N.ccore.hr

@[simp] theorem u_pos (F : NormalForm T P) :
    0 < F.u := by
  simpa [u] using F.N.ab.Adata.he

@[simp] theorem v_pos (F : NormalForm T P) :
    0 < F.v := by
  simpa [v] using F.N.ab.Bdata.he

@[simp] theorem w_pos (F : NormalForm T P) :
    0 < F.w := by
  simpa [w] using F.N.ccore.hw_pos

@[simp] theorem p_lt_q (F : NormalForm T P) :
    F.p < F.q := by
  simpa [p, q] using F.horder

/-- The inherited single-surplus-core normal-form fact. -/
theorem singleSurplusCore (F : NormalForm T P) :
    F.toOnePlaceCollisionData.SingleSurplusCore P := by
  simpa [toOnePlaceCollisionData] using F.N.singleSurplusCore

/-- The inherited residual-deficit fact.  In the pure model the residual is `1`. -/
theorem residualDeficit (F : NormalForm T P) :
    F.toOnePlaceCollisionData.ResidualDeficit P := by
  simpa [toOnePlaceCollisionData] using F.N.residualDeficit

end NormalForm

/-- The proposition that a triple admits the pure two-power normal form. -/
def Model (T : ABCData) (P : PowerData) : Prop :=
  Nonempty (NormalForm T P)

end CollisionFrontierPureTwo2
end ABCData
end ABD3
