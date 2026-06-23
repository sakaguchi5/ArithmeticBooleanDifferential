import ABD.ABD3.Views.CollisionFrontierA2
import ABD.ABD3.Views.DPlusGraph.Generators

namespace ABD3
namespace ABCData

/-- The pure two-power specialization of the existing one-place collision normal
form.

Mathematically this is the minimal single-port prime-power frontier

  A = p^u,  B = q^v,  C = 2^w.

It is implemented as the existing rank `(1,1)` collision normal form plus the
extra specialization `r = 2` and `s = 1` in `C = r^w * s`.  The inequality
`p < q` is only a normalization to avoid the symmetric duplicate. -/
structure PureTwoPowerNormalForm (T : ABCData) (P : PowerData) where
  N : RankOneOneCollisionNormalForm T P
  hcore_two : N.ccore.r = 2
  hresidual_one : N.ccore.s = 1
  horder : N.ab.Adata.p < N.ab.Bdata.p

namespace PureTwoPowerNormalForm

variable {T : ABCData} {P : PowerData}

/-- A-side base prime. -/
def p (F : PureTwoPowerNormalForm T P) : ℕ :=
  F.N.ab.Adata.p

/-- B-side base prime. -/
def q (F : PureTwoPowerNormalForm T P) : ℕ :=
  F.N.ab.Bdata.p

/-- C-side core prime; in this normal form it is `2`. -/
def r (F : PureTwoPowerNormalForm T P) : ℕ :=
  F.N.ccore.r

/-- A-side exponent. -/
def u (F : PureTwoPowerNormalForm T P) : ℕ :=
  F.N.ab.Adata.e

/-- B-side exponent. -/
def v (F : PureTwoPowerNormalForm T P) : ℕ :=
  F.N.ab.Bdata.e

/-- C-side two-adic exponent. -/
def w (F : PureTwoPowerNormalForm T P) : ℕ :=
  F.N.ccore.w

/-- The old one-place collision data obtained by forgetting the specialization. -/
def toOnePlaceCollisionData (F : PureTwoPowerNormalForm T P) :
    T.OnePlaceCollisionData :=
  F.N.toOnePlaceCollisionData

@[simp] theorem r_eq_two (F : PureTwoPowerNormalForm T P) :
    F.r = 2 := by
  simpa [r] using F.hcore_two

@[simp] theorem residual_eq_one (F : PureTwoPowerNormalForm T P) :
    F.N.ccore.s = 1 :=
  F.hresidual_one

@[simp] theorem toOnePlaceCollisionData_r
    (F : PureTwoPowerNormalForm T P) :
    F.toOnePlaceCollisionData.r = 2 := by
  simp [toOnePlaceCollisionData, RankOneOneCollisionNormalForm.toOnePlaceCollisionData,
    F.hcore_two]

@[simp] theorem toOnePlaceCollisionData_s
    (F : PureTwoPowerNormalForm T P) :
    F.toOnePlaceCollisionData.s = 1 := by
  simp [toOnePlaceCollisionData, RankOneOneCollisionNormalForm.toOnePlaceCollisionData,]

@[simp] theorem p_prime (F : PureTwoPowerNormalForm T P) :
    Nat.Prime F.p := by
  simpa [p] using F.N.ab.Adata.hp

@[simp] theorem q_prime (F : PureTwoPowerNormalForm T P) :
    Nat.Prime F.q := by
  simpa [q] using F.N.ab.Bdata.hp

@[simp] theorem r_prime (F : PureTwoPowerNormalForm T P) :
    Nat.Prime F.r := by
  simpa [r] using F.N.ccore.hr

@[simp] theorem u_pos (F : PureTwoPowerNormalForm T P) :
    0 < F.u := by
  simpa [u] using F.N.ab.Adata.he

@[simp] theorem v_pos (F : PureTwoPowerNormalForm T P) :
    0 < F.v := by
  simpa [v] using F.N.ab.Bdata.he

@[simp] theorem w_pos (F : PureTwoPowerNormalForm T P) :
    0 < F.w := by
  simpa [w] using F.N.ccore.hw_pos

@[simp] theorem p_lt_q (F : PureTwoPowerNormalForm T P) :
    F.p < F.q := by
  simpa [p, q] using F.horder

/-- The C-core surplus condition inherited from the rank-one collision normal
form. -/
theorem singleSurplusCore (F : PureTwoPowerNormalForm T P) :
    F.toOnePlaceCollisionData.SingleSurplusCore P := by
  simpa [toOnePlaceCollisionData] using F.N.singleSurplusCore

/-- The residual-deficit condition inherited from the rank-one collision normal
form.  In the pure two-power case the residual is `1`, so this condition is
usually vacuous, but keeping it inherited makes the bridge to existing files
smooth. -/
theorem residualDeficit (F : PureTwoPowerNormalForm T P) :
    F.toOnePlaceCollisionData.ResidualDeficit P := by
  simpa [toOnePlaceCollisionData] using F.N.residualDeficit

end PureTwoPowerNormalForm

/-- The proposition that a triple admits the pure two-power minimal normal form. -/
def PureTwoPowerModel (T : ABCData) (P : PowerData) : Prop :=
  Nonempty (PureTwoPowerNormalForm T P)

end ABCData
end ABD3
