import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step0Core
import ABD.ABD3.Views.DPlusGraph.Generators

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3

/-- Canonical pure two-power normal form.

This is the normalized rank `(1,1)` collision frontier

`A = p^u`, `B = q^v`, `C = 2^w`,

with residual `s = 1` and symmetry-breaking order `p < q`. -/
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

/-- C-side core prime. -/
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

/-- Forget the pure-two specialization. -/
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

/-- In the pure two-power model, the C-side value is exactly `2^w`. -/
theorem C_eq_two_pow (F : NormalForm T P) :
    T.C.val = 2 ^ F.w := by
  rw [F.N.ccore.hC]
  simp [w, F.hcore_two]

/-- The A-side value is `p^u`. -/
theorem A_eq_p_pow_u (F : NormalForm T P) :
    T.A.val = F.p ^ F.u := by
  simpa [p, u] using F.N.ab.Adata.hpow

/-- The B-side value is `q^v`. -/
theorem B_eq_q_pow_v (F : NormalForm T P) :
    T.B.val = F.q ^ F.v := by
  simpa [q, v] using F.N.ab.Bdata.hpow

/-- The source equation specialized to the minimal model: `p^u + q^v = 2^w`. -/
theorem source_sum_eq_two_pow (F : NormalForm T P) :
    F.p ^ F.u + F.q ^ F.v = 2 ^ F.w := by
  rw [← F.A_eq_p_pow_u, ← F.B_eq_q_pow_v, T.h_add, F.C_eq_two_pow]

/-- Positivity of the A-base prime. -/
theorem p_pos (F : NormalForm T P) :
    0 < F.p :=
  F.p_prime.pos

/-- Positivity of the B-base prime. -/
theorem q_pos (F : NormalForm T P) :
    0 < F.q :=
  F.q_prime.pos

/-- A-side support is the singleton `{p}`. -/
theorem supportA_eq_singleton_p (F : NormalForm T P) :
    T.supportA = ({F.p} : Support) := by
  have h := primeSupport_prime_pow_self F.p_prime F.u_pos
  simpa [supportA, F.A_eq_p_pow_u] using h

/-- B-side support is the singleton `{q}`. -/
theorem supportB_eq_singleton_q (F : NormalForm T P) :
    T.supportB = ({F.q} : Support) := by
  have h := primeSupport_prime_pow_self F.q_prime F.v_pos
  simpa [supportB, F.B_eq_q_pow_v] using h

/-- C-side support is the singleton `{2}`. -/
theorem supportC_eq_singleton_two (F : NormalForm T P) :
    T.supportC = ({2} : Support) := by
  have h := primeSupport_prime_pow_self Nat.prime_two F.w_pos
  simpa [supportC, F.C_eq_two_pow] using h

/-- The A prime is not the C prime `2`, by primitive support disjointness. -/
theorem p_ne_two (F : NormalForm T P) :
    F.p ≠ 2 := by
  intro hp2
  rcases T.supportBlocksDisjoint with ⟨_hAB, hAC, _hBC⟩
  have hpA : F.p ∈ T.supportA := by
    rw [F.supportA_eq_singleton_p]
    simp
  have h2A : 2 ∈ T.supportA := by
    simpa [hp2] using hpA
  have h2C : 2 ∈ T.supportC := by
    rw [F.supportC_eq_singleton_two]
    simp
  have hmem : 2 ∈ T.supportA ∩ T.supportC :=
    Finset.mem_inter.mpr ⟨h2A, h2C⟩
  have hbad : 2 ∈ (∅ : Support) := by
    rw [← hAC]
    exact hmem
  simp at hbad

/-- The B prime is not the C prime `2`, by primitive support disjointness. -/
theorem q_ne_two (F : NormalForm T P) :
    F.q ≠ 2 := by
  intro hq2
  rcases T.supportBlocksDisjoint with ⟨_hAB, _hAC, hBC⟩
  have hqB : F.q ∈ T.supportB := by
    rw [F.supportB_eq_singleton_q]
    simp
  have h2B : 2 ∈ T.supportB := by
    simpa [hq2] using hqB
  have h2C : 2 ∈ T.supportC := by
    rw [F.supportC_eq_singleton_two]
    simp
  have hmem : 2 ∈ T.supportB ∩ T.supportC :=
    Finset.mem_inter.mpr ⟨h2B, h2C⟩
  have hbad : 2 ∈ (∅ : Support) := by
    rw [← hBC]
    exact hmem
  simp at hbad

/-- The two A/B base primes are distinct because the normal form stores `p < q`. -/
theorem p_ne_q (F : NormalForm T P) :
    F.p ≠ F.q :=
  ne_of_lt F.p_lt_q

/-- The full ABC support is exactly the three-point support `{2,p,q}`. -/
theorem supportABC_eq_three (F : NormalForm T P) :
    T.supportABC = ({2, F.p, F.q} : Support) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ({F.p} : Support) ∪ ({F.q} : Support) ∪ ({2} : Support) := by
      simpa [supportABC, F.supportA_eq_singleton_p, F.supportB_eq_singleton_q,
        F.supportC_eq_singleton_two] using hx
    have hx_or : x = F.p ∨ x = F.q ∨ x = 2 := by
      simpa using hx'
    rcases hx_or with hxp | hxq | hx2
    · subst x; simp
    · subst x; simp
    · subst x; simp
  · intro hx
    have hx_or : x = 2 ∨ x = F.p ∨ x = F.q := by
      simpa using hx
    have hx_union : x ∈ ({F.p} : Support) ∪ ({F.q} : Support) ∪ ({2} : Support) := by
      rcases hx_or with hx2 | hxp | hxq
      · subst x; simp
      · subst x; simp
      · subst x; simp
    simpa [supportABC, F.supportA_eq_singleton_p, F.supportB_eq_singleton_q,
      F.supportC_eq_singleton_two] using hx_union

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

end CollisionFrontierPureTwo3
end ABCData
end ABD3
