import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step5Radical

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- A-side synchronization generator: `u * p^(u-1)`. -/
def pureGA (F : NormalForm T P) : ℕ :=
  F.u * F.p ^ (F.u - 1)

/-- B-side synchronization generator: `v * q^(v-1)`. -/
def pureGB (F : NormalForm T P) : ℕ :=
  F.v * F.q ^ (F.v - 1)

/-- C-side synchronization generator: `w * 2^(w-1)`. -/
def pureGC (F : NormalForm T P) : ℕ :=
  F.w * 2 ^ (F.w - 1)

/-- The pure-model A/B arithmetic synchronization generators. -/
def pureSyncGenerators (F : NormalForm T P) :
    ArithmeticSyncGenerators :=
  { gA := F.pureGA, gB := F.pureGB }

@[simp] theorem pureSyncGenerators_gA (F : NormalForm T P) :
    F.pureSyncGenerators.gA = F.pureGA := rfl

@[simp] theorem pureSyncGenerators_gB (F : NormalForm T P) :
    F.pureSyncGenerators.gB = F.pureGB := rfl

/-- A-side coefficient scale is the pure generator. -/
theorem coeffAbsA_eq_pureGA (F : NormalForm T P) :
    T.coeffAbsA F.p = F.pureGA := by
  have h := coeffOf_prime_pow_self_natAbs F.p_prime F.u_pos
  simpa [coeffAbsA, coeffA, pureGA, F.A_eq_p_pow_u] using h

/-- B-side coefficient scale is the pure generator. -/
theorem coeffAbsB_eq_pureGB (F : NormalForm T P) :
    T.coeffAbsB F.q = F.pureGB := by
  have h := coeffOf_prime_pow_self_natAbs F.q_prime F.v_pos
  simpa [coeffAbsB, coeffB, pureGB, F.B_eq_q_pow_v] using h

/-- C-side two-port coefficient scale is the pure generator. -/
theorem cPortCoeffNat_two_eq_pureGC (F : NormalForm T P) :
    T.CPortCoeffNat 2 = F.pureGC := by
  have h := coeffOf_prime_pow_self_natAbs Nat.prime_two F.w_pos
  simpa [CPortCoeffNat, coeffC, pureGC, F.C_eq_two_pow] using h

/-- Optional package collecting the three coefficient-scale identities. -/
structure CoeffScaleFacts (F : NormalForm T P) where
  hA : T.coeffAbsA F.p = F.pureGA
  hB : T.coeffAbsB F.q = F.pureGB
  hC : T.CPortCoeffNat 2 = F.pureGC

/-- The coefficient-scale package is realized. -/
theorem coeffScaleFacts (F : NormalForm T P) :
    CoeffScaleFacts F :=
  { hA := F.coeffAbsA_eq_pureGA
    hB := F.coeffAbsB_eq_pureGB
    hC := F.cPortCoeffNat_two_eq_pureGC }

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
