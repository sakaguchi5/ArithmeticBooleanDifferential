import ABD.ABD3.Views.CollisionFrontierA

namespace ABD3
namespace ABCData

namespace CCoreResidualFactoryReal

/-- The exact C-core exponent selected by the C-surplus port. -/
def coreExponent (T : ABCData) (r : ℕ) : ℕ :=
  T.valC r

/-- The residual cofactor after removing the full `r`-adic core from `C`. -/
def coreResidual (T : ABCData) (r : ℕ) : ℕ :=
  T.C.val / r ^ T.valC r

/-- A selected positive C-port is a genuine prime. -/
theorem prime_of_single_cPortCore
    (T : ABCData) (P : PowerData)
    (core : SingleCPortCoreData T P) :
    Nat.Prime core.r := by
  have hmem : core.r ∈ primeSupport T.C.val := by
    simpa [supportC] using core.hsupportC
  exact prime_of_mem_primeSupport hmem

/-- A selected positive C-port has positive C-valuation. -/
theorem coreExponent_pos
    (T : ABCData) (P : PowerData)
    (core : SingleCPortCoreData T P) :
    0 < coreExponent T core.r := by
  have hmem : core.r ∈ primeSupport T.C.val := by
    simpa [supportC] using core.hsupportC
  have hne : T.C.val.factorization core.r ≠ 0 :=
    factorization_ne_zero_of_mem_primeSupport hmem
  exact Nat.pos_of_ne_zero (by
    simpa [coreExponent, valC, vp] using hne)

/-- Removing the full selected core leaves a positive residual cofactor. -/
theorem coreResidual_pos
    (T : ABCData) (P : PowerData)
    (core : SingleCPortCoreData T P) :
    0 < coreResidual T core.r := by
  have hCne : T.C.val ≠ 0 := Nat.ne_of_gt T.C_pos
  have hpos : 0 < T.C.val / core.r ^ T.C.val.factorization core.r :=
    Nat.ordCompl_pos core.r hCne
  simpa [coreResidual, valC, vp] using hpos

/-- The selected core and residual multiply back to `C`. -/
theorem C_eq_core_mul_residual
    (T : ABCData) (P : PowerData)
    (core : SingleCPortCoreData T P) :
    T.C.val = core.r ^ coreExponent T core.r * coreResidual T core.r := by
  have h := (Nat.ordProj_mul_ordCompl_eq_self T.C.val core.r).symm
  simpa [coreExponent, coreResidual, valC, vp] using h

/-- The selected core prime is coprime to the residual cofactor. -/
theorem coprime_core_residual
    (T : ABCData) (P : PowerData)
    (core : SingleCPortCoreData T P) :
    Nat.Coprime core.r (coreResidual T core.r) := by
  have hCne : T.C.val ≠ 0 := Nat.ne_of_gt T.C_pos
  have hr : Nat.Prime core.r := prime_of_single_cPortCore T P core
  have hcop : Nat.Coprime core.r
      (T.C.val / core.r ^ T.C.val.factorization core.r) :=
    Nat.coprime_ordCompl hr hCne
  simpa [coreResidual, valC, vp] using hcop

/-- Every residual prime direction is still a C-side prime direction. -/
theorem mem_supportC_of_mem_coreResidual_support
    (T : ABCData) (P : PowerData)
    (core : SingleCPortCoreData T P)
    {l : ℕ} (hl : l ∈ primeSupport (coreResidual T core.r)) :
    l ∈ T.supportC := by
  have hlprime : Nat.Prime l := prime_of_mem_primeSupport hl
  have hldvd_res : l ∣ coreResidual T core.r :=
    dvd_of_mem_primeSupport hl
  have hC : T.C.val = core.r ^ coreExponent T core.r * coreResidual T core.r :=
    C_eq_core_mul_residual T P core
  have hres_dvd_C : coreResidual T core.r ∣ T.C.val := by
    refine ⟨core.r ^ coreExponent T core.r, ?_⟩
    rw [hC, Nat.mul_comm]
  have hldvd_C : l ∣ T.C.val := dvd_trans hldvd_res hres_dvd_C
  have hCne : T.C.val ≠ 0 := Nat.ne_of_gt T.C_pos
  have hfac_one : 1 ≤ T.C.val.factorization l :=
    (hlprime.dvd_iff_one_le_factorization hCne).mp hldvd_C
  have hfac_ne : T.C.val.factorization l ≠ 0 := by
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hfac_one)
  have hmem : l ∈ primeSupport T.C.val := by
    unfold primeSupport
    exact Finsupp.mem_support_iff.mpr hfac_ne
  simpa [supportC] using hmem

/-- A residual prime direction cannot be the selected core prime. -/
theorem ne_core_of_mem_coreResidual_support
    (T : ABCData) (P : PowerData)
    (core : SingleCPortCoreData T P)
    {l : ℕ} (hl : l ∈ primeSupport (coreResidual T core.r)) :
    l ≠ core.r := by
  intro hlr
  have hldvd : l ∣ coreResidual T core.r := dvd_of_mem_primeSupport hl
  have hrdvd : core.r ∣ coreResidual T core.r := by
    simpa [hlr] using hldvd
  have hcop : Nat.Coprime core.r (coreResidual T core.r) :=
    coprime_core_residual T P core
  have hrdvd_gcd : core.r ∣ Nat.gcd core.r (coreResidual T core.r) :=
    Nat.dvd_gcd (dvd_refl core.r) hrdvd
  have hgcd : Nat.gcd core.r (coreResidual T core.r) = 1 := hcop
  have hrdvd_one : core.r ∣ 1 := by
    simpa [hgcd] using hrdvd_gcd
  have hrprime : Nat.Prime core.r := prime_of_single_cPortCore T P core
  exact hrprime.ne_one (Nat.dvd_one.mp hrdvd_one)

/-- A residual prime direction is not a positive C-surplus port when the selected
core is the unique positive C-port. -/
theorem not_mem_cSurplusPorts_of_mem_coreResidual_support
    (T : ABCData) (P : PowerData)
    (core : SingleCPortCoreData T P)
    {l : ℕ} (hl : l ∈ primeSupport (coreResidual T core.r)) :
    l ∉ T.CSurplusPorts P := by
  intro hport
  have hmem_single : l ∈ ({core.r} : Finset ℕ) := by
    simpa [core.hsingle] using hport
  have hlr : l = core.r := by
    simpa using hmem_single
  exact ne_core_of_mem_coreResidual_support T P core hl hlr

/-- Residual prime directions have non-positive exponent surplus. -/
theorem residual_exponentSurplus_nonpos
    (T : ABCData) (P : PowerData)
    (core : SingleCPortCoreData T P)
    {l : ℕ} (hl : l ∈ primeSupport (coreResidual T core.r)) :
    T.ExponentSurplusAt P l ≤ 0 := by
  have hlC : l ∈ T.supportC :=
    mem_supportC_of_mem_coreResidual_support T P core hl
  have hnotPort : l ∉ T.CSurplusPorts P :=
    not_mem_cSurplusPorts_of_mem_coreResidual_support T P core hl
  have hnotHigh : ¬ P.N < T.CValuationRewardAt P l := by
    intro hhigh
    exact hnotPort ((T.mem_cSurplusPorts_iff_supportC_and_high_reward P l).mpr
      ⟨hlC, hhigh⟩)
  have hleNat : T.CValuationRewardAt P l ≤ P.N := le_of_not_gt hnotHigh
  rw [T.exponentSurplusAt_of_mem_supportC P hlC]
  exact sub_nonpos.mpr (by exact_mod_cast hleNat)

/-- The complete residual-deficit normal form for the selected C-core. -/
theorem residualDeficit
    (T : ABCData) (P : PowerData)
    (core : SingleCPortCoreData T P) :
    ∀ ⦃l : ℕ⦄, l ∈ primeSupport (coreResidual T core.r) →
      l ∈ T.supportC ∧ T.ExponentSurplusAt P l ≤ 0 := by
  intro l hl
  exact ⟨
    mem_supportC_of_mem_coreResidual_support T P core hl,
    residual_exponentSurplus_nonpos T P core hl
  ⟩

end CCoreResidualFactoryReal

/-- Realized Step A4: split the unique positive C-port core out of `C`, and show
that the residual cofactor consists only of non-positive surplus C-directions.

This discharges the formerly abstract `CCoreResidualFactory`. -/
theorem cCoreResidualFactory_real
    (T : ABCData) (P : PowerData) :
    T.CCoreResidualFactory P := by
  intro core
  let w : ℕ := CCoreResidualFactoryReal.coreExponent T core.r
  let s : ℕ := CCoreResidualFactoryReal.coreResidual T core.r
  refine ⟨{
    r := core.r
    s := s
    w := w
    hr := CCoreResidualFactoryReal.prime_of_single_cPortCore T P core
    hs_pos := by
      simpa [s] using CCoreResidualFactoryReal.coreResidual_pos T P core
    hw_pos := by
      simpa [w] using CCoreResidualFactoryReal.coreExponent_pos T P core
    hC := by
      simpa [w, s] using CCoreResidualFactoryReal.C_eq_core_mul_residual T P core
    hcop_core_residual := by
      simpa [s] using CCoreResidualFactoryReal.coprime_core_residual T P core
    hsingle := core.hsingle
    hresidual := by
      intro l hl
      simpa [s] using CCoreResidualFactoryReal.residualDeficit T P core hl
  }⟩

/-- Final A theorem with both Step A1 and Step A4 fully internalized. -/
theorem rankOneOneDesyncToEfficientCollisionGoal_real
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.RankOneOneDesyncToEfficientCollisionGoal P G R := by
  exact T.rankOneOneDesyncToEfficientCollisionGoal_of_cCoreResidualFactory
    P G R (T.cCoreResidualFactory_real P)

end ABCData
end ABD3
