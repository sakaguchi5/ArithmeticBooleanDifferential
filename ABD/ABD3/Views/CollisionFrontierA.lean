import ABD.ABD3.Views.CollisionFrontier
import ABD.ABD3.Views.DPlusGraph.CPortRefinement

namespace ABD3
namespace ABCData

/-- Step A1 certificate: a positive integer with one prime-support direction is
presented as a single prime power.

The genuinely arithmetic extraction
`0 < n -> supportRank n = 1 -> Nonempty (PrimePowerPresentation n)` is kept as
an explicit factory below, so the collision layer can remain independent of the
heavy `Nat.factorization` reconstruction API.
-/
structure PrimePowerPresentation (n : ℕ) where
  p : ℕ
  e : ℕ
  hp : Nat.Prime p
  he : 0 < e
  hpow : n = p ^ e

/-- The local A1 input needed by the rank-one frontier argument. -/
def SupportRankOnePrimePowerFactory : Prop :=
  ∀ n : ℕ, 0 < n → supportRank n = 1 →
    Nonempty (PrimePowerPresentation n)


/-- Prime support membership consists only of genuine prime directions. -/
theorem prime_of_mem_primeSupport {n p : ℕ}
    (hp : p ∈ primeSupport n) :
    Nat.Prime p := by
  have hne : n.factorization p ≠ 0 :=
    factorization_ne_zero_of_mem_primeSupport hp
  by_contra hnot
  exact hne (Nat.factorization_eq_zero_of_not_prime n hnot)

/-- Real Step A1: a positive integer whose prime-support rank is one is a
single prime power.

This replaces the former abstract `SupportRankOnePrimePowerFactory` input for
the A/B side of the collision frontier argument.
-/
theorem primePowerPresentation_of_supportRank_eq_one_real
    {n : ℕ} (hn : 0 < n) (hrank : supportRank n = 1) :
    Nonempty (PrimePowerPresentation n) := by
  have hcard : (primeSupport n).card = 1 := by
    simpa [supportRank] using hrank
  rcases Finset.card_eq_one.mp hcard with ⟨p, hsupport⟩
  have hp_mem : p ∈ primeSupport n := by
    rw [hsupport]
    simp
  let e : ℕ := n.factorization p
  have hp : Nat.Prime p := prime_of_mem_primeSupport hp_mem
  have he_ne : e ≠ 0 := by
    exact factorization_ne_zero_of_mem_primeSupport hp_mem
  have he : 0 < e := Nat.pos_of_ne_zero he_ne
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hfactor : n.factorization = Finsupp.single p e := by
    ext q
    by_cases hq : q = p
    · subst q
      simp [e]
    · have hq_not_mem : q ∉ primeSupport n := by
        intro hqmem
        have hq_single : q ∈ ({p} : Finset ℕ) := by
          simpa [hsupport] using hqmem
        have hqp : q = p := by
          simpa using hq_single
        exact hq hqp
      have hq_zero : n.factorization q = 0 := by
        exact Finsupp.notMem_support_iff.mp (by
          simpa [primeSupport] using hq_not_mem)
      simp [e, hq, hq_zero]
  have hpow : n = p ^ e :=
    Nat.eq_pow_of_factorization_eq_single hn_ne hfactor
  exact ⟨{ p := p, e := e, hp := hp, he := he, hpow := hpow }⟩

/-- Realized Step A1 factory. -/
theorem supportRankOnePrimePowerFactory :
    SupportRankOnePrimePowerFactory := by
  intro n hn hrank
  exact primePowerPresentation_of_supportRank_eq_one_real hn hrank

/-- Step A1, packaged as a theorem from the local prime-power factory. -/
theorem primePowerPresentation_of_supportRank_eq_one
    (H : SupportRankOnePrimePowerFactory)
    {n : ℕ} (hn : 0 < n) (hrank : supportRank n = 1) :
    Nonempty (PrimePowerPresentation n) :=
  H n hn hrank

/-- Step A2 certificate: both A and B have been normalized as prime powers. -/
structure LowABPrimePowerData (T : ABCData) where
  Adata : PrimePowerPresentation T.A.val
  Bdata : PrimePowerPresentation T.B.val

/-- Step A2: `LowABSupportRank` gives prime-power presentations of A and B,
provided the A1 prime-power factory is available. -/
theorem lowABPrimePowerData_of_supportRankOnePrimePowerFactory
    (T : ABCData) (H : SupportRankOnePrimePowerFactory)
    (hlow : T.LowABSupportRank) :
    Nonempty (LowABPrimePowerData T) := by
  rcases hlow with ⟨hA, hB⟩
  have hArank : supportRank T.A.val = 1 := by
    simpa [rankA] using hA
  have hBrank : supportRank T.B.val = 1 := by
    simpa [rankB] using hB
  rcases H T.A.val T.A_pos hArank with ⟨Ad⟩
  rcases H T.B.val T.B_pos hBrank with ⟨Bd⟩
  exact ⟨{ Adata := Ad, Bdata := Bd }⟩

/-- Step A3 certificate: the unique positive C-surplus port has been chosen and
refined to a genuine C-side support prime. -/
structure SingleCPortCoreData (T : ABCData) (P : PowerData) where
  r : ℕ
  hsingle : T.CSurplusPorts P = {r}
  hmem : r ∈ T.CSurplusPorts P
  hsupportC : r ∈ T.supportC

/-- Step A3: extract the unique C-port core from `SinglePositiveCPort`.

The existing D+ refinement theorem supplies `r ∈ supportC` from positive
C-port membership.
-/
theorem singleCPortCoreData_of_singlePositiveCPort
    (T : ABCData) (P : PowerData)
    (hsingle : T.SinglePositiveCPort P) :
    Nonempty (SingleCPortCoreData T P) := by
  rcases hsingle with ⟨r, hr⟩
  have hmem : r ∈ T.CSurplusPorts P := by
    rw [hr]
    simp
  have hsupportC : r ∈ T.supportC :=
    T.mem_supportC_of_mem_cSurplusPorts P hmem
  exact ⟨{ r := r, hsingle := hr, hmem := hmem, hsupportC := hsupportC }⟩

/-- Step A4 certificate: the chosen C-core has been split off as
`C = r^w * s`, with `s` coprime to `r`, and all residual prime directions have
non-positive exponent surplus.

This is the factorization-heavy part of A.  It is deliberately isolated from the
rank-one graph argument.
-/
structure CCoreResidualData (T : ABCData) (P : PowerData) where
  r : ℕ
  s : ℕ
  w : ℕ
  hr : Nat.Prime r
  hs_pos : 0 < s
  hw_pos : 0 < w
  hC : T.C.val = r ^ w * s
  hcop_core_residual : Nat.Coprime r s
  hsingle : T.CSurplusPorts P = {r}
  hresidual : ∀ ⦃l : ℕ⦄, l ∈ primeSupport s →
    l ∈ T.supportC ∧ T.ExponentSurplusAt P l ≤ 0

/-- The local A4 input needed by the collision frontier argument. -/
def CCoreResidualFactory (T : ABCData) (P : PowerData) : Prop :=
  SingleCPortCoreData T P → Nonempty (CCoreResidualData T P)

/-- Step A4, packaged as a theorem from the C-core residual factory. -/
theorem cCoreResidualData_of_factory
    (T : ABCData) (P : PowerData)
    (H : T.CCoreResidualFactory P)
    (Ccore : SingleCPortCoreData T P) :
    Nonempty (CCoreResidualData T P) :=
  H Ccore

/-- Step A5 normal form: A/B prime-power data plus C-core residual data. -/
structure RankOneOneCollisionNormalForm (T : ABCData) (P : PowerData) where
  ab : LowABPrimePowerData T
  ccore : CCoreResidualData T P

namespace RankOneOneCollisionNormalForm

/-- Convert the A1--A4 normal form into the previously introduced
`OnePlaceCollisionData`. -/
def toOnePlaceCollisionData
    {T : ABCData} {P : PowerData}
    (N : RankOneOneCollisionNormalForm T P) :
    T.OnePlaceCollisionData :=
  { p := N.ab.Adata.p
    q := N.ab.Bdata.p
    r := N.ccore.r
    s := N.ccore.s
    u := N.ab.Adata.e
    v := N.ab.Bdata.e
    w := N.ccore.w
    hp := N.ab.Adata.hp
    hq := N.ab.Bdata.hp
    hr := N.ccore.hr
    hs_pos := N.ccore.hs_pos
    hw_pos := N.ccore.hw_pos
    hA := N.ab.Adata.hpow
    hB := N.ab.Bdata.hpow
    hC := N.ccore.hC
    hcop_core_residual := N.ccore.hcop_core_residual }

@[simp] theorem toOnePlaceCollisionData_r
    {T : ABCData} {P : PowerData}
    (N : RankOneOneCollisionNormalForm T P) :
    N.toOnePlaceCollisionData.r = N.ccore.r := rfl

@[simp] theorem toOnePlaceCollisionData_s
    {T : ABCData} {P : PowerData}
    (N : RankOneOneCollisionNormalForm T P) :
    N.toOnePlaceCollisionData.s = N.ccore.s := rfl

/-- The collision normal form supplies the unique-surplus-core condition. -/
theorem singleSurplusCore
    {T : ABCData} {P : PowerData}
    (N : RankOneOneCollisionNormalForm T P) :
    N.toOnePlaceCollisionData.SingleSurplusCore P := by
  simpa [OnePlaceCollisionData.SingleSurplusCore,
    RankOneOneCollisionNormalForm.toOnePlaceCollisionData]
    using N.ccore.hsingle

/-- The collision normal form supplies the residual-deficit condition. -/
theorem residualDeficit
    {T : ABCData} {P : PowerData}
    (N : RankOneOneCollisionNormalForm T P) :
    N.toOnePlaceCollisionData.ResidualDeficit P := by
  simpa [OnePlaceCollisionData.ResidualDeficit,
    RankOneOneCollisionNormalForm.toOnePlaceCollisionData]
    using N.ccore.hresidual

end RankOneOneCollisionNormalForm

/-- Step A5: build the full collision normal form from A1 and A4 factories. -/
theorem rankOneOneCollisionNormalForm_of_factories
    (T : ABCData) (P : PowerData)
    (Hpp : SupportRankOnePrimePowerFactory)
    (Hc : T.CCoreResidualFactory P)
    (hlow : T.LowABSupportRank)
    (hsingle : T.SinglePositiveCPort P) :
    Nonempty (RankOneOneCollisionNormalForm T P) := by
  rcases T.lowABPrimePowerData_of_supportRankOnePrimePowerFactory Hpp hlow with ⟨ab⟩
  rcases T.singleCPortCoreData_of_singlePositiveCPort P hsingle with ⟨core⟩
  rcases T.cCoreResidualData_of_factory P Hc core with ⟨ccore⟩
  exact ⟨{ ab := ab, ccore := ccore }⟩

/-- A-collision assembly theorem: a collision normal form proves the old
`RankOneOneDesyncToEfficientCollisionGoal`. -/
theorem rankOneOneDesyncToEfficientCollisionGoal_of_normalForm
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (N : RankOneOneCollisionNormalForm T P) :
    T.RankOneOneDesyncToEfficientCollisionGoal P G R := by
  intro hfrontier
  let D := N.toOnePlaceCollisionData
  refine ⟨hfrontier, ?_⟩
  exact ⟨D, N.singleSurplusCore, N.residualDeficit⟩

/-- Final A theorem: A1 plus A4 factories close the full rank `(1,1)`
desynchronized-to-efficient-collision reduction. -/
theorem rankOneOneDesyncToEfficientCollisionGoal_of_factories
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (Hpp : SupportRankOnePrimePowerFactory)
    (Hc : T.CCoreResidualFactory P) :
    T.RankOneOneDesyncToEfficientCollisionGoal P G R := by
  intro hfrontier
  have hlow : T.LowABSupportRank := hfrontier.1
  have hsingle : T.SinglePositiveCPort P := hfrontier.2.2.2.1
  rcases T.rankOneOneCollisionNormalForm_of_factories P Hpp Hc hlow hsingle with ⟨N⟩
  exact T.rankOneOneDesyncToEfficientCollisionGoal_of_normalForm P G R N hfrontier


/-- Final A theorem with Step A1 fully internalized.

After this theorem, the only remaining local input for A is the C-side
core/residual factorization package `CCoreResidualFactory`.
-/
theorem rankOneOneDesyncToEfficientCollisionGoal_of_cCoreResidualFactory
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (Hc : T.CCoreResidualFactory P) :
    T.RankOneOneDesyncToEfficientCollisionGoal P G R := by
  exact T.rankOneOneDesyncToEfficientCollisionGoal_of_factories
    P G R supportRankOnePrimePowerFactory Hc

end ABCData
end ABD3
