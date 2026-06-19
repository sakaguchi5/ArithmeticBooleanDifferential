import ABD.ABD2.Fibration.TargetZeroCostAnatomy

namespace ABD2
namespace ABCTriple

/-- One-sided AB support: exactly the regime where one AB block is absent and the
other is present.

B2 is about this case.  Unlike the two-sided case from B0/B1, a target-zero good
base point cannot exist here; any nondegenerate good seed forces a nonzero target
which must be absorbed by the C side. -/
def OneSidedABSupport (T : ABCTriple) : Prop :=
  (T.supportA = ∅ ∧ T.supportB.Nonempty) ∨
    (T.supportB = ∅ ∧ T.supportA.Nonempty)

/-- If the A-support is empty, the A-derivative value of every full tangent is
zero. -/
theorem ADerivValue_eq_zero_of_supportA_eq_empty
    (T : ABCTriple) {x : T.FullTangent}
    (hA : T.supportA = ∅) :
    T.ADerivValue x = 0 := by
  unfold ABCTriple.ADerivValue
  rw [← T.formalDeriv_a_eq_maskA x]
  have hmask : T.maskA x = 0 := by
    unfold ABCTriple.maskA
    rw [hA]
    simp
  rw [hmask]
  simp

/-- If the B-support is empty, the B-derivative value of every full tangent is
zero. -/
theorem BDerivValue_eq_zero_of_supportB_eq_empty
    (T : ABCTriple) {x : T.FullTangent}
    (hB : T.supportB = ∅) :
    T.BDerivValue x = 0 := by
  unfold ABCTriple.BDerivValue
  rw [← T.formalDeriv_b_eq_maskB x]
  have hmask : T.maskB x = 0 := by
    unfold ABCTriple.maskB
    rw [hB]
    simp
  rw [hmask]
  simp

/-- If both AB derivative values vanish, then the Wronskian vanishes. -/
theorem Wronskian_eq_zero_of_ADerivValue_eq_zero_of_BDerivValue_eq_zero
    (T : ABCTriple) {x : T.FullTangent}
    (hA : T.ADerivValue x = 0) (hB : T.BDerivValue x = 0) :
    T.Wronskian x = 0 := by
  unfold ABCTriple.Wronskian ABCTriple.ADerivValue ABCTriple.BDerivValue at *
  rw [hB, hA]
  simp

/-- If the A-support is empty, no target-zero good base point can live at the
specified tangent.

Target-zero would force the remaining B-derivative value to vanish, and then the
Wronskian would vanish, contradicting goodness. -/
theorem not_targetZeroGoodBasePoint_of_supportA_eq_empty
    (T : ABCTriple) (P : T.CImageProfile) {x : T.FullTangent}
    (hA : T.supportA = ∅) :
    ¬ T.TargetZeroGoodBasePoint P x := by
  intro htz
  have hAval : T.ADerivValue x = 0 :=
    T.ADerivValue_eq_zero_of_supportA_eq_empty hA
  have hcancel : T.ADerivValue x + T.BDerivValue x = 0 :=
    T.ADerivValue_add_BDerivValue_eq_zero_of_targetZeroGoodBasePoint P htz
  have hBval : T.BDerivValue x = 0 := by
    rw [hAval] at hcancel
    simpa using hcancel
  have hWzero : T.Wronskian x = 0 :=
    T.Wronskian_eq_zero_of_ADerivValue_eq_zero_of_BDerivValue_eq_zero hAval hBval
  exact (T.wronskian_ne_zero_of_targetZeroGoodBasePoint P htz) hWzero

/-- If the B-support is empty, no target-zero good base point can live at the
specified tangent. -/
theorem not_targetZeroGoodBasePoint_of_supportB_eq_empty
    (T : ABCTriple) (P : T.CImageProfile) {x : T.FullTangent}
    (hB : T.supportB = ∅) :
    ¬ T.TargetZeroGoodBasePoint P x := by
  intro htz
  have hBval : T.BDerivValue x = 0 :=
    T.BDerivValue_eq_zero_of_supportB_eq_empty hB
  have hcancel : T.ADerivValue x + T.BDerivValue x = 0 :=
    T.ADerivValue_add_BDerivValue_eq_zero_of_targetZeroGoodBasePoint P htz
  have hAval : T.ADerivValue x = 0 := by
    rw [hBval] at hcancel
    simpa using hcancel
  have hWzero : T.Wronskian x = 0 :=
    T.Wronskian_eq_zero_of_ADerivValue_eq_zero_of_BDerivValue_eq_zero hAval hBval
  exact (T.wronskian_ne_zero_of_targetZeroGoodBasePoint P htz) hWzero

/-- If either AB block is empty, target-zero good base points do not exist. -/
theorem not_hasTargetZeroGoodBasePoint_of_left_empty
    (T : ABCTriple) (P : T.CImageProfile)
    (hA : T.supportA = ∅) :
    ¬ T.HasTargetZeroGoodBasePoint P := by
  intro h
  rcases h with ⟨x, hx⟩
  exact T.not_targetZeroGoodBasePoint_of_supportA_eq_empty P hA hx

/-- If either AB block is empty, target-zero good base points do not exist. -/
theorem not_hasTargetZeroGoodBasePoint_of_right_empty
    (T : ABCTriple) (P : T.CImageProfile)
    (hB : T.supportB = ∅) :
    ¬ T.HasTargetZeroGoodBasePoint P := by
  intro h
  rcases h with ⟨x, hx⟩
  exact T.not_targetZeroGoodBasePoint_of_supportB_eq_empty P hB hx

/-- In the one-sided AB-support case, target-zero good base points are impossible. -/
theorem not_hasTargetZeroGoodBasePoint_of_oneSidedABSupport
    (T : ABCTriple) (P : T.CImageProfile)
    (hside : T.OneSidedABSupport) :
    ¬ T.HasTargetZeroGoodBasePoint P := by
  rcases hside with hleft | hright
  · exact T.not_hasTargetZeroGoodBasePoint_of_left_empty P hleft.1
  · exact T.not_hasTargetZeroGoodBasePoint_of_right_empty P hright.1

/-- If the A-support is empty, a good base point necessarily has nonzero AB
target. -/
theorem abTarget_ne_zero_of_goodBasePoint_of_supportA_eq_empty
    (T : ABCTriple) (P : T.CImageProfile) {x : T.FullTangent}
    (hA : T.supportA = ∅) (hgood : T.GoodBasePoint P x) :
    T.abTarget x ≠ 0 := by
  intro htarget
  have htz : T.TargetZeroGoodBasePoint P x := ⟨hgood, htarget⟩
  exact T.not_targetZeroGoodBasePoint_of_supportA_eq_empty P hA htz

/-- If the B-support is empty, a good base point necessarily has nonzero AB
target. -/
theorem abTarget_ne_zero_of_goodBasePoint_of_supportB_eq_empty
    (T : ABCTriple) (P : T.CImageProfile) {x : T.FullTangent}
    (hB : T.supportB = ∅) (hgood : T.GoodBasePoint P x) :
    T.abTarget x ≠ 0 := by
  intro htarget
  have htz : T.TargetZeroGoodBasePoint P x := ⟨hgood, htarget⟩
  exact T.not_targetZeroGoodBasePoint_of_supportB_eq_empty P hB htz

/-- In the one-sided AB-support case, every good base point forces a nonzero AB
target. -/
theorem abTarget_ne_zero_of_goodBasePoint_of_oneSidedABSupport
    (T : ABCTriple) (P : T.CImageProfile) {x : T.FullTangent}
    (hside : T.OneSidedABSupport) (hgood : T.GoodBasePoint P x) :
    T.abTarget x ≠ 0 := by
  rcases hside with hleft | hright
  · exact T.abTarget_ne_zero_of_goodBasePoint_of_supportA_eq_empty P hleft.1 hgood
  · exact T.abTarget_ne_zero_of_goodBasePoint_of_supportB_eq_empty P hright.1 hgood

/-- B2 forced-lift anatomy.

A certificate of this type says: in a one-sided AB-support regime, a good seed
cannot be target-zero; any C-lift must therefore realize a nonzero C-linear value.
This is the precise sense in which the one-sided case is genuinely a C-lift
problem, unlike the two-sided B0/B1 case. -/
structure OneSidedForcedCLiftAnatomy
    (T : ABCTriple) (P : T.CImageProfile) where
  seed : T.FullTangent
  lift : T.FullTangent
  oneSided : T.OneSidedABSupport
  good : T.GoodBasePoint P seed
  cLift : T.HasCLift seed lift
  target_ne_zero : T.abTarget seed ≠ 0
  cLinearForm_eq_target : T.cLinearForm lift = T.abTarget seed
  cLinearForm_ne_zero : T.cLinearForm lift ≠ 0

/-- Existence of a one-sided forced C-lift anatomy certificate. -/
def HasOneSidedForcedCLiftAnatomy
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  Nonempty (T.OneSidedForcedCLiftAnatomy P)

/-- Build the forced C-lift anatomy from a good base point and one concrete
C-lift. -/
def oneSidedForcedCLiftAnatomy_of_goodBasePoint_and_cLift
    (T : ABCTriple) (P : T.CImageProfile) {seed lift : T.FullTangent}
    (hside : T.OneSidedABSupport)
    (hgood : T.GoodBasePoint P seed)
    (hlift : T.HasCLift seed lift) :
    T.OneSidedForcedCLiftAnatomy P := by
  have htarget : T.abTarget seed ≠ 0 :=
    T.abTarget_ne_zero_of_goodBasePoint_of_oneSidedABSupport P hside hgood
  refine
    { seed := seed
      lift := lift
      oneSided := hside
      good := hgood
      cLift := hlift
      target_ne_zero := htarget
      cLinearForm_eq_target := hlift.c_balance
      cLinearForm_ne_zero := ?_ }
  intro hzero
  apply htarget
  rw [← hlift.c_balance]
  exact hzero

/-- A good base point plus fiber nonemptiness gives a forced one-sided C-lift
certificate. -/
theorem hasOneSidedForcedCLiftAnatomy_of_hasGoodBasePoint_and_fiberNonemptyForBase
    (T : ABCTriple) (P : T.CImageProfile)
    (hside : T.OneSidedABSupport)
    (hbase : T.HasGoodBasePoint P)
    (hfiber : T.FiberNonemptyForBase P) :
    T.HasOneSidedForcedCLiftAnatomy P := by
  rcases hbase with ⟨seed, hgood⟩
  rcases hfiber seed hgood.1 with ⟨lift, hlift⟩
  exact ⟨T.oneSidedForcedCLiftAnatomy_of_goodBasePoint_and_cLift P hside hgood hlift⟩

/-- A solved qualitative fibration in the one-sided support case always contains a
forced nonzero C-lift. -/
theorem hasOneSidedForcedCLiftAnatomy_of_qualitativeFibrationSolved
    (T : ABCTriple) (P : T.CImageProfile)
    (hside : T.OneSidedABSupport)
    (hqual : T.QualitativeFibrationSolved P) :
    T.HasOneSidedForcedCLiftAnatomy P := by
  exact T.hasOneSidedForcedCLiftAnatomy_of_hasGoodBasePoint_and_fiberNonemptyForBase
    P hside hqual.1 hqual.2

/-- A finite-cost version of the one-sided forced C-lift anatomy. -/
structure OneSidedForcedLiftCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) where
  forced : T.OneSidedForcedCLiftAnatomy P
  smallLift : T.SmallTangent forced.lift B

/-- Existence of a finite-cost one-sided forced C-lift anatomy certificate. -/
def HasFiniteOneSidedForcedLiftCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∃ B : ℤ, Nonempty (T.OneSidedForcedLiftCostAnatomy P B)

/-- Add the crude finite coordinate bound to a forced C-lift anatomy certificate. -/
theorem nonempty_oneSidedForcedLiftCostAnatomy_of_forcedCLiftAnatomy
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.OneSidedForcedCLiftAnatomy P) :
    Nonempty (T.OneSidedForcedLiftCostAnatomy P (T.coordinateBound h.lift)) := by
  exact ⟨{ forced := h, smallLift := T.smallTangent_coordinateBound h.lift }⟩

/-- A forced C-lift anatomy certificate automatically has some finite lift cost. -/
theorem hasFiniteOneSidedForcedLiftCostAnatomy_of_hasOneSidedForcedCLiftAnatomy
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasOneSidedForcedCLiftAnatomy P) :
    T.HasFiniteOneSidedForcedLiftCostAnatomy P := by
  rcases h with ⟨hforced⟩
  exact ⟨T.coordinateBound hforced.lift,
    T.nonempty_oneSidedForcedLiftCostAnatomy_of_forcedCLiftAnatomy P hforced⟩

/-- B2 completed theorem: a solved qualitative fibration in the one-sided support
case yields a finite-cost forced C-lift anatomy certificate. -/
theorem hasFiniteOneSidedForcedLiftCostAnatomy_of_qualitativeFibrationSolved
    (T : ABCTriple) (P : T.CImageProfile)
    (hside : T.OneSidedABSupport)
    (hqual : T.QualitativeFibrationSolved P) :
    T.HasFiniteOneSidedForcedLiftCostAnatomy P := by
  exact T.hasFiniteOneSidedForcedLiftCostAnatomy_of_hasOneSidedForcedCLiftAnatomy P
    (T.hasOneSidedForcedCLiftAnatomy_of_qualitativeFibrationSolved P hside hqual)

/-- A one-sided forced C-lift anatomy certificate still routes to a strict
candidate. -/
theorem hasStrictCandidate_of_oneSidedForcedCLiftAnatomy
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.OneSidedForcedCLiftAnatomy P) :
    T.HasStrictCandidate := by
  exact ⟨h.lift,
    T.strictCandidate_of_goodSeed_and_cLift h.seed h.lift h.good.2 h.cLift⟩

/-- Finite-cost one-sided forced anatomy also routes to a strict candidate. -/
theorem hasStrictCandidate_of_hasFiniteOneSidedForcedLiftCostAnatomy
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasFiniteOneSidedForcedLiftCostAnatomy P) :
    T.HasStrictCandidate := by
  rcases h with ⟨B, hB⟩
  rcases hB with ⟨hcert⟩
  exact T.hasStrictCandidate_of_oneSidedForcedCLiftAnatomy P hcert.forced

end ABCTriple
end ABD2
