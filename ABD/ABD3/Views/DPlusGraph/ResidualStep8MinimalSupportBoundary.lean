import ABD.ABD3.Views.DPlusGraph.ResidualStep7RejectedNormalForm

namespace ABD3

namespace ABCData

/-- A positive natural number different from `1` has a nonempty prime support.

This is the small arithmetic fact used to turn the non-unit boundary
`A ≠ 1`, `B ≠ 1` into actual support-cardinality information. -/
theorem primeSupport_nonempty_of_pos_ne_one {n : ℕ}
    (hpos : 0 < n) (hne : n ≠ 1) :
    (primeSupport n).Nonempty := by
  obtain ⟨p, hpprime, hpdvd⟩ := (Nat.ne_one_iff_exists_prime_dvd).mp hne
  refine ⟨p, ?_⟩
  have hnz : n ≠ 0 := Nat.ne_of_gt hpos
  have hle : 1 ≤ n.factorization p :=
    (hpprime.dvd_iff_one_le_factorization hnz).mp hpdvd
  have hfac_ne : n.factorization p ≠ 0 := by
    omega
  simpa [primeSupport] using (Finsupp.mem_support_iff.mpr hfac_ne)

/-- Non-unit A-side gives a nonempty A-support. -/
theorem supportA_nonempty_of_not_unitBoundary
    (T : ABCData) (hunit : ¬ T.ResidualUnitBoundary) :
    T.supportA.Nonempty := by
  have hnotUnit : ¬ T.UnitBoundary := by
    simpa [ResidualUnitBoundary] using hunit
  have hnon : T.NonExceptional :=
    (T.nonExceptional_iff_not_unitBoundary).mpr hnotUnit
  simpa [supportA] using
    (primeSupport_nonempty_of_pos_ne_one T.A_pos hnon.1)

/-- Non-unit B-side gives a nonempty B-support. -/
theorem supportB_nonempty_of_not_unitBoundary
    (T : ABCData) (hunit : ¬ T.ResidualUnitBoundary) :
    T.supportB.Nonempty := by
  have hnotUnit : ¬ T.UnitBoundary := by
    simpa [ResidualUnitBoundary] using hunit
  have hnon : T.NonExceptional :=
    (T.nonExceptional_iff_not_unitBoundary).mpr hnotUnit
  simpa [supportB] using
    (primeSupport_nonempty_of_pos_ne_one T.B_pos hnon.2)

/-- The C-side support is always nonempty for positive `A+B=C` data.

Indeed `A` and `B` are positive, hence `C ≥ 2`. -/
theorem supportC_nonempty (T : ABCData) :
    T.supportC.Nonempty := by
  have hA1 : 1 ≤ T.A.val := Nat.succ_le_of_lt T.A_pos
  have hB1 : 1 ≤ T.B.val := Nat.succ_le_of_lt T.B_pos
  have hC2 : 2 ≤ T.C.val := by
    rw [← T.h_add]
    exact Nat.add_le_add hA1 hB1
  have hCne : T.C.val ≠ 1 := by
    intro hC
    omega
  simpa [supportC] using
    (primeSupport_nonempty_of_pos_ne_one T.C_pos hCne)

/-- Step 8 minimal support boundary.

This is the mathematically minimal full-support boundary for a non-unit primitive
ABC triple: once A, B, and C each contribute at least one disjoint support block,
the full support can have cardinality `3`, but not less. -/
def ResidualMinimalSupportBoundary (T : ABCData) : Prop :=
  T.supportABC.card = 3

/-- Backward-compatible concrete support-small predicate.

The graph-exceptional support-small side is still the existing `card ≤ 3`
predicate.  The new content of Step 8 is that, away from the unit boundary, this
is equivalent to the minimal boundary `card = 3`. -/
def ResidualSupportSmallConcrete
    (T : ABCData) (_P : PowerData)
    (_G : ArithmeticSyncGenerators) (_R : ℕ) : Prop :=
  T.SupportSmallExceptional

/-- The concrete support-small predicate is exactly the existing support-small
exceptional side. -/
theorem residualSupportSmallConcrete_iff_supportSmallExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) :
    T.ResidualSupportSmallConcrete P G R ↔ T.SupportSmallExceptional := by
  rfl

/-- Concrete support-small gives the residual support-small frontier. -/
theorem residualSupportSmall_of_concrete
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ResidualSupportSmallConcrete P G R) :
    T.ResidualSupportSmall P G R := by
  exact h

/-- Residual support-small is currently the same as the concrete support-small
normal form. -/
theorem residualSupportSmallConcrete_of_residualSupportSmall
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ResidualSupportSmall P G R) :
    T.ResidualSupportSmallConcrete P G R := by
  exact h

/-- Concrete support-small triples lie in the residual frontier. -/
theorem residualFrontier_of_supportSmallConcrete
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ResidualSupportSmallConcrete P G R) :
    T.ResidualFrontier P G R := by
  exact T.residualFrontier_of_supportSmall P G R h

/-- Concrete support-small triples are graph-exceptional. -/
theorem dPlusGraphExceptional_of_supportSmallConcrete
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (h : T.ResidualSupportSmallConcrete P G R) :
    T.DPlusGraphExceptional P := by
  exact T.dPlusGraphExceptional_of_residualFrontier P G R
    (T.residualFrontier_of_supportSmallConcrete P G R h)

/-- Outside the graph-exceptional side, the concrete support-small frontier is
impossible. -/
theorem not_residualSupportSmallConcrete_of_not_dPlusGraphExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hnot : ¬ T.DPlusGraphExceptional P) :
    ¬ T.ResidualSupportSmallConcrete P G R := by
  intro hsmall
  exact hnot (T.dPlusGraphExceptional_of_supportSmallConcrete P G R hsmall)

/-- The complementary non-minimal-support side used by later residual analysis. -/
def ResidualSupportNotSmallConcrete
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ¬ T.ResidualSupportSmallConcrete P G R

/-- Non-exceptionality gives the non-small-support side. -/
theorem residualSupportNotSmallConcrete_of_not_dPlusGraphExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hnot : ¬ T.DPlusGraphExceptional P) :
    T.ResidualSupportNotSmallConcrete P G R := by
  exact T.not_residualSupportSmallConcrete_of_not_dPlusGraphExceptional P G R hnot

/-- Non-unit primitive triples have full support cardinality at least three. -/
theorem three_le_supportABC_card_of_not_unitBoundary
    (T : ABCData) (hunit : ¬ T.ResidualUnitBoundary) :
    3 ≤ T.supportABC.card := by
  obtain ⟨pA, hpA⟩ := T.supportA_nonempty_of_not_unitBoundary hunit
  obtain ⟨pB, hpB⟩ := T.supportB_nonempty_of_not_unitBoundary hunit
  obtain ⟨pC, hpC⟩ := T.supportC_nonempty
  have hpAabc : pA ∈ T.supportABC := by
    simp [supportABC, hpA]
  have hpBabc : pB ∈ T.supportABC := by
    simp [supportABC, hpB]
  have hpCabc : pC ∈ T.supportABC := by
    simp [supportABC, hpC]
  have hblocks := T.supportBlocksDisjoint
  have hABne : pA ≠ pB := by
    intro hEq
    have hmem : pA ∈ T.supportA ∩ T.supportB := by
      simp only [hEq, Finset.mem_inter, hpB, and_true]
      rw [← hEq]
      exact hpA
    have hempty : T.supportA ∩ T.supportB = ∅ := hblocks.1
    simp [hempty] at hmem
  have hACne : pA ≠ pC := by
    intro hEq
    have hmem : pA ∈ T.supportA ∩ T.supportC := by
      simp only [hEq, Finset.mem_inter, hpC, and_true]
      rw [← hEq]
      exact hpA
    have hempty : T.supportA ∩ T.supportC = ∅ := hblocks.2.1
    simp [hempty] at hmem
  have hBCne : pB ≠ pC := by
    intro hEq
    have hmem : pB ∈ T.supportB ∩ T.supportC := by
      simp only [hEq, Finset.mem_inter, hpC, and_true]
      rw [← hEq]
      exact hpB
    have hempty : T.supportB ∩ T.supportC = ∅ := hblocks.2.2
    simp [hempty] at hmem
  have hsubset : ({pA, pB, pC} : Finset ℕ) ⊆ T.supportABC := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp_eq | hp_eq | hp_eq
    · simpa [hp_eq] using hpAabc
    · simpa [hp_eq] using hpBabc
    · simpa [hp_eq] using hpCabc
  have hcard : ({pA, pB, pC} : Finset ℕ).card = 3 := by
    simp [hABne, hACne, hBCne]
  have hle := Finset.card_le_card hsubset
  simpa [hcard] using hle

/-- Away from the unit boundary, the concrete support-small side is exactly the
minimal support boundary. -/
theorem residualSupportSmallConcrete_iff_minimalSupportBoundary_of_not_unitBoundary
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hunit : ¬ T.ResidualUnitBoundary) :
    T.ResidualSupportSmallConcrete P G R ↔ T.ResidualMinimalSupportBoundary := by
  unfold ResidualSupportSmallConcrete ResidualMinimalSupportBoundary SupportSmallExceptional
  have hlow : 3 ≤ T.supportABC.card :=
    T.three_le_supportABC_card_of_not_unitBoundary hunit
  constructor
  · intro hle
    exact le_antisymm hle hlow
  · intro hEq
    simp [hEq]

/-- Outside the concrete support-small side, the full support is strictly beyond
minimal; equivalently it has cardinality at least four. -/
theorem four_le_supportABC_card_of_not_supportSmallConcrete
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hnot : T.ResidualSupportNotSmallConcrete P G R) :
    4 ≤ T.supportABC.card := by
  unfold ResidualSupportNotSmallConcrete ResidualSupportSmallConcrete
    SupportSmallExceptional at hnot
  omega

/-- A convenient non-exceptional version of the strict-above-minimal conclusion. -/
theorem four_le_supportABC_card_of_not_dPlusGraphExceptional
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hnot : ¬ T.DPlusGraphExceptional P) :
    4 ≤ T.supportABC.card := by
  exact T.four_le_supportABC_card_of_not_supportSmallConcrete P G R
    (T.residualSupportNotSmallConcrete_of_not_dPlusGraphExceptional P G R hnot)

end ABCData

end ABD3
