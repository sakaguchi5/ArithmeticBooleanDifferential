import ABD.ABD2.Fibration.BadSeedFrontierA4

namespace ABD2

namespace ABCTriple

/-- A good AB-base point whose AB target is exactly zero.

This is the B0 object: it separates the two-sided AB case from the C-lift
problem.  If such a point exists, the C side can use the zero lift at the
qualitative level. -/
def TargetZeroGoodBasePoint
    (T : ABCTriple) (P : T.CImageProfile) (x : T.FullTangent) : Prop :=
  T.GoodBasePoint P x ∧ T.abTarget x = 0

/-- Existence of a target-zero good base point. -/
def HasTargetZeroGoodBasePoint
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∃ x : T.FullTangent, T.TargetZeroGoodBasePoint P x

@[simp]
theorem targetZeroGoodBasePoint_iff
    (T : ABCTriple) (P : T.CImageProfile) (x : T.FullTangent) :
    T.TargetZeroGoodBasePoint P x ↔
      x ∈ T.ABBase P ∧ T.Wronskian x ≠ 0 ∧ T.abTarget x = 0 := by
  constructor
  · intro h
    rcases h with ⟨hgood, htarget⟩
    rcases hgood with ⟨hbase, hnotker⟩
    refine ⟨hbase, ?_, htarget⟩
    intro hW
    apply hnotker
    change T.Wronskian x = 0
    exact hW
  · intro h
    rcases h with ⟨hbase, hW, htarget⟩
    refine ⟨?_, htarget⟩
    exact ⟨hbase, by
      intro hker
      apply hW
      change T.Wronskian x = 0 at hker
      exact hker⟩

/-- A target-zero tangent is automatically compatible with every nonzero-gcd
C-image profile. -/
theorem mem_ABBase_of_abTarget_eq_zero
    (T : ABCTriple) (P : T.CImageProfile) {x : T.FullTangent}
    (htarget : T.abTarget x = 0) :
    x ∈ T.ABBase P := by
  change P.gcd ∣ T.abTarget x
  rw [htarget]
  exact dvd_zero P.gcd


/-- If the A- and B-derivatives are opposite, then the AB target cancels. -/
theorem abTarget_eq_zero_of_opposite_formalDeriv
    (T : ABCTriple) (x : T.FullTangent) (D : ℤ)
    (hDa : formalDeriv T.support x T.a = D)
    (hDb : formalDeriv T.support x T.b = -D) :
    T.abTarget x = 0 := by
  unfold ABCTriple.abTarget
  rw [T.formalDeriv_a_eq_maskA x]
  rw [T.formalDeriv_b_eq_maskB x]
  rw [hDa, hDb]
  simp

/-- If the A- and B-derivatives are opposite, the Wronskian collapses to
`-c * D`. -/
theorem Wronskian_eq_neg_c_mul_of_opposite_formalDeriv
    (T : ABCTriple) (x : T.FullTangent) (D : ℤ)
    (hDa : formalDeriv T.support x T.a = D)
    (hDb : formalDeriv T.support x T.b = -D) :
    T.Wronskian x = -((T.c : ℤ) * D) := by
  have hc_eq : (T.c : ℤ) = (T.a : ℤ) + (T.b : ℤ) := by
    exact_mod_cast T.add_eq.symm
  unfold ABCTriple.Wronskian
  rw [hDa, hDb, hc_eq]
  simp [sub_eq_add_neg, mul_add, add_comm, mul_comm]

/-- Opposite nonzero A/B-derivatives give a nonzero Wronskian whenever
`c ≠ 0`. -/
theorem Wronskian_ne_zero_of_opposite_formalDeriv
    (T : ABCTriple) (x : T.FullTangent) (D : ℤ)
    (hc : T.c ≠ 0) (hD : D ≠ 0)
    (hDa : formalDeriv T.support x T.a = D)
    (hDb : formalDeriv T.support x T.b = -D) :
    T.Wronskian x ≠ 0 := by
  have hW : T.Wronskian x = -((T.c : ℤ) * D) :=
    T.Wronskian_eq_neg_c_mul_of_opposite_formalDeriv x D hDa hDb
  have hcInt : (T.c : ℤ) ≠ 0 := by
    exact_mod_cast hc
  rw [hW]
  exact neg_ne_zero.mpr (mul_ne_zero hcInt hD)

/-- Two coordinate witnesses, one on A and one on B, can be combined into a
target-zero good base point.

If `α = derivCoeff a pA` and `β = derivCoeff b pB`, the tangent
`β • eA + (-α) • eB` has opposite A/B derivatives:

* `D_a = β * α`,
* `D_b = -(β * α)`.

Hence its AB target is exactly zero, while its Wronskian is nonzero when
`c ≠ 0`.  Thus the C-fiber is qualitatively trivial in the two-sided AB case. -/
theorem hasTargetZeroGoodBasePoint_of_twoSidedCoeffWitness
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    {pA pB : ℕ}
    (hpA : pA ∈ T.supportA) (hcoeffA : derivCoeff T.a pA ≠ 0)
    (hpB : pB ∈ T.supportB) (hcoeffB : derivCoeff T.b pB ≠ 0) :
    T.HasTargetZeroGoodBasePoint P := by
  have hpAFull : pA ∈ T.support := by
    simp [ABCTriple.support, hpA]
  have hpBFull : pB ∈ T.support := by
    simp [ABCTriple.support, hpB]
  let pAFull : {p : ℕ // p ∈ T.support} := ⟨pA, hpAFull⟩
  let pBFull : {p : ℕ // p ∈ T.support} := ⟨pB, hpBFull⟩
  let eA : T.FullTangent := coordinateTangent T.support pAFull
  let eB : T.FullTangent := coordinateTangent T.support pBFull
  let α : ℤ := derivCoeff T.a pA
  let β : ℤ := derivCoeff T.b pB
  let D : ℤ := β * α
  let x : T.FullTangent := β • eA + (-α) • eB
  have hpA_notB : pA ∉ T.supportB := by
    intro hpAB
    exact Finset.disjoint_left.mp hblocks.disjAB hpA hpAB
  have hpB_notA : pB ∉ T.supportA := by
    intro hpBA
    exact Finset.disjoint_left.mp hblocks.disjAB hpBA hpB
  have hcoeffB_at_A : derivCoeff T.b pA = 0 := by
    exact derivCoeff_eq_zero_of_not_mem_PrimeSupport T.b pA
      (by simpa [ABCTriple.supportB] using hpA_notB)
  have hcoeffA_at_B : derivCoeff T.a pB = 0 := by
    exact derivCoeff_eq_zero_of_not_mem_PrimeSupport T.a pB
      (by simpa [ABCTriple.supportA] using hpB_notA)
  have heA_a : formalDeriv T.support eA T.a = α := by
    simpa [eA, pAFull, α] using
      formalDeriv_coordinateTangent T.support T.a pAFull
  have heA_b : formalDeriv T.support eA T.b = 0 := by
    simpa [eA, pAFull, hcoeffB_at_A] using
      formalDeriv_coordinateTangent T.support T.b pAFull
  have heB_a : formalDeriv T.support eB T.a = 0 := by
    simpa [eB, pBFull, hcoeffA_at_B] using
      formalDeriv_coordinateTangent T.support T.a pBFull
  have heB_b : formalDeriv T.support eB T.b = β := by
    simpa [eB, pBFull, β] using
      formalDeriv_coordinateTangent T.support T.b pBFull
  have hDa : formalDeriv T.support x T.a = D := by
    calc
      formalDeriv T.support x T.a
          = formalDeriv T.support (β • eA + (-α) • eB) T.a := by
              rfl
      _ = formalDeriv T.support (β • eA) T.a
            + formalDeriv T.support ((-α) • eB) T.a := by
              rw [formalDeriv_add]
      _ = β * formalDeriv T.support eA T.a
            + (-α) * formalDeriv T.support eB T.a := by
              rw [formalDeriv_smul, formalDeriv_smul]
      _ = β * α + (-α) * 0 := by
              rw [heA_a, heB_a]
      _ = D := by
              simp [D]
  have hDb : formalDeriv T.support x T.b = -D := by
    calc
      formalDeriv T.support x T.b
          = formalDeriv T.support (β • eA + (-α) • eB) T.b := by
              rfl
      _ = formalDeriv T.support (β • eA) T.b
            + formalDeriv T.support ((-α) • eB) T.b := by
              rw [formalDeriv_add]
      _ = β * formalDeriv T.support eA T.b
            + (-α) * formalDeriv T.support eB T.b := by
              rw [formalDeriv_smul, formalDeriv_smul]
      _ = β * 0 + (-α) * β := by
              rw [heA_b, heB_b]
      _ = -D := by
              simp [D, mul_comm]
  have htarget : T.abTarget x = 0 :=
    T.abTarget_eq_zero_of_opposite_formalDeriv x D hDa hDb
  have hD_ne : D ≠ 0 := by
    exact mul_ne_zero hcoeffB hcoeffA
  have hW_ne : T.Wronskian x ≠ 0 :=
    T.Wronskian_ne_zero_of_opposite_formalDeriv x D hc hD_ne hDa hDb
  refine ⟨x, ?_⟩
  exact (T.targetZeroGoodBasePoint_iff P x).2
    ⟨T.mem_ABBase_of_abTarget_eq_zero P htarget, hW_ne, htarget⟩

/-- Two-sided support, plus quotient nonvanishing for the chosen coordinates,
produces a target-zero good base point. -/
theorem hasTargetZeroGoodBasePoint_of_twoSidedSupportWitness
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    {pA pB : ℕ}
    (hpA : pA ∈ T.supportA) (hdivA : T.a / pA ≠ 0)
    (hpB : pB ∈ T.supportB) (hdivB : T.b / pB ≠ 0) :
    T.HasTargetZeroGoodBasePoint P := by
  exact T.hasTargetZeroGoodBasePoint_of_twoSidedCoeffWitness P hblocks hc hpA
    (derivCoeff_ne_zero_of_mem_PrimeSupport_of_div_ne_zero T.a pA
      (by simpa [ABCTriple.supportA] using hpA) hdivA)
    hpB
    (derivCoeff_ne_zero_of_mem_PrimeSupport_of_div_ne_zero T.b pB
      (by simpa [ABCTriple.supportB] using hpB) hdivB)

/-- B0 main theorem, support form.

If both AB support blocks are nonempty, then there is a good base point with
zero AB target.  Consequently the C side does not need to absorb a nonzero
target at the qualitative level in the two-sided case. -/
theorem hasTargetZeroGoodBasePoint_of_twoSidedSupport_nonempty
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose) (hc : T.c ≠ 0)
    (hA : T.supportA.Nonempty) (hB : T.supportB.Nonempty) :
    T.HasTargetZeroGoodBasePoint P := by
  rcases hA with ⟨pA, hpA⟩
  rcases hB with ⟨pB, hpB⟩
  exact T.hasTargetZeroGoodBasePoint_of_twoSidedSupportWitness P hblocks hc hpA
    (div_ne_zero_of_mem_PrimeSupport T.a pA
      (by simpa [ABCTriple.supportA] using hpA))
    hpB
    (div_ne_zero_of_mem_PrimeSupport T.b pB
      (by simpa [ABCTriple.supportB] using hpB))

/-- A target-zero good base point is, in particular, a good base point. -/
theorem hasGoodBasePoint_of_hasTargetZeroGoodBasePoint
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasTargetZeroGoodBasePoint P) :
    T.HasGoodBasePoint P := by
  rcases h with ⟨x, hx⟩
  exact ⟨x, hx.1⟩

/-- In a realized profile, the two-sided target-zero base point already gives a
strict candidate. -/
theorem hasStrictCandidate_of_twoSidedSupport_nonempty_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hc : T.c ≠ 0)
    (hA : T.supportA.Nonempty) (hB : T.supportB.Nonempty) :
    T.HasStrictCandidate := by
  have htz : T.HasTargetZeroGoodBasePoint P :=
    T.hasTargetZeroGoodBasePoint_of_twoSidedSupport_nonempty P hblocks hc hA hB
  exact (T.hasStrictCandidate_iff_hasGoodBasePoint_of_profileRealizesCImage
    P hblocks hreal).2
    (T.hasGoodBasePoint_of_hasTargetZeroGoodBasePoint P htz)

end ABCTriple
end ABD2
