import ABD.ABD2.Fibration.BadSeedFrontierA

namespace ABD2

/-- The coordinate tangent supported at a single full-support coordinate. -/
def coordinateTangent (S : Finset ℕ) (p : {p : ℕ // p ∈ S}) : Tangent S :=
  fun q => if q = p then 1 else 0

@[simp]
theorem coordinateTangent_self
    (S : Finset ℕ) (p : {p : ℕ // p ∈ S}) :
    coordinateTangent S p p = 1 := by
  simp [coordinateTangent]

@[simp]
theorem coordinateTangent_ne
    (S : Finset ℕ) (p q : {p : ℕ // p ∈ S})
    (h : q ≠ p) :
    coordinateTangent S p q = 0 := by
  simp [coordinateTangent, h]

/-- Evaluating a formal derivative on a coordinate tangent extracts the corresponding
coefficient. -/
theorem formalDeriv_coordinateTangent
    (S : Finset ℕ) (n : ℕ) (p : {p : ℕ // p ∈ S}) :
    formalDeriv S (coordinateTangent S p) n = derivCoeff n p.1 := by
  unfold formalDeriv coordinateTangent
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _hq hq
    simp [hq]
  · intro hp
    exfalso
    exact hp (Finset.mem_univ p)

namespace ABCTriple

/-- Coefficient-level A-side witness for a nonzero Wronskian direction.

This is the safe second-stage A-frontier condition: if an A-coordinate has a
nonzero formal-derivative coefficient and the B block is disjoint from A, then
that coordinate direction makes the Wronskian nonzero. -/
theorem hasNonzeroWronskianDirection_of_aCoeffWitness
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hb : T.b ≠ 0) {p : ℕ}
    (hpA : p ∈ T.supportA) (hcoeff : derivCoeff T.a p ≠ 0) :
    T.HasNonzeroWronskianDirection := by
  have hpFull : p ∈ T.support := by
    simp [ABCTriple.support, hpA]
  let pFull : {p : ℕ // p ∈ T.support} := ⟨p, hpFull⟩
  let e : T.FullTangent := coordinateTangent T.support pFull
  have hpB : p ∉ T.supportB := by
    intro hpB
    exact Finset.disjoint_left.mp hblocks.disjAB hpA hpB
  have hcoeffB : derivCoeff T.b p = 0 := by
    exact derivCoeff_eq_zero_of_not_mem_PrimeSupport T.b p
      (by simpa [ABCTriple.supportB] using hpB)
  have hDa : formalDeriv T.support e T.a = derivCoeff T.a p := by
    simpa [e, pFull] using formalDeriv_coordinateTangent T.support T.a pFull
  have hDb : formalDeriv T.support e T.b = 0 := by
    simpa [e, pFull, hcoeffB] using formalDeriv_coordinateTangent T.support T.b pFull
  have hbInt : (T.b : ℤ) ≠ 0 := by
    exact_mod_cast hb
  have hprod : (T.b : ℤ) * derivCoeff T.a p ≠ 0 :=
    mul_ne_zero hbInt hcoeff
  refine ⟨e, ?_⟩
  simpa [ABCTriple.Wronskian, hDa, hDb] using (neg_ne_zero.mpr hprod)

/-- Coefficient-level B-side witness for a nonzero Wronskian direction. -/
theorem hasNonzeroWronskianDirection_of_bCoeffWitness
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (ha : T.a ≠ 0) {p : ℕ}
    (hpB : p ∈ T.supportB) (hcoeff : derivCoeff T.b p ≠ 0) :
    T.HasNonzeroWronskianDirection := by
  have hpFull : p ∈ T.support := by
    simp [ABCTriple.support, hpB]
  let pFull : {p : ℕ // p ∈ T.support} := ⟨p, hpFull⟩
  let e : T.FullTangent := coordinateTangent T.support pFull
  have hpA : p ∉ T.supportA := by
    intro hpA
    exact Finset.disjoint_left.mp hblocks.disjAB hpA hpB
  have hcoeffA : derivCoeff T.a p = 0 := by
    exact derivCoeff_eq_zero_of_not_mem_PrimeSupport T.a p
      (by simpa [ABCTriple.supportA] using hpA)
  have hDa : formalDeriv T.support e T.a = 0 := by
    simpa [e, pFull, hcoeffA] using formalDeriv_coordinateTangent T.support T.a pFull
  have hDb : formalDeriv T.support e T.b = derivCoeff T.b p := by
    simpa [e, pFull] using formalDeriv_coordinateTangent T.support T.b pFull
  have haInt : (T.a : ℤ) ≠ 0 := by
    exact_mod_cast ha
  have hprod : (T.a : ℤ) * derivCoeff T.b p ≠ 0 :=
    mul_ne_zero haInt hcoeff
  refine ⟨e, ?_⟩
  simpa [ABCTriple.Wronskian, hDa, hDb] using hprod

/-- A compact coefficient-witness condition for the second stage of A-frontier
elimination.  It says that one side of the AB support contains a coefficient
which genuinely contributes to the Wronskian. -/
def HasABCoeffWitness (T : ABCTriple) : Prop :=
  (T.b ≠ 0 ∧ ∃ p : ℕ, p ∈ T.supportA ∧ derivCoeff T.a p ≠ 0) ∨
    (T.a ≠ 0 ∧ ∃ p : ℕ, p ∈ T.supportB ∧ derivCoeff T.b p ≠ 0)

/-- A coefficient witness produces a nonzero Wronskian direction. -/
theorem hasNonzeroWronskianDirection_of_hasABCoeffWitness
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (h : T.HasABCoeffWitness) :
    T.HasNonzeroWronskianDirection := by
  rcases h with hA | hB
  · rcases hA with ⟨hb, p, hpA, hcoeff⟩
    exact T.hasNonzeroWronskianDirection_of_aCoeffWitness hblocks hb hpA hcoeff
  · rcases hB with ⟨ha, p, hpB, hcoeff⟩
    exact T.hasNonzeroWronskianDirection_of_bCoeffWitness hblocks ha hpB hcoeff

/-- A coefficient witness eliminates the BadSeedFrontier for every nonzero-gcd
profile. -/
theorem not_badSeedFrontier_of_hasABCoeffWitness
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (h : T.HasABCoeffWitness) :
    ¬ T.BadSeedFrontier P := by
  exact T.not_badSeedFrontier_of_hasNonzeroWronskianDirection P
    (T.hasNonzeroWronskianDirection_of_hasABCoeffWitness hblocks h)

/-- Canonical strict-skeleton consequence: under a realized C-image profile, a
coefficient witness already gives a strict candidate. -/
theorem hasStrictCandidate_of_hasABCoeffWitness_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (h : T.HasABCoeffWitness) :
    T.HasStrictCandidate := by
  have hbase : T.HasGoodBasePoint P :=
    (T.hasGoodBasePoint_iff_hasNonzeroWronskianDirection P).2
      (T.hasNonzeroWronskianDirection_of_hasABCoeffWitness hblocks h)
  exact (T.hasStrictCandidate_iff_hasGoodBasePoint_of_profileRealizesCImage
    P hblocks hreal).2 hbase

end ABCTriple
end ABD2
