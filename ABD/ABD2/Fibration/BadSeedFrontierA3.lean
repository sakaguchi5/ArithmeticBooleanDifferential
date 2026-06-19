import ABD.ABD2.Fibration.BadSeedFrontierA2

namespace ABD2

/-- A prime-support coordinate with nonzero quotient gives a nonzero formal-
derivative coefficient.

This file keeps the last purely arithmetic bridge explicit: from
`p ∈ PrimeSupport n` we know the valuation factor is nonzero, while the
separate hypothesis `n / p ≠ 0` records that the Leibniz quotient factor is also
nonzero.  Later this quotient hypothesis can be discharged from the standard
prime-support arithmetic API. -/
theorem derivCoeff_ne_zero_of_mem_PrimeSupport_of_div_ne_zero
    (n p : ℕ) (hp : p ∈ PrimeSupport n) (hdiv : n / p ≠ 0) :
    derivCoeff n p ≠ 0 := by
  have hvalNat : n.factorization p ≠ 0 := by
    exact Finsupp.mem_support_iff.mp (by simpa [PrimeSupport] using hp)
  have hvalInt : ((val n p : ℕ) : ℤ) ≠ 0 := by
    unfold val
    exact_mod_cast hvalNat
  have hdivInt : (((n / p : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast hdiv
  unfold derivCoeff
  exact mul_ne_zero hvalInt hdivInt

namespace ABCTriple

/-- Support-level AB witness: one AB-side support coordinate contributes a
nonzero Leibniz quotient, and the opposite scalar in the Wronskian is nonzero. -/
def HasABSupportWitness (T : ABCTriple) : Prop :=
  (T.b ≠ 0 ∧ ∃ p : ℕ, p ∈ T.supportA ∧ T.a / p ≠ 0) ∨
    (T.a ≠ 0 ∧ ∃ p : ℕ, p ∈ T.supportB ∧ T.b / p ≠ 0)

/-- An A-side support witness gives the coefficient witness used in A2. -/
theorem hasABCoeffWitness_of_aSupportWitness
    (T : ABCTriple) (hb : T.b ≠ 0) {p : ℕ}
    (hpA : p ∈ T.supportA) (hdiv : T.a / p ≠ 0) :
    T.HasABCoeffWitness := by
  left
  refine ⟨hb, p, hpA, ?_⟩
  exact derivCoeff_ne_zero_of_mem_PrimeSupport_of_div_ne_zero T.a p
    (by simpa [ABCTriple.supportA] using hpA) hdiv

/-- A B-side support witness gives the coefficient witness used in A2. -/
theorem hasABCoeffWitness_of_bSupportWitness
    (T : ABCTriple) (ha : T.a ≠ 0) {p : ℕ}
    (hpB : p ∈ T.supportB) (hdiv : T.b / p ≠ 0) :
    T.HasABCoeffWitness := by
  right
  refine ⟨ha, p, hpB, ?_⟩
  exact derivCoeff_ne_zero_of_mem_PrimeSupport_of_div_ne_zero T.b p
    (by simpa [ABCTriple.supportB] using hpB) hdiv

/-- A support-level witness gives the coefficient-level witness. -/
theorem hasABCoeffWitness_of_hasABSupportWitness
    (T : ABCTriple) (h : T.HasABSupportWitness) :
    T.HasABCoeffWitness := by
  rcases h with hA | hB
  · rcases hA with ⟨hb, p, hpA, hdiv⟩
    exact T.hasABCoeffWitness_of_aSupportWitness hb hpA hdiv
  · rcases hB with ⟨ha, p, hpB, hdiv⟩
    exact T.hasABCoeffWitness_of_bSupportWitness ha hpB hdiv

/-- A support-level witness produces a nonzero Wronskian direction. -/
theorem hasNonzeroWronskianDirection_of_hasABSupportWitness
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (h : T.HasABSupportWitness) :
    T.HasNonzeroWronskianDirection := by
  exact T.hasNonzeroWronskianDirection_of_hasABCoeffWitness hblocks
    (T.hasABCoeffWitness_of_hasABSupportWitness h)

/-- A support-level witness eliminates the A-frontier for every nonzero-gcd
profile. -/
theorem not_badSeedFrontier_of_hasABSupportWitness
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (h : T.HasABSupportWitness) :
    ¬ T.BadSeedFrontier P := by
  exact T.not_badSeedFrontier_of_hasABCoeffWitness P hblocks
    (T.hasABCoeffWitness_of_hasABSupportWitness h)

/-- A direct A-side support-witness elimination form. -/
theorem not_badSeedFrontier_of_aSupportWitness
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hb : T.b ≠ 0) {p : ℕ}
    (hpA : p ∈ T.supportA) (hdiv : T.a / p ≠ 0) :
    ¬ T.BadSeedFrontier P := by
  exact T.not_badSeedFrontier_of_hasABCoeffWitness P hblocks
    (T.hasABCoeffWitness_of_aSupportWitness hb hpA hdiv)

/-- A direct B-side support-witness elimination form. -/
theorem not_badSeedFrontier_of_bSupportWitness
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (ha : T.a ≠ 0) {p : ℕ}
    (hpB : p ∈ T.supportB) (hdiv : T.b / p ≠ 0) :
    ¬ T.BadSeedFrontier P := by
  exact T.not_badSeedFrontier_of_hasABCoeffWitness P hblocks
    (T.hasABCoeffWitness_of_bSupportWitness ha hpB hdiv)

/-- If the A support is nonempty and every A-support coordinate has nonzero
quotient, then the support-level witness exists. -/
theorem hasABSupportWitness_of_supportA_nonempty
    (T : ABCTriple) (hb : T.b ≠ 0)
    (hA : T.supportA.Nonempty)
    (hdiv : ∀ {p : ℕ}, p ∈ T.supportA → T.a / p ≠ 0) :
    T.HasABSupportWitness := by
  rcases hA with ⟨p, hpA⟩
  left
  exact ⟨hb, p, hpA, hdiv hpA⟩

/-- If the B support is nonempty and every B-support coordinate has nonzero
quotient, then the support-level witness exists. -/
theorem hasABSupportWitness_of_supportB_nonempty
    (T : ABCTriple) (ha : T.a ≠ 0)
    (hB : T.supportB.Nonempty)
    (hdiv : ∀ {p : ℕ}, p ∈ T.supportB → T.b / p ≠ 0) :
    T.HasABSupportWitness := by
  rcases hB with ⟨p, hpB⟩
  right
  exact ⟨ha, p, hpB, hdiv hpB⟩

/-- Strict-skeleton consequence from a support-level witness. -/
theorem hasStrictCandidate_of_hasABSupportWitness_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (h : T.HasABSupportWitness) :
    T.HasStrictCandidate := by
  exact T.hasStrictCandidate_of_hasABCoeffWitness_of_profileRealizesCImage
    P hblocks hreal (T.hasABCoeffWitness_of_hasABSupportWitness h)

end ABCTriple
end ABD2
