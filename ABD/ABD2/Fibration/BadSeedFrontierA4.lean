import ABD.ABD2.Fibration.BadSeedFrontierA3

namespace ABD2

/-- A prime-support coordinate has a nonzero Leibniz quotient.

This closes the last arithmetic gap left in `BadSeedFrontierA3`: membership in
`PrimeSupport n` means that `p` is a genuine nonzero divisor of `n`, hence
`n / p` is nonzero. -/
theorem div_ne_zero_of_mem_PrimeSupport
    (n p : ℕ) (hp : p ∈ PrimeSupport n) :
    n / p ≠ 0 := by
  have hval_ne : n.factorization p ≠ 0 := by
    exact Finsupp.mem_support_iff.mp (by simpa [PrimeSupport] using hp)
  have hnot_cases : ¬ (¬ Nat.Prime p ∨ ¬ p ∣ n ∨ n = 0) := by
    intro hcases
    exact hval_ne ((Nat.factorization_eq_zero_iff n p).2 hcases)
  have hpPrime : Nat.Prime p := by
    by_contra hnp
    exact hnot_cases (Or.inl hnp)
  have hpdvd : p ∣ n := by
    by_contra hndvd
    exact hnot_cases (Or.inr (Or.inl hndvd))
  have hnz : n ≠ 0 := by
    intro hn
    exact hnot_cases (Or.inr (Or.inr hn))
  have hp_pos : 0 < p := hpPrime.pos
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hnz
  have hp_le_n : p ≤ n := Nat.le_of_dvd hn_pos hpdvd
  exact Nat.ne_of_gt (Nat.div_pos hp_le_n hp_pos)

namespace ABCTriple

/-- A nonempty A-support, together with a nonzero opposite Wronskian scalar,
produces the support-level witness from A3. -/
theorem hasABSupportWitness_of_supportA_nonempty_arithmetic
    (T : ABCTriple) (hb : T.b ≠ 0)
    (hA : T.supportA.Nonempty) :
    T.HasABSupportWitness := by
  apply T.hasABSupportWitness_of_supportA_nonempty hb hA
  intro p hpA
  exact div_ne_zero_of_mem_PrimeSupport T.a p
    (by simpa [ABCTriple.supportA] using hpA)

/-- A nonempty B-support, together with a nonzero opposite Wronskian scalar,
produces the support-level witness from A3. -/
theorem hasABSupportWitness_of_supportB_nonempty_arithmetic
    (T : ABCTriple) (ha : T.a ≠ 0)
    (hB : T.supportB.Nonempty) :
    T.HasABSupportWitness := by
  apply T.hasABSupportWitness_of_supportB_nonempty ha hB
  intro p hpB
  exact div_ne_zero_of_mem_PrimeSupport T.b p
    (by simpa [ABCTriple.supportB] using hpB)

/-- Arithmetic AB-support witness: once both AB-side scalars are nonzero, it is
enough that at least one of the A/B supports is nonempty. -/
theorem hasABSupportWitness_of_ABSupport_nonempty
    (T : ABCTriple) (ha : T.a ≠ 0) (hb : T.b ≠ 0)
    (hAB : T.supportA.Nonempty ∨ T.supportB.Nonempty) :
    T.HasABSupportWitness := by
  rcases hAB with hA | hB
  · exact T.hasABSupportWitness_of_supportA_nonempty_arithmetic hb hA
  · exact T.hasABSupportWitness_of_supportB_nonempty_arithmetic ha hB

/-- A-main theorem, support form.

For a nonzero-gcd C-image profile, the A-frontier is absent as soon as the AB
side is genuinely nontrivial: both AB scalars are nonzero and at least one AB
support block is nonempty.  Thus the first frontier is not a profile-specific
congruence obstruction; it is only the completely Wronskian-zero degeneration. -/
theorem not_badSeedFrontier_of_ABSupport_nonempty
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (ha : T.a ≠ 0) (hb : T.b ≠ 0)
    (hAB : T.supportA.Nonempty ∨ T.supportB.Nonempty) :
    ¬ T.BadSeedFrontier P := by
  exact T.not_badSeedFrontier_of_hasABSupportWitness P hblocks
    (T.hasABSupportWitness_of_ABSupport_nonempty ha hb hAB)

/-- Product-nonzero version of the A-main theorem. -/
theorem not_badSeedFrontier_of_ABSupport_nonempty_of_mul_ne_zero
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hab : T.a * T.b ≠ 0)
    (hAB : T.supportA.Nonempty ∨ T.supportB.Nonempty) :
    ¬ T.BadSeedFrontier P := by
  have ha : T.a ≠ 0 := by
    intro ha0
    exact hab (by simp [ha0])
  have hb : T.b ≠ 0 := by
    intro hb0
    exact hab (by simp [hb0])
  exact T.not_badSeedFrontier_of_ABSupport_nonempty P hblocks ha hb hAB

/-- Strict-skeleton consequence of the support-form A-main theorem. -/
theorem hasStrictCandidate_of_ABSupport_nonempty_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (ha : T.a ≠ 0) (hb : T.b ≠ 0)
    (hAB : T.supportA.Nonempty ∨ T.supportB.Nonempty) :
    T.HasStrictCandidate := by
  exact T.hasStrictCandidate_of_hasABSupportWitness_of_profileRealizesCImage
    P hblocks hreal
    (T.hasABSupportWitness_of_ABSupport_nonempty ha hb hAB)

/-- Product-nonzero strict-skeleton consequence of the A-main theorem. -/
theorem hasStrictCandidate_of_ABSupport_nonempty_of_mul_ne_zero_of_profileRealizesCImage
    (T : ABCTriple) (P : T.CImageProfile)
    (hblocks : T.SupportBlocksDecompose)
    (hreal : T.ProfileRealizesCImage P)
    (hab : T.a * T.b ≠ 0)
    (hAB : T.supportA.Nonempty ∨ T.supportB.Nonempty) :
    T.HasStrictCandidate := by
  have ha : T.a ≠ 0 := by
    intro ha0
    exact hab (by simp [ha0])
  have hb : T.b ≠ 0 := by
    intro hb0
    exact hab (by simp [hb0])
  exact T.hasStrictCandidate_of_ABSupport_nonempty_of_profileRealizesCImage
    P hblocks hreal ha hb hAB

end ABCTriple
end ABD2
