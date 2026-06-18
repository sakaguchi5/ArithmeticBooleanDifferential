import ABD.ABD2.Lattice.CoeffFinsetGCD

namespace ABD2

/-- If at least one coefficient is nonzero, then the finite coefficient gcd is nonzero.

This avoids reopening the finite Bezout construction.  The proof uses only the
already-proved fact that the finite gcd divides every coefficient: if the gcd were
`0`, then `0` would divide a nonzero coefficient, impossible. -/
theorem coeffFinsetGCD_ne_zero_of_exists_nonzero_coeff
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ)
    (h : ∃ i : ι, coeff i ≠ 0) :
    CoeffFinsetGCD coeff ≠ 0 := by
  intro hg
  rcases h with ⟨i, hi⟩
  have hdiv : CoeffFinsetGCD coeff ∣ coeff i :=
    coeffFinsetGCD_dvd_coeff coeff i
  rw [hg] at hdiv
  exact hi (by
    simpa using hdiv)

/-- Contrapositive-style convenience: if the finite coefficient gcd is zero, every
coefficient is zero. -/
theorem coeff_eq_zero_of_coeffFinsetGCD_eq_zero
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ)
    (hg : CoeffFinsetGCD coeff = 0) (i : ι) :
    coeff i = 0 := by
  have hdiv : CoeffFinsetGCD coeff ∣ coeff i :=
    coeffFinsetGCD_dvd_coeff coeff i
  rw [hg] at hdiv
  simpa using hdiv

end ABD2
