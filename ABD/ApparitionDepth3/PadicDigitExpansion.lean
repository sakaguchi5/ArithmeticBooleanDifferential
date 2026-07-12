/-
  ABD.ApparitionDepth3.PadicDigitExpansion

  Stage 13:
    * assemble the adjacent ordinary p-adic digit equations;
    * identify every finite representative with its complete digit prefix.
-/

import ABD.ApparitionDepth3.BranchTreeExact

namespace ApparitionDepth3

/-- The ordinary base-p digit prefix of length r. -/
noncomputable def branchPadicDigitSum
    (g p d j r : Nat) [Fact p.Prime] : Nat :=
  Finset.sum (Finset.range r) (fun k => branchPadicDigitNat g p d j k * p ^ k)

/-- The level-zero representative is the unique residue modulo 1. -/
theorem branchPadicRepresentative_zero
    {g p d j : Nat} [Fact p.Prime] :
    branchPadicRepresentative g p d j 0 = 0 := by
  have hlt := branchPadicRepresentative_lt_modulus
    (g := g) (p := p) (d := d) (j := j) (r := 0)
  simp only [pow_zero] at hlt
  omega

/-- Every finite representative is exactly the prefix sum of its ordinary
base-p digits. -/
theorem branchPadicRepresentative_eq_digitSum
    {g p d j r : Nat} [Fact p.Prime] :
    branchPadicRepresentative g p d j r =
      branchPadicDigitSum g p d j r := by
  induction r with
  | zero =>
      simp [branchPadicDigitSum, branchPadicRepresentative_zero]
  | succ r ih =>
      rw [branchPadicRepresentative_succ_decomposition, ih]
      simp [branchPadicDigitSum, Finset.sum_range_succ]

/-- Coordinate form: the p-adic reduction is the cast of its complete digit
prefix. -/
theorem branchPadicReduction_eq_digitSum
    {g p d j r : Nat} [Fact p.Prime] :
    branchPadicReduction g p d j r =
      (branchPadicDigitSum g p d j r : ZMod (p ^ r)) := by
  rw [← branchPadicRepresentative_eq_digitSum]
  exact (branchPadicRepresentative_cast
    (g := g) (p := p) (d := d) (j := j) (r := r)).symm

/-- The next digit prefix extends the previous prefix by one term. -/
theorem branchPadicDigitSum_succ
    {g p d j r : Nat} [Fact p.Prime] :
    branchPadicDigitSum g p d j (r + 1) =
      branchPadicDigitSum g p d j r +
        branchPadicDigitNat g p d j r * p ^ r := by
  simp [branchPadicDigitSum, Finset.sum_range_succ]

/-- Public stage-13 package: ordinary digits, boundedness, finite sums, and the
Witt-coordinate boundary for every positive coordinate. -/
structure PadicDigitExpansionResult
    (g p d j : Nat) [Fact p.Prime] : Prop where
  digitBound : ∀ r : Nat, branchPadicDigitNat g p d j r < p
  finiteExpansion : ∀ r : Nat,
    branchPadicRepresentative g p d j r =
      Finset.sum (Finset.range r)
        (fun k => branchPadicDigitNat g p d j k * p ^ k)
  reductionExpansion : ∀ r : Nat,
    branchPadicReduction g p d j r =
      ((Finset.sum (Finset.range r)
          (fun k => branchPadicDigitNat g p d j k * p ^ k))
        : ZMod (p ^ r))
  wittCoeffZero : ∀ n : Nat, 0 < n →
    (branchWittRoot g p d j).coeff n = 0

/-- Concrete construction of the complete ordinary-digit expansion package. -/
theorem padicDigitExpansionResult
    {g p d j : Nat} [Fact p.Prime] :
    PadicDigitExpansionResult g p d j := by
  refine
    { digitBound := fun _ => branchPadicDigitNat_lt_prime
      finiteExpansion := ?_
      reductionExpansion := ?_
      wittCoeffZero := ?_ }
  · intro r
    simpa only [branchPadicDigitSum] using
      (branchPadicRepresentative_eq_digitSum
        (g := g) (p := p) (d := d) (j := j) (r := r))
  · intro r
    simpa [branchPadicDigitSum, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using
      (branchPadicReduction_eq_digitSum
        (g := g) (p := p) (d := d) (j := j) (r := r))
  · intro n hn
    exact branchWittRoot_coeff_pos hn

end ApparitionDepth3
