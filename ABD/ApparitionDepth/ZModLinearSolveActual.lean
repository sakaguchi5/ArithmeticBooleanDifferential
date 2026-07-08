/-
  ABD.ApparitionDepth.ZModLinearSolveActual

  Step 21R of the Apparition-Depth Decomposition project.

  This file proves the remaining linear-solve target from Step 21N in the case
  where `ZMod p` is available as a field.  The correction digit is chosen as a
  natural representative of

      -(q : ZMod p) * a⁻¹.

  This is the concrete algebraic content behind the earlier
  `ZModLinearExplicitSolveAtNonzero` certificate.
-/

import ABD.ApparitionDepth.BranchDerivativeUnit
import ABD.ApparitionDepth.ZModFieldLinearSolveProgress

namespace ApparitionDepth

/-! ## Actual field proof of the local linear solve -/

/-- In `ZMod p` for prime `p`, every nonzero element is a unit. -/
lemma zmod_isUnit_of_ne_zero
    {p : Nat} [NeZero p] [Fact p.Prime]
    {a : ZMod p} (ha : a ≠ 0) :
    IsUnit a := by
  have hval_ne : a.val ≠ 0 := by
    intro h
    exact ha ((ZMod.val_eq_zero a).mp h)
  have hval_pos : 0 < a.val := Nat.pos_of_ne_zero hval_ne
  have hval_lt : a.val < p := ZMod.val_lt a
  have hnot_dvd : ¬ p ∣ a.val := by
    intro hdiv
    have hp_le : p ≤ a.val := Nat.le_of_dvd hval_pos hdiv
    exact (not_le_of_gt hval_lt) hp_le
  have hcop_p_val : Nat.Coprime p a.val := by
    exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hnot_dvd
  have hcop_val_p : Nat.Coprime a.val p := hcop_p_val.symm
  have hunit_val : IsUnit ((a.val : Nat) : ZMod p) := by
    exact (ZMod.isUnit_iff_coprime a.val p).mpr hcop_val_p
  simpa [ZMod.natCast_zmod_val a] using hunit_val
/-- In `ZMod p` for prime `p`, a nonzero element cancels with its inverse
on the left. -/
lemma zmod_inv_mul_cancel_of_ne_zero
    {p : Nat} [NeZero p] [Fact p.Prime]
    {a : ZMod p} (ha : a ≠ 0) :
    a⁻¹ * a = (1 : ZMod p) := by
  exact ZMod.inv_mul_of_unit a (zmod_isUnit_of_ne_zero ha)

/-- In `ZMod p` for prime `p`, multiplication by a nonzero coefficient is
right-cancellable. -/
lemma zmod_mul_right_cancel_of_ne_zero
    {p : Nat} [NeZero p] [Fact p.Prime]
    {a x y : ZMod p} (ha : a ≠ 0)
    (h : x * a = y * a) :
    x = y := by
  have hunit : a * a⁻¹ = (1 : ZMod p) := by
    exact ZMod.mul_inv_of_unit a (zmod_isUnit_of_ne_zero ha)
  calc
    x = x * (a * a⁻¹) := by
          rw [hunit, mul_one]
    _ = (x * a) * a⁻¹ := by
          rw [mul_assoc]
    _ = (y * a) * a⁻¹ := by
          rw [h]
    _ = y * (a * a⁻¹) := by
          rw [mul_assoc]
    _ = y := by
          rw [hunit, mul_one]

/-- In `ZMod p` for prime `p`, a nonzero coefficient solves every linear
Hensel correction equation `q + t*a = 0` with an explicit Nat witness. -/
theorem zmodLinearExplicitSolveAtNonzero_of_prime
    {p : Nat} [NeZero p] [Fact p.Prime] (a : ZMod p) :
    ZModLinearExplicitSolveAtNonzero p a := by
  unfold ZModLinearExplicitSolveAtNonzero
  intro ha q
  unfold ZModLinearExplicitSolved
  let x : ZMod p := -(q : ZMod p) * a⁻¹
  refine ⟨x.val, ?_⟩
  have hx : ((x.val : Nat) : ZMod p) = x := by
    exact ZMod.natCast_zmod_val x
  constructor
  · unfold ZModLinearSolutionWitness
    calc
      (q : ZMod p) + ((x.val : Nat) : ZMod p) * a
          = (q : ZMod p) + x * a := by
              rw [hx]
      _ = (q : ZMod p) + (-(q : ZMod p) * a⁻¹) * a := by
              rfl
      _ = (q : ZMod p) + -(q : ZMod p) * (a⁻¹ * a) := by
              ring
      _ = 0 := by
              rw [zmod_inv_mul_cancel_of_ne_zero ha]
              ring
  · unfold ZModLinearUniquenessWitness
    unfold FiniteHenselLinearSolutionUnique
    intro t1 t2 h1 h2
    unfold FiniteHenselLinearEquation at h1 h2
    have hmul : (t1 : ZMod p) * a = (t2 : ZMod p) * a := by
      apply add_left_cancel (a := (q : ZMod p))
      calc
        (q : ZMod p) + (t1 : ZMod p) * a
            = 0 := h1
        _ = (q : ZMod p) + (t2 : ZMod p) * a := h2.symm
    exact zmod_mul_right_cancel_of_ne_zero ha hmul

/-- Prime-modulus version of the older certificate API. -/
theorem zmodLinearSolveCertificate_of_prime
    {p : Nat} [NeZero p] [Fact p.Prime] (a : ZMod p) :
    ZModLinearSolveCertificate p a :=
  zmodLinearSolveCertificate_of_explicitAtNonzero
    (zmodLinearExplicitSolveAtNonzero_of_prime a)

/-- Branch-seed derivative version of the actual prime-modulus linear solve. -/
theorem branchSeedZModLinearExplicitSolveAtNonzero_of_prime
    {g p d j : Nat} [NeZero p] [Fact p.Prime] :
    BranchSeedZModLinearExplicitSolveAtNonzero g p d j :=
  zmodLinearExplicitSolveAtNonzero_of_prime
    (branchSeedDerivativeValue g p d j)

/-- Concrete derivative version of the actual prime-modulus linear solve. -/
theorem henselDerivativeZModLinearExplicitSolveAtNonzero_of_prime
    {omega p d : Nat} [NeZero p] [Fact p.Prime] :
    HenselDerivativeZModLinearExplicitSolveAtNonzero omega p d :=
  zmodLinearExplicitSolveAtNonzero_of_prime
    (branchDerivativeValue omega p d)

/-- Branch-seed derivative certificate obtained from the prime-modulus proof. -/
theorem branchSeedZModLinearSolveCertificate_of_prime
    {g p d j : Nat} [NeZero p] [Fact p.Prime] :
    BranchSeedZModLinearSolveCertificate g p d j :=
  branchSeedZModLinearSolveCertificate_of_explicitAtNonzero
    (branchSeedZModLinearExplicitSolveAtNonzero_of_prime
      (g := g) (p := p) (d := d) (j := j))

/-- Concrete derivative certificate obtained from the prime-modulus proof. -/
theorem henselDerivativeZModLinearSolveCertificate_of_prime
    {omega p d : Nat} [NeZero p] [Fact p.Prime] :
    HenselDerivativeZModLinearSolveCertificate omega p d :=
  henselDerivativeZModLinearSolveCertificate_of_explicitAtNonzero
    (henselDerivativeZModLinearExplicitSolveAtNonzero_of_prime
      (omega := omega) (p := p) (d := d))

/-- Concrete correction solve from derivative nonvanishing, using the actual
prime-modulus linear solve. -/
theorem finiteHenselCorrectionSolved_of_prime_derivativeNonzero
    {omega q p d : Nat} [NeZero p] [Fact p.Prime]
    (hderiv : HenselDerivativeNonzeroModP omega p d) :
    FiniteHenselCorrectionSolved omega q p d :=
  finiteHenselCorrectionSolved_of_linearSolved
    (correctionLinearSolved_of_zmodCertificate
      (henselDerivativeZModLinearSolveCertificate_of_prime
        (omega := omega) (p := p) (d := d))
      hderiv)

end ApparitionDepth
