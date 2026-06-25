import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step10HardElementary

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Oddness excludes evenness, in the public PureTwo3 API. -/
theorem not_even_of_odd {n : ℕ} (hn : Odd n) :
    ¬ Even n := by
  intro he
  exact odd_not_even_nat hn he

/-- Linear-exponent branch: at least one exponent is `1`.

This branch is intentionally kept out of Branch 5.  It will be analyzed as a
one-sided low-exponent frontier. -/
def LinearExponentBranch (F : NormalForm T P) : Prop :=
  F.u = 1 ∨ F.v = 1

/-- Both exponents are genuinely nonlinear. -/
def NonlinearExponentBranch (F : NormalForm T P) : Prop :=
  2 ≤ F.u ∧ 2 ≤ F.v

/-- Mixed-parity branch after the mod-8 obstruction has removed the even/even case. -/
def MixedParityBranch (F : NormalForm T P) : Prop :=
  (Even F.u ∧ Odd F.v) ∨ (Odd F.u ∧ Even F.v)

/-- Both exponents are odd.  This is the parity entrance to the hard branch. -/
def BothOddBranch (F : NormalForm T P) : Prop :=
  Odd F.u ∧ Odd F.v

/-- Branch 5 core data: both exponents are odd and at least `3`.

The coprimality condition is not stored here, because PureTwo3 proves it as the
canonical theorem `F.exponentCoprime`. -/
structure Branch5Data (F : NormalForm T P) where
  three_le_u : 3 ≤ F.u
  three_le_v : 3 ≤ F.v
  u_odd : Odd F.u
  v_odd : Odd F.v

/-- Branch 5 implies the both-odd branch. -/
theorem bothOddBranch_of_branch5Data
    (F : NormalForm T P) (B : Branch5Data F) :
    F.BothOddBranch :=
  ⟨B.u_odd, B.v_odd⟩

/-- Branch 5 is nonlinear. -/
theorem nonlinearExponentBranch_of_branch5Data
    (F : NormalForm T P) (B : Branch5Data F) :
    F.NonlinearExponentBranch := by
  exact ⟨le_trans (by decide : 2 ≤ 3) B.three_le_u,
    le_trans (by decide : 2 ≤ 3) B.three_le_v⟩

/-- The A-exponent is not even in Branch 5. -/
theorem u_not_even_of_branch5Data
    (F : NormalForm T P) (B : Branch5Data F) :
    ¬ Even F.u :=
  not_even_of_odd B.u_odd

/-- The B-exponent is not even in Branch 5. -/
theorem v_not_even_of_branch5Data
    (F : NormalForm T P) (B : Branch5Data F) :
    ¬ Even F.v :=
  not_even_of_odd B.v_odd

/-- Exponent coprimality is theorem-supplied in Branch 5. -/
theorem exponentCoprime_of_branch5Data
    (F : NormalForm T P) (_B : Branch5Data F) :
    Nat.Coprime F.u F.v :=
  F.exponentCoprime

/-- The mod-8 base constraint available in Branch 5: `p+q ≡ 0 mod 8`. -/
theorem p_add_q_mod8_eq_zero_of_branch5Data
    (F : NormalForm T P) (B : Branch5Data F) :
    (F.p + F.q) % 8 = 0 := by
  have H8 : ModEightConstraints F := F.modEightConstraints_real
  exact H8.odd_u_odd_v_forces_p_add_q_mod8_eq_zero
    (F.u_not_even_of_branch5Data B) (F.v_not_even_of_branch5Data B)

/-- Canonical Branch 5 package collecting the data and theorem-level elementary layer. -/
structure Branch5Package (F : NormalForm T P) where
  branch5 : Branch5Data F
  hard : HardElementaryGoals F

/-- Build the canonical Branch 5 package once the core Branch 5 data is supplied. -/
theorem branch5Package_of_branch5Data
    (F : NormalForm T P) (B : Branch5Data F) :
    Branch5Package F :=
  { branch5 := B
    hard := F.hardElementaryGoals }

/-- Extract exponent coprimality from a Branch 5 package. -/
theorem branch5Package_coprime
    (F : NormalForm T P) (K : Branch5Package F) :
    Nat.Coprime F.u F.v :=
  F.exponentCoprime_of_branch5Data K.branch5

/-- Extract the mod-8 base constraint from a Branch 5 package. -/
theorem branch5Package_mod8
    (F : NormalForm T P) (K : Branch5Package F) :
    (F.p + F.q) % 8 = 0 :=
  F.p_add_q_mod8_eq_zero_of_branch5Data K.branch5

/-- Extract the nonlinear-exponent fact from a Branch 5 package. -/
theorem branch5Package_nonlinear
    (F : NormalForm T P) (K : Branch5Package F) :
    F.NonlinearExponentBranch :=
  F.nonlinearExponentBranch_of_branch5Data K.branch5

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
