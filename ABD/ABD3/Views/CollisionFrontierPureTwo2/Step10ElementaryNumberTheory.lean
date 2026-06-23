import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step9SyncGraph

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- The A prime is an odd prime in the elementary sense: it is not `2`. -/
theorem p_is_odd_prime_boundary (F : NormalForm T P) :
    Nat.Prime F.p ∧ F.p ≠ 2 :=
  ⟨F.p_prime, F.p_ne_two⟩

/-- The B prime is an odd prime in the elementary sense: it is not `2`. -/
theorem q_is_odd_prime_boundary (F : NormalForm T P) :
    Nat.Prime F.q ∧ F.q ≠ 2 :=
  ⟨F.q_prime, F.q_ne_two⟩

/-- The A base is at least `3`. -/
theorem three_le_p (F : NormalForm T P) :
    3 ≤ F.p := by
  have h2 : 2 ≤ F.p := F.p_prime.two_le
  have hne : F.p ≠ 2 := F.p_ne_two
  omega

/-- The B base is at least `4`; the sharper `5 ≤ q` is kept in the elementary
package below because it uses the primality boundary together with `p < q`. -/
theorem four_le_q (F : NormalForm T P) :
    4 ≤ F.q := by
  have hp3 : 3 ≤ F.p := F.three_le_p
  have hpq : F.p < F.q := F.p_lt_q
  omega

/-- Elementary lower-bound target: sharpen `4 ≤ q` to `5 ≤ q` using primality. -/
def FiveLeQGoal (F : NormalForm T P) : Prop :=
  5 ≤ F.q

/-- Elementary lower-bound target: from `p^u + q^v = 2^w` and `p ≥ 3`, `q ≥ 5`,
deduce `3 ≤ w`. -/
def ThreeLeWGoal (F : NormalForm T P) : Prop :=
  3 ≤ F.w

/-- Mod-8 source equation target.  This is the first clean modular form of
`p^u + q^v = 2^w` once `3 ≤ w` is available. -/
def SourceSumModEightGoal (F : NormalForm T P) : Prop :=
  (F.p ^ F.u + F.q ^ F.v) % 8 = 0

/-- Parity obstruction target: the two exponents cannot both be even. -/
def NotBothExponentsEvenGoal (F : NormalForm T P) : Prop :=
  ¬ (Even F.u ∧ Even F.v)

/-- First mod-8 branch target: if `u` is even and `v` is odd then `q ≡ 7 mod 8`. -/
def EvenUOddVForcesQSevenModEightGoal (F : NormalForm T P) : Prop :=
  Even F.u → ¬ Even F.v → F.q % 8 = 7

/-- Second mod-8 branch target: if `u` is odd and `v` is even then `p ≡ 7 mod 8`. -/
def OddUEvenVForcesPSevenModEightGoal (F : NormalForm T P) : Prop :=
  ¬ Even F.u → Even F.v → F.p % 8 = 7

/-- Third mod-8 branch target: if both exponents are odd then `p + q ≡ 0 mod 8`. -/
def OddUOddVForcesPAddQZeroModEightGoal (F : NormalForm T P) : Prop :=
  ¬ Even F.u → ¬ Even F.v → (F.p + F.q) % 8 = 0

/-- Collected elementary-number-theory layer for the pure two-power model.  This
package is independent of the `{2}` C-surplus identification from Steps 8--9; it
is the remaining parity/mod-8 refinement that can be added to the frontier once
proved. -/
structure ElementaryConstraints (F : NormalForm T P) where
  five_le_q : F.FiveLeQGoal
  three_le_w : F.ThreeLeWGoal
  source_sum_mod_eight : F.SourceSumModEightGoal
  not_both_exponents_even : F.NotBothExponentsEvenGoal
  even_u_odd_v_forces_q_mod8_eq_7 : F.EvenUOddVForcesQSevenModEightGoal
  odd_u_even_v_forces_p_mod8_eq_7 : F.OddUEvenVForcesPSevenModEightGoal
  odd_u_odd_v_forces_p_add_q_mod8_eq_zero : F.OddUOddVForcesPAddQZeroModEightGoal

/-- Remaining elementary target for enriching the final three-rejection frontier
with parity and mod-8 information. -/
def ElementaryConstraintsGoal (F : NormalForm T P) : Prop :=
  Nonempty (ElementaryConstraints F)

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
