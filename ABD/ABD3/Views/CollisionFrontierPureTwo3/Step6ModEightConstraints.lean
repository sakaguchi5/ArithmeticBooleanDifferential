import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step5SourceCongruence

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

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

/-- Pure mod-8 residue package, separated from lower-bound facts. -/
structure ModEightConstraints (F : NormalForm T P) where
  source_sum_mod_eight : F.SourceSumModEightGoal
  not_both_exponents_even : F.NotBothExponentsEvenGoal
  even_u_odd_v_forces_q_mod8_eq_7 : F.EvenUOddVForcesQSevenModEightGoal
  odd_u_even_v_forces_p_mod8_eq_7 : F.OddUEvenVForcesPSevenModEightGoal
  odd_u_odd_v_forces_p_add_q_mod8_eq_zero :
    F.OddUOddVForcesPAddQZeroModEightGoal

def ModEightConstraintsGoal (F : NormalForm T P) : Prop :=
  Nonempty (ModEightConstraints F)

private theorem not_both_even_of_odd_bases_sum_mod_eight
    {x y u v : ℕ}
    (hx : Odd x) (hy : Odd y)
    (hsum : ((x ^ u % 8) + (y ^ v % 8)) % 8 = 0) :
    ¬ (Even u ∧ Even v) := by
  intro hboth
  rcases hboth with ⟨hu_even, hv_even⟩
  have hxmod : x ^ u % 8 = 1 :=
    odd_pow_even_exp_mod_eight hx hu_even
  have hymod : y ^ v % 8 = 1 :=
    odd_pow_even_exp_mod_eight hy hv_even
  have hbad : (1 + 1) % 8 = 0 := by
    simp [hxmod, hymod] at hsum
  exact (by decide : ¬ (1 + 1) % 8 = 0) hbad

private theorem even_odd_forces_right_mod8_eq_seven
    {x y u v : ℕ}
    (hx : Odd x) (hy : Odd y)
    (hsum : ((x ^ u % 8) + (y ^ v % 8)) % 8 = 0)
    (hu_even : Even u) (hv_not_even : ¬ Even v) :
    y % 8 = 7 := by
  have hv_odd : Odd v := Nat.not_even_iff_odd.mp hv_not_even
  have hxmod : x ^ u % 8 = 1 :=
    odd_pow_even_exp_mod_eight hx hu_even
  have hymod : y ^ v % 8 = y % 8 :=
    odd_pow_odd_exp_mod_eight hy hv_odd
  have hysum : (1 + y % 8) % 8 = 0 := by
    simpa [hxmod, hymod] using hsum
  exact mod8_eq_seven_of_one_add_mod8_eq_zero
    (Nat.mod_lt y (by decide : 0 < 8)) hysum

private theorem odd_even_forces_left_mod8_eq_seven
    {x y u v : ℕ}
    (hx : Odd x) (hy : Odd y)
    (hsum : ((x ^ u % 8) + (y ^ v % 8)) % 8 = 0)
    (hu_not_even : ¬ Even u) (hv_even : Even v) :
    x % 8 = 7 := by
  have hu_odd : Odd u := Nat.not_even_iff_odd.mp hu_not_even
  have hxmod : x ^ u % 8 = x % 8 :=
    odd_pow_odd_exp_mod_eight hx hu_odd
  have hymod : y ^ v % 8 = 1 :=
    odd_pow_even_exp_mod_eight hy hv_even
  have hxsum : (x % 8 + 1) % 8 = 0 := by
    simpa [hxmod, hymod, Nat.add_comm] using hsum
  have hxsum' : (1 + x % 8) % 8 = 0 := by
    simpa [Nat.add_comm] using hxsum
  exact mod8_eq_seven_of_one_add_mod8_eq_zero
    (Nat.mod_lt x (by decide : 0 < 8)) hxsum'

private theorem odd_odd_forces_base_sum_mod8_zero
    {x y u v : ℕ}
    (hx : Odd x) (hy : Odd y)
    (hsum : ((x ^ u % 8) + (y ^ v % 8)) % 8 = 0)
    (hu_not_even : ¬ Even u) (hv_not_even : ¬ Even v) :
    (x + y) % 8 = 0 := by
  have hu_odd : Odd u := Nat.not_even_iff_odd.mp hu_not_even
  have hv_odd : Odd v := Nat.not_even_iff_odd.mp hv_not_even
  have hxmod : x ^ u % 8 = x % 8 :=
    odd_pow_odd_exp_mod_eight hx hu_odd
  have hymod : y ^ v % 8 = y % 8 :=
    odd_pow_odd_exp_mod_eight hy hv_odd
  have hxysum : (x % 8 + y % 8) % 8 = 0 := by
    simpa [hxmod, hymod] using hsum
  calc
    (x + y) % 8
        = (x % 8 + y % 8) % 8 := by
            rw [Nat.add_mod]
    _ = 0 := hxysum

/-- Realization of the mod-8 package. -/
theorem modEightConstraints_real (F : NormalForm T P) :
    ModEightConstraints F := by
  have hp_odd : Odd F.p := F.p_odd
  have hq_odd : Odd F.q := F.q_odd
  have hb : BasicBounds F := F.basicBounds_real
  have hmod8 : F.SourceSumModEightGoal :=
    F.source_sum_mod_eight_real hb.three_le_w
  have hsum8 :
      ((F.p ^ F.u % 8) + (F.q ^ F.v % 8)) % 8 = 0 :=
    residue_sum_mod_eight_of_source_sum_mod_eight F hmod8
  refine
    { source_sum_mod_eight := hmod8
      not_both_exponents_even := ?_
      even_u_odd_v_forces_q_mod8_eq_7 := ?_
      odd_u_even_v_forces_p_mod8_eq_7 := ?_
      odd_u_odd_v_forces_p_add_q_mod8_eq_zero := ?_ }
  · exact not_both_even_of_odd_bases_sum_mod_eight hp_odd hq_odd hsum8
  · intro hu_even hv_not_even
    exact even_odd_forces_right_mod8_eq_seven
      hp_odd hq_odd hsum8 hu_even hv_not_even
  · intro hu_not_even hv_even
    exact odd_even_forces_left_mod8_eq_seven
      hp_odd hq_odd hsum8 hu_not_even hv_even
  · intro hu_not_even hv_not_even
    exact odd_odd_forces_base_sum_mod8_zero
      hp_odd hq_odd hsum8 hu_not_even hv_not_even

theorem modEightConstraintsGoal (F : NormalForm T P) :
    F.ModEightConstraintsGoal :=
  ⟨F.modEightConstraints_real⟩

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
