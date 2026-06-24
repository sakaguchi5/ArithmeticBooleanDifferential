import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step4ModAPI

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Source equation reduced modulo an arbitrary modulus. -/
def SourceSumModGoal (F : NormalForm T P) (m : ℕ) : Prop :=
  (F.p ^ F.u + F.q ^ F.v) % m = (2 ^ F.w) % m

/-- Realization of the arbitrary-modulus source congruence. -/
theorem source_sum_mod_goal (F : NormalForm T P) (m : ℕ) :
    F.SourceSumModGoal m := by
  change (F.p ^ F.u + F.q ^ F.v) % m = (2 ^ F.w) % m
  rw [F.source_sum_eq_two_pow]

/-- Source equation modulo a power of two, in zero-residue form. -/
def SourceSumModTwoPowZeroGoal (F : NormalForm T P) (k : ℕ) : Prop :=
  (F.p ^ F.u + F.q ^ F.v) % (2 ^ k) = 0

/-- If `k ≤ w`, then the source sum is `0 mod 2^k`. -/
theorem source_sum_mod_two_pow_zero_of_le_w
    (F : NormalForm T P) {k : ℕ}
    (hk : k ≤ F.w) :
    F.SourceSumModTwoPowZeroGoal k := by
  change (F.p ^ F.u + F.q ^ F.v) % (2 ^ k) = 0
  rw [F.source_sum_eq_two_pow]
  have hdiv : 2 ^ k ∣ 2 ^ F.w := by
    refine ⟨2 ^ (F.w - k), ?_⟩
    rw [← pow_add, Nat.add_sub_of_le hk]
  exact Nat.mod_eq_zero_of_dvd hdiv

/-- Mod-8 source equation target. -/
def SourceSumModEightGoal (F : NormalForm T P) : Prop :=
  (F.p ^ F.u + F.q ^ F.v) % 8 = 0

/-- Realization of the mod-8 source equation from `3 ≤ w`. -/
theorem source_sum_mod_eight_real
    (F : NormalForm T P) (hthree : F.ThreeLeWGoal) :
    F.SourceSumModEightGoal := by
  change (F.p ^ F.u + F.q ^ F.v) % (2 ^ 3) = 0
  exact F.source_sum_mod_two_pow_zero_of_le_w hthree

/-- Residue-sum form of the mod-8 source equation. -/
theorem residue_sum_mod_eight_of_source_sum_mod_eight
    (F : NormalForm T P)
    (h : F.SourceSumModEightGoal) :
    ((F.p ^ F.u % 8) + (F.q ^ F.v % 8)) % 8 = 0 := by
  have hopen :
      (F.p ^ F.u + F.q ^ F.v) % 8 = 0 := by
    change F.SourceSumModEightGoal
    exact h
  exact add_mod_eight_zero_of_sum_mod_eight hopen

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
