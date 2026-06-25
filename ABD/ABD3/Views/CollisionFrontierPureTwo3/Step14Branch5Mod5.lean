import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step13Branch5Mod3

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Branch 5 source equation modulo `5`. -/
structure Branch5Mod5Data (F : NormalForm T P) where
  branch5 : Branch5Data F
  source_mod5 : F.SourceSumModFiveGoal

/-- Build the mod-5 package. -/
theorem branch5Mod5Data
    (F : NormalForm T P) (B : Branch5Data F) :
    Branch5Mod5Data F :=
  { branch5 := B
    source_mod5 := F.source_sum_mod_five }

/-- At least one base is congruent to zero modulo `5` because it is the prime `5`.

This is kept separate from the unit case since power periods modulo `5` only apply
to bases coprime to `5`. -/
def Branch5Mod5ZeroBaseCase (F : NormalForm T P) : Prop :=
  F.p = 5 ∨ F.q = 5

/-- Both bases are units modulo `5`. -/
def Branch5Mod5UnitBaseCase (F : NormalForm T P) : Prop :=
  F.p ≠ 5 ∧ F.q ≠ 5

/-- A raw mod-5 residue signature for Branch 5.

In the unit case this can later be refined using exponent classes modulo `4`. -/
structure Branch5Mod5Signature (F : NormalForm T P) where
  branch5 : Branch5Data F
  p_pow_residue : ℕ
  q_pow_residue : ℕ
  rhs_residue : ℕ
  hp_pow : F.p ^ F.u % 5 = p_pow_residue % 5
  hq_pow : F.q ^ F.v % 5 = q_pow_residue % 5
  hrhs : 2 ^ F.w % 5 = rhs_residue % 5
  hsum : (p_pow_residue + q_pow_residue) % 5 = rhs_residue % 5

/-- The trivial Branch 5 mod-5 signature obtained from the source equation. -/
def branch5Mod5Signature_trivial
    (F : NormalForm T P) (B : Branch5Data F) :
    Branch5Mod5Signature F := by
  refine
    { branch5 := B
      p_pow_residue := F.p ^ F.u % 5
      q_pow_residue := F.q ^ F.v % 5
      rhs_residue := 2 ^ F.w % 5
      hp_pow := by rw [Nat.mod_mod]
      hq_pow := by rw [Nat.mod_mod]
      hrhs := by rw [Nat.mod_mod]
      hsum := ?_ }
  have hsource : F.SourceSumModFiveGoal := F.source_sum_mod_five
  change (F.p ^ F.u + F.q ^ F.v) % 5 = (2 ^ F.w) % 5 at hsource
  calc
    ((F.p ^ F.u % 5) + (F.q ^ F.v % 5)) % 5
        = (F.p ^ F.u + F.q ^ F.v) % 5 := by
            rw [← Nat.add_mod]
    _ = (2 ^ F.w) % 5 := hsource
    _ = ((2 ^ F.w) % 5) % 5 := by rw [Nat.mod_mod]

/-- Recover the source congruence modulo `5` from a Branch 5 mod-5 signature. -/
theorem source_mod5_of_branch5Mod5Signature
    (F : NormalForm T P) (S : Branch5Mod5Signature F) :
    F.SourceSumModFiveGoal := by
  change (F.p ^ F.u + F.q ^ F.v) % 5 = (2 ^ F.w) % 5
  calc
    (F.p ^ F.u + F.q ^ F.v) % 5
        = ((F.p ^ F.u % 5) + (F.q ^ F.v % 5)) % 5 := by
            rw [Nat.add_mod]
    _ = (S.p_pow_residue % 5 + S.q_pow_residue % 5) % 5 := by
            rw [S.hp_pow, S.hq_pow]
    _ = (S.p_pow_residue + S.q_pow_residue) % 5 := by
            rw [← Nat.add_mod]
    _ = S.rhs_residue % 5 := S.hsum
    _ = (2 ^ F.w) % 5 := by rw [← S.hrhs]

/-- A Branch 5 mod-5 signature always exists. -/
theorem exists_branch5Mod5Signature
    (F : NormalForm T P) (B : Branch5Data F) :
    ∃ S : Branch5Mod5Signature F, S.branch5 = B :=
  ⟨F.branch5Mod5Signature_trivial B, rfl⟩

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
