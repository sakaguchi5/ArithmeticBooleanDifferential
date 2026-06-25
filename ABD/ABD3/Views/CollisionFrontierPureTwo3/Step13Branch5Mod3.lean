import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step12Branch5Mod16

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Branch 5 source equation modulo `3`. -/
structure Branch5Mod3Data (F : NormalForm T P) where
  branch5 : Branch5Data F
  source_mod3 : F.SourceSumModThreeGoal

/-- Build the mod-3 package. -/
theorem branch5Mod3Data
    (F : NormalForm T P) (B : Branch5Data F) :
    Branch5Mod3Data F :=
  { branch5 := B
    source_mod3 := F.source_sum_mod_three }

/-- The unit case for mod `3`: neither base is the prime `3`.

This is separated because if one of `p,q` is `3`, the corresponding power is
zero modulo `3`; otherwise odd exponents can later be reduced to base residues. -/
def Branch5Mod3UnitBaseCase (F : NormalForm T P) : Prop :=
  F.p ≠ 3 ∧ F.q ≠ 3

/-- A raw mod-3 residue signature for Branch 5. -/
structure Branch5Mod3Signature (F : NormalForm T P) where
  branch5 : Branch5Data F
  p_pow_residue : ℕ
  q_pow_residue : ℕ
  rhs_residue : ℕ
  hp_pow : F.p ^ F.u % 3 = p_pow_residue % 3
  hq_pow : F.q ^ F.v % 3 = q_pow_residue % 3
  hrhs : 2 ^ F.w % 3 = rhs_residue % 3
  hsum : (p_pow_residue + q_pow_residue) % 3 = rhs_residue % 3

/-- The trivial Branch 5 mod-3 signature obtained from the source equation. -/
def branch5Mod3Signature_trivial
    (F : NormalForm T P) (B : Branch5Data F) :
    Branch5Mod3Signature F := by
  refine
    { branch5 := B
      p_pow_residue := F.p ^ F.u % 3
      q_pow_residue := F.q ^ F.v % 3
      rhs_residue := 2 ^ F.w % 3
      hp_pow := by rw [Nat.mod_mod]
      hq_pow := by rw [Nat.mod_mod]
      hrhs := by rw [Nat.mod_mod]
      hsum := ?_ }
  have hsource : F.SourceSumModThreeGoal := F.source_sum_mod_three
  change (F.p ^ F.u + F.q ^ F.v) % 3 = (2 ^ F.w) % 3 at hsource
  calc
    ((F.p ^ F.u % 3) + (F.q ^ F.v % 3)) % 3
        = (F.p ^ F.u + F.q ^ F.v) % 3 := by rw [← Nat.add_mod]
    _ = (2 ^ F.w) % 3 := hsource
    _ = ((2 ^ F.w) % 3) % 3 := by rw [Nat.mod_mod]

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
