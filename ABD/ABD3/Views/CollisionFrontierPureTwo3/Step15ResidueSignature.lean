import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step14Branch5Mod5

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- A reusable period certificate for powers modulo `m`. -/
structure PowResiduePeriod (m x d : ℕ) : Prop where
  positive_period : 0 < d
  stable : ∀ n : ℕ, x ^ (n + d) % m = x ^ n % m

/-- A finite exponent-class rule for reducing `x^n mod m`.

This is intentionally lightweight: later files can instantiate it with concrete
periods such as mod-16 odd-unit period `4` or prime-modulus unit periods. -/
structure PowResidueClassRule (m x d r value : ℕ) : Prop where
  period_pos : 0 < d
  class_eq : r < d
  realizes : ∀ n : ℕ, n % d = r → x ^ n % m = value % m

/-- Generic source residue signature for the pure two-power equation at a fixed modulus `m`.

The modulus is an explicit type parameter, so a value of
`SourceResidueSignature F m` is guaranteed by its type to be a signature modulo
that same `m`. -/
structure SourceResidueSignature (F : NormalForm T P) (m : ℕ) where
  p_pow_residue : ℕ
  q_pow_residue : ℕ
  rhs_residue : ℕ
  hp_pow : F.p ^ F.u % m = p_pow_residue % m
  hq_pow : F.q ^ F.v % m = q_pow_residue % m
  hrhs : 2 ^ F.w % m = rhs_residue % m
  hsum : (p_pow_residue + q_pow_residue) % m = rhs_residue % m

/-- Trivial generic signature obtained by taking the actual residues. -/
def sourceResidueSignature_trivial
    (F : NormalForm T P) (m : ℕ) :
    SourceResidueSignature F m := by
  refine
    { p_pow_residue := F.p ^ F.u % m
      q_pow_residue := F.q ^ F.v % m
      rhs_residue := 2 ^ F.w % m
      hp_pow := by rw [Nat.mod_mod]
      hq_pow := by rw [Nat.mod_mod]
      hrhs := by rw [Nat.mod_mod]
      hsum := ?_ }
  have hsource : F.SourceSumModGoal m := F.source_sum_mod_goal m
  change (F.p ^ F.u + F.q ^ F.v) % m = (2 ^ F.w) % m at hsource
  calc
    ((F.p ^ F.u % m) + (F.q ^ F.v % m)) % m
        = (F.p ^ F.u + F.q ^ F.v) % m := by
            rw [← Nat.add_mod]
    _ = (2 ^ F.w) % m := hsource
    _ = ((2 ^ F.w) % m) % m := by rw [Nat.mod_mod]

/-- Recover the source congruence from a generic residue signature. -/
theorem source_mod_of_sourceResidueSignature
    (F : NormalForm T P) {m : ℕ} (S : SourceResidueSignature F m) :
    F.SourceSumModGoal m := by
  change (F.p ^ F.u + F.q ^ F.v) % m = (2 ^ F.w) % m
  calc
    (F.p ^ F.u + F.q ^ F.v) % m
        = ((F.p ^ F.u % m) + (F.q ^ F.v % m)) % m := by
            rw [Nat.add_mod]
    _ = (S.p_pow_residue % m + S.q_pow_residue % m) % m := by
            rw [S.hp_pow, S.hq_pow]
    _ = (S.p_pow_residue + S.q_pow_residue) % m := by
            rw [← Nat.add_mod]
    _ = S.rhs_residue % m := S.hsum
    _ = (2 ^ F.w) % m := by rw [← S.hrhs]

/-- Branch 5 version of the generic residue signature at a fixed modulus. -/
structure Branch5ResidueSignature (F : NormalForm T P) (m : ℕ) where
  branch5 : Branch5Data F
  signature : SourceResidueSignature F m

/-- Build a Branch 5 residue signature for any modulus. -/
def branch5ResidueSignature_trivial
    (F : NormalForm T P) (B : Branch5Data F) (m : ℕ) :
    Branch5ResidueSignature F m :=
  { branch5 := B
    signature := F.sourceResidueSignature_trivial m }

/-- A Branch 5 residue signature exists for every modulus. -/
theorem exists_branch5ResidueSignature
    (F : NormalForm T P) (B : Branch5Data F) (m : ℕ) :
    ∃ S : Branch5ResidueSignature F m, S.branch5 = B :=
  ⟨F.branch5ResidueSignature_trivial B m, rfl⟩

/-- A named package collecting the first concrete residue refinements and the
general arbitrary-modulus hook. -/
structure Branch5ResidueToolkit (F : NormalForm T P) where
  branch5 : Branch5Data F
  mod3 : Branch5Mod3Signature F
  mod5 : Branch5Mod5Signature F
  arbitrary : ∀ m : ℕ, Branch5ResidueSignature F m

/-- Realization of the residue toolkit from Branch 5 core data. -/
def branch5ResidueToolkit
    (F : NormalForm T P) (B : Branch5Data F) :
    Branch5ResidueToolkit F :=
  { branch5 := B
    mod3 := F.branch5Mod3Signature_trivial B
    mod5 := F.branch5Mod5Signature_trivial B
    arbitrary := fun m => F.branch5ResidueSignature_trivial B m }

/-- A Branch 5 residue toolkit exists once Branch 5 core data is supplied. -/
theorem exists_branch5ResidueToolkit
    (F : NormalForm T P) (B : Branch5Data F) :
    ∃ K : Branch5ResidueToolkit F, K.branch5 = B :=
  ⟨F.branch5ResidueToolkit B, rfl⟩

/-- Extract the arbitrary-modulus source congruence from the Branch 5 toolkit. -/
theorem source_mod_of_branch5ResidueToolkit
    (F : NormalForm T P) (K : Branch5ResidueToolkit F) (m : ℕ) :
    F.SourceSumModGoal m := by
  exact F.source_mod_of_sourceResidueSignature (K.arbitrary m).signature

/-- Extract the mod-3 source congruence from the Branch 5 toolkit. -/
theorem source_mod3_of_branch5ResidueToolkit
    (F : NormalForm T P) (K : Branch5ResidueToolkit F) :
    F.SourceSumModThreeGoal :=
  F.source_mod3_of_branch5Mod3Signature K.mod3

/-- Extract the mod-5 source congruence from the Branch 5 toolkit. -/
theorem source_mod5_of_branch5ResidueToolkit
    (F : NormalForm T P) (K : Branch5ResidueToolkit F) :
    F.SourceSumModFiveGoal :=
  F.source_mod5_of_branch5Mod5Signature K.mod5

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
