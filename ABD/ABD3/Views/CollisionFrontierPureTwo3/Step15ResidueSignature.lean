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

/-- Generic source residue signature for the pure two-power equation.

It records residues of the three power terms modulo an arbitrary modulus and the
sum constraint inherited from `p^u + q^v = 2^w`. -/
structure SourceResidueSignature (F : NormalForm T P) where
  modulus : ℕ
  p_pow_residue : ℕ
  q_pow_residue : ℕ
  rhs_residue : ℕ
  hp_pow : F.p ^ F.u % modulus = p_pow_residue % modulus
  hq_pow : F.q ^ F.v % modulus = q_pow_residue % modulus
  hrhs : 2 ^ F.w % modulus = rhs_residue % modulus
  hsum : (p_pow_residue + q_pow_residue) % modulus = rhs_residue % modulus

/-- Trivial generic signature obtained by taking the actual residues. -/
def sourceResidueSignature_trivial
    (F : NormalForm T P) (m : ℕ) :
    SourceResidueSignature F := by
  refine
    { modulus := m
      p_pow_residue := F.p ^ F.u % m
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

/-- Branch 5 version of the generic residue signature. -/
structure Branch5ResidueSignature (F : NormalForm T P) where
  branch5 : Branch5Data F
  signature : SourceResidueSignature F

/-- Build a Branch 5 residue signature for any modulus. -/
def branch5ResidueSignature_trivial
    (F : NormalForm T P) (B : Branch5Data F) (m : ℕ) :
    Branch5ResidueSignature F :=
  { branch5 := B
    signature := F.sourceResidueSignature_trivial m }

/-- A named package collecting the first concrete residue refinements and the
general arbitrary-modulus hook. -/
structure Branch5ResidueToolkit (F : NormalForm T P) where
  branch5 : Branch5Data F
  mod3 : Branch5Mod3Signature F
  mod5 : Branch5Mod5Signature F
  arbitrary : ∀ _m : ℕ, Branch5ResidueSignature F

/-- Realization of the residue toolkit from Branch 5 core data. -/
def branch5ResidueToolkit
    (F : NormalForm T P) (B : Branch5Data F) :
    Branch5ResidueToolkit F :=
  { branch5 := B
    mod3 := F.branch5Mod3Signature_trivial B
    mod5 := F.branch5Mod5Signature_trivial B
    arbitrary := fun m => F.branch5ResidueSignature_trivial B m }

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
