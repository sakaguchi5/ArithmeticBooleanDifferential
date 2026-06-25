import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step11Branch5Data

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Odd exponent classes modulo `4` used for the mod-16 refinement. -/
inductive OddModFourClass where
  | one
  | three
  deriving DecidableEq, Repr

namespace OddModFourClass

/-- Interpretation of an odd modulo-four class. -/
def Holds (c : OddModFourClass) (n : ℕ) : Prop :=
  match c with
  | one => n % 4 = 1
  | three => n % 4 = 3

end OddModFourClass

/-- Branch 5 plus chosen modulo-four classes for the two odd exponents. -/
structure Branch5ModFourSignature (F : NormalForm T P) where
  branch5 : Branch5Data F
  u_class : OddModFourClass
  v_class : OddModFourClass
  hu_class : u_class.Holds F.u
  hv_class : v_class.Holds F.v

/-- Conditional Branch 5 mod-16 data.

The source equation becomes zero modulo `16` once `4 ≤ w`.  This file does not
force a particular `(u mod 4, v mod 4)` signature; that refinement is represented
by `Branch5ModFourSignature`. -/
structure Branch5Mod16Data (F : NormalForm T P) where
  branch5 : Branch5Data F
  four_le_w : 4 ≤ F.w
  source_mod16 : F.SourceSumModSixteenGoal

/-- Build the conditional mod-16 package from `4 ≤ w`. -/
theorem branch5Mod16Data_of_four_le_w
    (F : NormalForm T P) (B : Branch5Data F) (h4 : 4 ≤ F.w) :
    Branch5Mod16Data F :=
  { branch5 := B
    four_le_w := h4
    source_mod16 := F.source_sum_mod_sixteen_of_four_le_w h4 }

/-- Raw mod-16 power-signature target.

For later refinements, `p_pow` and `q_pow` can be replaced by the class-specific
values obtained from `u mod 4` and `v mod 4`. -/
structure Branch5Mod16PowerSignature (F : NormalForm T P) where
  branch5 : Branch5Data F
  four_le_w : 4 ≤ F.w
  p_pow_residue : ℕ
  q_pow_residue : ℕ
  hp_pow : F.p ^ F.u % 16 = p_pow_residue % 16
  hq_pow : F.q ^ F.v % 16 = q_pow_residue % 16
  hsum_zero : (p_pow_residue + q_pow_residue) % 16 = 0

/-- The trivial raw power-signature obtained directly from the mod-16 source equation. -/
def branch5Mod16PowerSignature_trivial
    (F : NormalForm T P) (B : Branch5Data F) (h4 : 4 ≤ F.w) :
    Branch5Mod16PowerSignature F := by
  refine
    { branch5 := B
      four_le_w := h4
      p_pow_residue := F.p ^ F.u % 16
      q_pow_residue := F.q ^ F.v % 16
      hp_pow := by rw [Nat.mod_mod]
      hq_pow := by rw [Nat.mod_mod]
      hsum_zero := ?_ }
  have h16 : F.SourceSumModSixteenGoal :=
    F.source_sum_mod_sixteen_of_four_le_w h4
  have hsum :
      ((F.p ^ F.u % 16) + (F.q ^ F.v % 16)) % 16 = 0 := by
    have hrewrite :
        (F.p ^ F.u + F.q ^ F.v) % 16 =
          ((F.p ^ F.u % 16) + (F.q ^ F.v % 16)) % 16 := by
      rw [Nat.add_mod]
    rw [← hrewrite]
    exact h16
  simpa using hsum

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
