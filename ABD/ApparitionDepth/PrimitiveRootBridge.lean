/-
  ABD.ApparitionDepth.PrimitiveRootBridge

  Step 15 of the Apparition-Depth Decomposition project.

  This file introduces a light bridge wrapper for primitive roots modulo `p`.

  Design choice:
    * we do not yet depend on a deep primitive-root existence theorem;
    * we express "`g` is a primitive root modulo `p`" as saying that the
      multiplicative order of the unit represented by `g` is `p - 1`;
    * later files can connect this wrapper to mathlib's cyclic/primitive-root
      API or prove existence for prime `p`.

  This is enough for the next file to prove that the branch seed

      g ^ (((p - 1) / d) * j)

  is a `d`-th root modulo `p` whenever `d | p - 1`.
-/

import ABD.ApparitionDepth.BranchSeedBasic

namespace ApparitionDepth

/-- `g` is a primitive root modulo `p`, expressed through the existing
`orderMod` bridge.

The existential stores the coprimality proof needed to regard `g` as a unit of
`ZMod p`.  The order condition is the usual primitive-root condition:

`order(g mod p) = p - 1`.

Prime assumptions on `p` are intentionally not part of this wrapper; theorem
layers can add them where needed. -/
def PrimitiveRootModP (g p : Nat) : Prop :=
  ∃ hcop : g.Coprime p, OrderModIs g p (p - 1) hcop

/-- Constructor for `PrimitiveRootModP`. -/
theorem primitiveRootModP_intro {g p : Nat} (hcop : g.Coprime p)
    (hord : OrderModIs g p (p - 1) hcop) :
    PrimitiveRootModP g p :=
  ⟨hcop, hord⟩

/-- A primitive-root wrapper gives the stored coprimality proof. -/
theorem primitiveRootModP_coprime {g p : Nat}
    (hprim : PrimitiveRootModP g p) :
    ∃ hcop : g.Coprime p, OrderModIs g p (p - 1) hcop :=
  hprim

/-- If `g` is a primitive root modulo `p`, then any exponent divisible by
`p - 1` gives power one in the unit group. -/
theorem unitPowOneAt_of_primitiveRootModP_dvd {g p n : Nat}
    (hprim : PrimitiveRootModP g p)
    (hdiv : p - 1 ∣ n) :
    ∃ hcop : g.Coprime p, UnitPowOneAt g p n hcop := by
  rcases hprim with ⟨hcop, hord⟩
  exact ⟨hcop, unitPowOneAt_of_orderModIs_dvd hord hdiv⟩

/-- The same consequence, projected from the unit group down to `ZMod p`. -/
theorem residuePowOne_of_primitiveRootModP_dvd {g p n : Nat}
    (hprim : PrimitiveRootModP g p)
    (hdiv : p - 1 ∣ n) :
    ((g : ZMod p) ^ n = 1) := by
  rcases unitPowOneAt_of_primitiveRootModP_dvd hprim hdiv with ⟨hcop, hunit⟩
  exact (unitPowOneAt_iff_residuePowOne hcop).mp hunit

/-- The seed exponent multiplied by `d` is `(p - 1) * j`, provided `d | p - 1`.

This is the elementary arithmetic identity behind the branch-root proof. -/
theorem branchSeedExponent_mul_d_eq {p d j : Nat}
    (hdvd : d ∣ p - 1) :
    branchSeedExponent p d j * d = (p - 1) * j := by
  unfold branchSeedExponent
  calc
    (((p - 1) / d) * j) * d = (((p - 1) / d) * d) * j := by
      ac_rfl
    _ = (p - 1) * j := by
      rw [Nat.div_mul_cancel hdvd]

/-- Therefore `p - 1` divides the full exponent used in the `d`-th power of the
branch seed. -/
theorem p_sub_one_dvd_branchSeedExponent_mul_d_of_branchParams {p d j : Nat}
    (hparams : BranchParams p d j) :
    p - 1 ∣ branchSeedExponent p d j * d := by
  refine ⟨j, ?_⟩
  exact branchSeedExponent_mul_d_eq (branchParams_dvd hparams)

end ApparitionDepth
