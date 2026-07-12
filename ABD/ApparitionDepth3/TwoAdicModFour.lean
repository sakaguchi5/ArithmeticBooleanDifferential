/-
  ABD.ApparitionDepth3.TwoAdicModFour

  Stage 17:
    the p=2 boundary.  Modulo 2 the roots +1 and -1 coincide, so the initial
    branch boundary is moved to modulo 4.  The two p-adic roots are constructed
    directly; no false simple-root-mod-2 hypothesis is introduced.
-/

import ABD.ApparitionDepth3.OddPrimeComplete

namespace ApparitionDepth3

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The two 2-adic Teichmuller torsion branches. -/
inductive TwoAdicBranch where
  | positive
  | negative
  deriving DecidableEq

/-- The mod-4 seed which distinguishes the two branches. -/
def twoAdicSeedModFour : TwoAdicBranch → ZMod 4
  | .positive => 1
  | .negative => 3

/-- Their natural torsion orders in the 2-adic unit group. -/
def twoAdicTorsionOrder : TwoAdicBranch → Nat
  | .positive => 1
  | .negative => 2

/-- The actual 2-adic roots. -/
noncomputable def twoAdicPadicRoot : TwoAdicBranch → ℤ_[2]
  | .positive => 1
  | .negative => -1

/-- Finite reduction modulo 2^r. -/
noncomputable def twoAdicReduction
    (b : TwoAdicBranch) (r : Nat) : ZMod (2 ^ r) :=
  PadicInt.toZModPow r (twoAdicPadicRoot b)

/-- Standard natural representative of the finite reduction. -/
noncomputable def twoAdicRepresentative
    (b : TwoAdicBranch) (r : Nat) : Nat :=
  (twoAdicReduction b r).val

/-- Both branches are roots of X^2-1 in the 2-adic integers. -/
theorem twoAdicPadicRoot_sq (b : TwoAdicBranch) :
    twoAdicPadicRoot b ^ 2 = 1 := by
  cases b <;> simp [twoAdicPadicRoot]

/-- Every finite coordinate is a square root of one. -/
theorem twoAdicReduction_sq
    (b : TwoAdicBranch) (r : Nat) :
    twoAdicReduction b r ^ 2 = 1 := by
  unfold twoAdicReduction
  rw [← map_pow, twoAdicPadicRoot_sq, map_one]

/-- The finite coordinates are compatible. -/
theorem twoAdicReduction_compat
    (b : TwoAdicBranch) {m n : Nat} (hmn : m ≤ n) :
    ZMod.cast (twoAdicReduction b n) = twoAdicReduction b m := by
  unfold twoAdicReduction
  exact PadicInt.cast_toZModPow m n hmn (twoAdicPadicRoot b)

/-- Casting the standard representative recovers the reduction. -/
theorem twoAdicRepresentative_cast
    (b : TwoAdicBranch) (r : Nat) :
    (twoAdicRepresentative b r : ZMod (2 ^ r)) =
      twoAdicReduction b r := by
  unfold twoAdicRepresentative
  exact ZMod.natCast_zmod_val _

@[simp]
theorem twoAdicReduction_positive
    (r : Nat) : twoAdicReduction .positive r = 1 := by
  simp [twoAdicReduction, twoAdicPadicRoot]

@[simp]
theorem twoAdicReduction_negative
    (r : Nat) : twoAdicReduction .negative r = -1 := by
  simp [twoAdicReduction, twoAdicPadicRoot]

/-- At precision 4, the positive branch is 1. -/
theorem twoAdicReduction_positive_modFour :
    (twoAdicReduction .positive 2 : ZMod 4) =
      twoAdicSeedModFour .positive := by
  simp [twoAdicSeedModFour]

/-- At precision 4, the negative branch is 3=-1. -/
theorem twoAdicReduction_negative_modFour :
    (twoAdicReduction .negative 2 : ZMod 4) =
      twoAdicSeedModFour .negative := by
  simp only [Nat.reducePow, twoAdicReduction_negative]
  decide

/-- The mod-4 seed theorem for both branches. -/
theorem twoAdicReduction_modFour
    (b : TwoAdicBranch) :
    (twoAdicReduction b 2 : ZMod 4) = twoAdicSeedModFour b := by
  cases b
  · exact twoAdicReduction_positive_modFour
  · exact twoAdicReduction_negative_modFour

/-- Every precision r>=2 reduces to the correct mod-4 seed. -/
theorem twoAdicReduction_cast_modFour
    (b : TwoAdicBranch) {r : Nat} (hr : 2 ≤ r) :
    (ZMod.cast (twoAdicReduction b r) : ZMod (2 ^ 2)) =
      (twoAdicSeedModFour b : ZMod (2 ^ 2)) := by
  have hcompat := twoAdicReduction_compat b hr
  have hseed := twoAdicReduction_modFour b
  simpa using hcompat.trans hseed

/-- The two branches are already distinct modulo 4. -/
theorem twoAdicSeeds_distinct :
    twoAdicSeedModFour .positive ≠ twoAdicSeedModFour .negative := by
  decide

/-- Exact mod-4 order statement for the positive branch. -/
theorem twoAdicPositive_modFour_order_one :
    twoAdicSeedModFour .positive = 1 := rfl

/-- Exact mod-4 order statement for the negative branch. -/
theorem twoAdicNegative_modFour_order_two :
    twoAdicSeedModFour .negative ^ 2 = 1 ∧
      twoAdicSeedModFour .negative ≠ 1 := by
  decide

/-- There are no other square roots of one in the 2-adic integers. -/
theorem twoAdicPadicRoot_complete
    (theta : ℤ_[2])
    (hroot : theta ^ 2 = 1) :
    theta = twoAdicPadicRoot .positive ∨
      theta = twoAdicPadicRoot .negative := by
  rcases (sq_eq_one_iff).mp hroot with h | h
  · left
    simpa [twoAdicPadicRoot] using h
  · right
    simpa [twoAdicPadicRoot] using h

/-- Public data for one of the two 2-adic branches. -/
structure TwoAdicBranchSynthesisResult
    (b : TwoAdicBranch) where
  root : ℤ_[2]
  root_eq : root = twoAdicPadicRoot b
  squareRoot : root ^ 2 = 1
  compatible : ∀ {m n : Nat}, m ≤ n →
    ZMod.cast (PadicInt.toZModPow n root) = PadicInt.toZModPow m root
  representative : ∀ r : Nat,
    (twoAdicRepresentative b r : ZMod (2 ^ r)) = PadicInt.toZModPow r root
  modFourSeed :
    (PadicInt.toZModPow 2 root : ZMod 4) = twoAdicSeedModFour b

/-- Construction of either 2-adic branch. -/
noncomputable def twoAdicBranchSynthesisResult
    (b : TwoAdicBranch) :
    TwoAdicBranchSynthesisResult b := by
  refine
    { root := twoAdicPadicRoot b
      root_eq := rfl
      squareRoot := twoAdicPadicRoot_sq b
      compatible := ?_
      representative := ?_
      modFourSeed := ?_ }
  · intro m n hmn
    exact PadicInt.cast_toZModPow m n hmn (twoAdicPadicRoot b)
  · intro r
    exact twoAdicRepresentative_cast b r
  · exact twoAdicReduction_modFour b

/-- Complete p=2 classification package. -/
structure TwoAdicCompleteSynthesis where
  positive : TwoAdicBranchSynthesisResult .positive
  negative : TwoAdicBranchSynthesisResult .negative
  distinguishedModFour :
    twoAdicSeedModFour .positive ≠ twoAdicSeedModFour .negative
  complete : ∀ theta : ℤ_[2], theta ^ 2 = 1 →
    theta = twoAdicPadicRoot .positive ∨
      theta = twoAdicPadicRoot .negative

/-- Complete p=2 synthesis using mod 4 as the initial branch boundary. -/
noncomputable def twoAdicCompleteSynthesis : TwoAdicCompleteSynthesis :=
  { positive := twoAdicBranchSynthesisResult .positive
    negative := twoAdicBranchSynthesisResult .negative
    distinguishedModFour := twoAdicSeeds_distinct
    complete := twoAdicPadicRoot_complete }

end ApparitionDepth3
