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

/-- Recover the source congruence modulo `3` from a Branch 5 mod-3 signature. -/
theorem source_mod3_of_branch5Mod3Signature
    (F : NormalForm T P) (S : Branch5Mod3Signature F) :
    F.SourceSumModThreeGoal := by
  change (F.p ^ F.u + F.q ^ F.v) % 3 = (2 ^ F.w) % 3
  calc
    (F.p ^ F.u + F.q ^ F.v) % 3
        = ((F.p ^ F.u % 3) + (F.q ^ F.v % 3)) % 3 := by
            rw [Nat.add_mod]
    _ = (S.p_pow_residue % 3 + S.q_pow_residue % 3) % 3 := by
            rw [S.hp_pow, S.hq_pow]
    _ = (S.p_pow_residue + S.q_pow_residue) % 3 := by
            rw [← Nat.add_mod]
    _ = S.rhs_residue % 3 := S.hsum
    _ = (2 ^ F.w) % 3 := by rw [← S.hrhs]

/-- A Branch 5 mod-3 signature always exists. -/
theorem exists_branch5Mod3Signature
    (F : NormalForm T P) (B : Branch5Data F) :
    ∃ S : Branch5Mod3Signature F, S.branch5 = B :=
  ⟨F.branch5Mod3Signature_trivial B, rfl⟩

--lemma
theorem square_mod3_eq_one_of_ne_zero
    {x : ℕ} (hx : x % 3 ≠ 0) :
    x ^ 2 % 3 = 1 := by
  have h : x % 3 = 1 ∨ x % 3 = 2 := by
    have := Nat.mod_lt x (by decide : 0 < 3)
    interval_cases x % 3 <;> omega
  cases h with
  | inl h1 =>
      have : x % 3 = 1 % 3 := by simp [h1]
      simpa using pow_mod_eq_of_mod_eq this (k := 2)
  | inr h2 =>
      have : x % 3 = 2 % 3 := by simp [h2]
      have hcalc : (2 : ℕ)^2 % 3 = 1 := by decide
      simpa using pow_mod_eq_of_mod_eq this (k := 2)

--lemma
theorem mul_pow_square_mod3_eq_self
    {x k : ℕ}
    (hx : x % 3 ≠ 0) :
    (x * (x ^ 2) ^ k) % 3 = x % 3 := by
  have hx2 : x ^ 2 % 3 = 1 := by
    exact square_mod3_eq_one_of_ne_zero hx
  have hx2pow : (x ^ 2) ^ k % 3 = 1 := by
    have hx2' : x ^ 2 % 3 = 1 % 3 := by
      exact hx2
    have h :=
      pow_mod_eq_of_mod_eq hx2' (k := k)
    simpa using h
  calc
    (x * (x ^ 2) ^ k) % 3
        = ((x % 3) * (((x ^ 2) ^ k) % 3)) % 3 := by
            rw [Nat.mul_mod]
    _ = ((x % 3) * 1) % 3 := by rw [hx2pow]
    _ = x % 3 := by simp

/-- Odd powers reduce to the base modulo `3`. -/
theorem pow_odd_mod3_eq_self
    {x n : ℕ} (hn : Odd n) :
    x ^ n % 3 = x % 3 := by
  rcases hn with ⟨k, hk⟩
  have hpow : x ^ (2 * k + 1) = x * (x ^ 2) ^ k := by
    rw [show 2 * k + 1 = 1 + 2 * k by omega]
    rw [pow_add, pow_one]
    rw [pow_mul]
  rw [hk, hpow]
  by_cases hx0 : x % 3 = 0
  · calc
      (x * (x ^ 2) ^ k) % 3
          = ((x % 3) * (((x ^ 2) ^ k) % 3)) % 3 := by
              rw [Nat.mul_mod]
      _ = 0 := by simp [hx0]
      _ = x % 3 := hx0.symm
  · exact mul_pow_square_mod3_eq_self hx0

/-- In Branch 5, the mod-3 source equation reduces to a base-residue sum. -/
theorem branch5_mod3_base_sum
    (F : NormalForm T P) (B : Branch5Data F) :
    (F.p + F.q) % 3 = (2 ^ F.w) % 3 := by
  have hsource : F.SourceSumModThreeGoal := F.source_sum_mod_three
  change (F.p ^ F.u + F.q ^ F.v) % 3 = (2 ^ F.w) % 3 at hsource
  have hp : F.p ^ F.u % 3 = F.p % 3 := pow_odd_mod3_eq_self B.u_odd
  have hq : F.q ^ F.v % 3 = F.q % 3 := pow_odd_mod3_eq_self B.v_odd
  calc
    (F.p + F.q) % 3
        = ((F.p % 3) + (F.q % 3)) % 3 := by rw [Nat.add_mod]
    _ = ((F.p ^ F.u % 3) + (F.q ^ F.v % 3)) % 3 := by rw [← hp, ← hq]
    _ = (F.p ^ F.u + F.q ^ F.v) % 3 := by rw [← Nat.add_mod]
    _ = (2 ^ F.w) % 3 := hsource

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
