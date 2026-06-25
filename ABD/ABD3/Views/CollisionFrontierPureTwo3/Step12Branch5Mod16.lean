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

/-- Recover the mod-16 source-zero statement from a raw Branch 5 power signature. -/
theorem source_mod16_zero_of_branch5Mod16PowerSignature
    (F : NormalForm T P) (S : Branch5Mod16PowerSignature F) :
    F.SourceSumModSixteenGoal := by
  change (F.p ^ F.u + F.q ^ F.v) % 16 = 0
  calc
    (F.p ^ F.u + F.q ^ F.v) % 16
        = ((F.p ^ F.u % 16) + (F.q ^ F.v % 16)) % 16 := by
            rw [Nat.add_mod]
    _ = (S.p_pow_residue % 16 + S.q_pow_residue % 16) % 16 := by
            rw [S.hp_pow, S.hq_pow]
    _ = (S.p_pow_residue + S.q_pow_residue) % 16 := by
            rw [← Nat.add_mod]
    _ = 0 := S.hsum_zero

/-- An odd natural number has residue `1` or `3` modulo `4`. -/
theorem exists_oddModFourClass_of_odd
    {n : ℕ} (hn : Odd n) :
    ∃ c : OddModFourClass, c.Holds n := by
  have hlt : n % 4 < 4 := Nat.mod_lt n (by decide : 0 < 4)
  have hne : ¬ Even n := not_even_of_odd hn
  have hdecomp : n = 4 * (n / 4) + n % 4 := by
    have hmad := Nat.mod_add_div n 4
    omega
  rcases hmod : n % 4 with _ | r
  · exfalso
    apply hne
    refine ⟨2 * (n / 4), ?_⟩
    omega
  · rcases r with _ | r
    · exact ⟨OddModFourClass.one, by simpa [OddModFourClass.Holds] using hmod⟩
    · rcases r with _ | r
      · exfalso
        apply hne
        refine ⟨2 * (n / 4) + 1, ?_⟩
        omega
      · rcases r with _ | r
        · exact ⟨OddModFourClass.three, by simpa [OddModFourClass.Holds] using hmod⟩
        · have hbad : Nat.succ (Nat.succ (Nat.succ (Nat.succ r))) < 4 := by
            simpa [hmod] using hlt
          omega

/-- Branch 5 admits a modulo-four signature for its two odd exponents. -/
theorem exists_branch5ModFourSignature
    (F : NormalForm T P) (B : Branch5Data F) :
    ∃ S : Branch5ModFourSignature F, S.branch5 = B := by
  rcases exists_oddModFourClass_of_odd B.u_odd with ⟨cu, hcu⟩
  rcases exists_oddModFourClass_of_odd B.v_odd with ⟨cv, hcv⟩
  exact
    ⟨{ branch5 := B
       u_class := cu
       v_class := cv
       hu_class := hcu
       hv_class := hcv }, rfl⟩

/-- Odd fourth powers are `1` modulo `16`. -/
theorem odd_pow_four_mod_sixteen {x : ℕ} (hx : Odd x) :
    x ^ 4 % 16 = 1 := by
  rcases hx with ⟨k, rfl⟩
  have hEven : Even (k * (k + 1)) := Nat.even_mul_succ_self k
  rcases hEven with ⟨m, hm⟩
  have hsq : (2 * k + 1) ^ 2 = 8 * m + 1 := by
    nlinarith
  have hfour_rewrite : (2 * k + 1) ^ 4 = ((2 * k + 1) ^ 2) ^ 2 := by
    ring
  have hcalc : (8 * m + 1) ^ 2 = 16 * (4 * m * m + m) + 1 := by
    nlinarith
  calc
    (2 * k + 1) ^ 4 % 16
        = (((2 * k + 1) ^ 2) ^ 2) % 16 := by rw [hfour_rewrite]
    _ = (8 * m + 1) ^ 2 % 16 := by rw [hsq]
    _ = (16 * (4 * m * m + m) + 1) % 16 := by rw [hcalc]
    _ = 1 := by simp

--lemma
theorem pow_mod16_eq_one_of_mod16_eq_one
    {a k : ℕ}
    (h : a % 16 = 1) :
    a ^ k % 16 = 1 := by
  have h' : a % 16 = 1 % 16 := by
    simpa using h
  have hp :=
    pow_mod_eq_of_mod_eq
      (a := a)
      (b := 1)
      (M := 16)
      (k := k)
      h'
  calc
    a ^ k % 16 = 1 ^ k % 16 := hp
    _ = 1 := by simp

/-- If an odd base has exponent class `1 mod 4`, reduce the power modulo `16`. -/
theorem odd_pow_mod16_of_exp_mod4_one
    {x n : ℕ} (hx : Odd x) (hn : n % 4 = 1) :
    x ^ n % 16 = x % 16 := by
  have hdecomp : n = 4 * (n / 4) + 1 := by
    have hmad := Nat.mod_add_div n 4
    omega
  have hfour : x ^ 4 % 16 = 1 := odd_pow_four_mod_sixteen hx
  have hfourpow :
    (x ^ 4) ^ (n / 4) % 16 = 1 := by
    exact pow_mod16_eq_one_of_mod16_eq_one hfour
  rw [hdecomp]
  rw [show 4 * (n / 4) + 1 = 1 + 4 * (n / 4) by omega]
  rw [pow_add, pow_one, pow_mul]
  calc
    (x * (x ^ 4) ^ (n / 4)) % 16
        = ((x % 16) * (((x ^ 4) ^ (n / 4)) % 16)) % 16 := by
            rw [Nat.mul_mod]
    _ = ((x % 16) * 1) % 16 := by rw [hfourpow]
    _ = x % 16 := by simp

/-- If an odd base has exponent class `3 mod 4`, reduce the power modulo `16`. -/
theorem odd_pow_mod16_of_exp_mod4_three
    {x n : ℕ} (hx : Odd x) (hn : n % 4 = 3) :
    x ^ n % 16 = x ^ 3 % 16 := by
  have hdecomp : n = 4 * (n / 4) + 3 := by
    have hmad := Nat.mod_add_div n 4
    omega
  have hfour : x ^ 4 % 16 = 1 := odd_pow_four_mod_sixteen hx
  have hfourpow :
    (x ^ 4) ^ (n / 4) % 16 = 1 := by
    exact pow_mod16_eq_one_of_mod16_eq_one hfour
  rw [hdecomp]
  rw [show 4 * (n / 4) + 3 = 3 + 4 * (n / 4) by omega]
  rw [pow_add, pow_mul]
  calc
    (x ^ 3 * (x ^ 4) ^ (n / 4)) % 16
        = ((x ^ 3 % 16) * (((x ^ 4) ^ (n / 4)) % 16)) % 16 := by
            rw [Nat.mul_mod]
    _ = ((x ^ 3 % 16) * 1) % 16 := by rw [hfourpow]
    _ = x ^ 3 % 16 := by simp

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
