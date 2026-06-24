import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step3ParityAPI

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Equal residues remain equal after taking powers. -/
theorem pow_mod_eq_of_mod_eq
    {a b M k : ℕ} (h : a % M = b % M) :
    (a ^ k) % M = (b ^ k) % M := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      calc
        (a ^ k * a) % M
            = ((a ^ k % M) * (a % M)) % M := by
                rw [Nat.mul_mod]
        _ = ((b ^ k % M) * (b % M)) % M := by
                rw [ih, h]
        _ = (b ^ k * b) % M := by
                symm
                rw [Nat.mul_mod]

/-- If `Z` is odd, then `A*Z` is congruent to `A` modulo `2*A`. -/
theorem mul_odd_mod_two_mul_self
    {A Z : ℕ} (hApos : 0 < A) (hZodd : Odd Z) :
    (A * Z) % (2 * A) = A := by
  rcases hZodd with ⟨k, hk⟩
  have hlt : A < 2 * A := by
    nlinarith
  calc
    (A * Z) % (2 * A)
        = (A * (2 * k + 1)) % (2 * A) := by
            rw [hk]
    _ = ((2 * A) * k + A) % (2 * A) := by
            have hrewrite : A * (2 * k + 1) = (2 * A) * k + A := by
              nlinarith
            rw [hrewrite]
    _ = A := by
            rw [Nat.add_mod]
            have hmul : ((2 * A) * k) % (2 * A) = 0 :=
              Nat.mul_mod_right (2 * A) k
            rw [hmul]
            simp [Nat.mod_eq_of_lt hlt]

/-- If `X,Y` are odd, then `X^2` and `Y^2` have the same residue modulo
`2*(X+Y)`. -/
theorem sq_mod_two_mul_add_eq_of_odd_odd
    {X Y : ℕ} (hX_odd : Odd X) (hY_odd : Odd Y) :
    (X ^ 2) % (2 * (X + Y)) = (Y ^ 2) % (2 * (X + Y)) := by
  rcases hX_odd with ⟨a, ha⟩
  rcases hY_odd with ⟨b, hb⟩
  let M : ℕ := 2 * (X + Y)
  by_cases hXY : X ≤ Y
  · have hdiff_even : Even (Y - X) := by
      refine ⟨b - a, ?_⟩
      rw [ha, hb]
      omega
    rcases hdiff_even with ⟨t, ht⟩
    have hy : X + (Y - X) = Y :=
      Nat.add_sub_of_le hXY
    have hdiff : Y ^ 2 = X ^ 2 + M * t := by
      dsimp [M]
      nlinarith [hy, ht]
    have hadd_mod :
        (X ^ 2 + M * t) % M = (X ^ 2) % M := by
      rw [Nat.add_mod]
      have hmul_mod : (M * t) % M = 0 :=
        Nat.mul_mod_right M t
      rw [hmul_mod]
      simp
    calc
      (X ^ 2) % M
          = (X ^ 2 + M * t) % M := by
              exact hadd_mod.symm
      _ = (Y ^ 2) % M := by
              rw [hdiff]
  · have hYX : Y ≤ X :=
      Nat.le_of_not_ge hXY
    have hdiff_even : Even (X - Y) := by
      refine ⟨a - b, ?_⟩
      rw [ha, hb]
      omega
    rcases hdiff_even with ⟨t, ht⟩
    have hx : Y + (X - Y) = X :=
      Nat.add_sub_of_le hYX
    have hdiff : X ^ 2 = Y ^ 2 + M * t := by
      dsimp [M]
      nlinarith [hx, ht]
    have hadd_mod :
        (Y ^ 2 + M * t) % M = (Y ^ 2) % M := by
      rw [Nat.add_mod]
      have hmul_mod : (M * t) % M = 0 :=
        Nat.mul_mod_right M t
      rw [hmul_mod]
      simp
    calc
      (X ^ 2) % M
          = (Y ^ 2 + M * t) % M := by
              rw [hdiff]
      _ = (Y ^ 2) % M := by
              exact hadd_mod

/-- Odd powers of odd numbers have the expected `2*(X+Y)` residue. -/
theorem odd_pow_sum_mod_two_mul_sum
    {X Y n : ℕ}
    (hX_odd : Odd X) (hY_odd : Odd Y) (hn_odd : Odd n) :
    (X ^ n + Y ^ n) % (2 * (X + Y)) = X + Y := by
  rcases hn_odd with ⟨k, hk⟩
  let M : ℕ := 2 * (X + Y)
  change (X ^ n + Y ^ n) % M = X + Y
  have hApos : 0 < X + Y :=
    Nat.add_pos_left (pos_of_odd_nat hX_odd) Y
  have hsq_mod :
      (X ^ 2) % M = (Y ^ 2) % M := by
    dsimp [M]
    exact sq_mod_two_mul_add_eq_of_odd_odd hX_odd hY_odd
  have hpow_mod :
      ((X ^ 2) ^ k) % M = ((Y ^ 2) ^ k) % M :=
    pow_mod_eq_of_mod_eq hsq_mod
  have hYsq_odd : Odd (Y ^ 2) := by
    exact (show Odd (Y ^ 2) from hY_odd.pow)
  have hYpow_odd : Odd ((Y ^ 2) ^ k) := by
    exact (show Odd ((Y ^ 2) ^ k) from hYsq_odd.pow)
  have hXpow : X ^ n = X * (X ^ 2) ^ k := by
    rw [hk]
    rw [show 2 * k + 1 = 1 + 2 * k by omega]
    rw [pow_add, pow_one]
    rw [pow_mul]
  have hYpow : Y ^ n = Y * (Y ^ 2) ^ k := by
    rw [hk]
    rw [show 2 * k + 1 = 1 + 2 * k by omega]
    rw [pow_add, pow_one]
    rw [pow_mul]
  calc
    (X ^ n + Y ^ n) % M
        = (X * (X ^ 2) ^ k + Y * (Y ^ 2) ^ k) % M := by
            rw [hXpow, hYpow]
    _ = (X * (Y ^ 2) ^ k + Y * (Y ^ 2) ^ k) % M := by
            have hxmod :
                (X * (X ^ 2) ^ k) % M =
                  (X * (Y ^ 2) ^ k) % M := by
              calc
                (X * (X ^ 2) ^ k) % M
                    = ((X % M) * (((X ^ 2) ^ k) % M)) % M := by
                        rw [Nat.mul_mod]
                _ = ((X % M) * (((Y ^ 2) ^ k) % M)) % M := by
                        rw [hpow_mod]
                _ = (X * (Y ^ 2) ^ k) % M := by
                        symm
                        rw [Nat.mul_mod]
            calc
              (X * (X ^ 2) ^ k + Y * (Y ^ 2) ^ k) % M
                  = (((X * (X ^ 2) ^ k) % M +
                        (Y * (Y ^ 2) ^ k) % M) % M) := by
                      rw [Nat.add_mod]
              _ = (((X * (Y ^ 2) ^ k) % M +
                        (Y * (Y ^ 2) ^ k) % M) % M) := by
                      rw [hxmod]
              _ = (X * (Y ^ 2) ^ k + Y * (Y ^ 2) ^ k) % M := by
                      symm
                      rw [Nat.add_mod]
    _ = ((X + Y) * (Y ^ 2) ^ k) % M := by
            have hdist :
                (X + Y) * (Y ^ 2) ^ k =
                  X * (Y ^ 2) ^ k + Y * (Y ^ 2) ^ k := by
              rw [Nat.add_mul]
            rw [hdist]
    _ = X + Y := by
            dsimp [M]
            exact mul_odd_mod_two_mul_self hApos hYpow_odd

/-- Odd squares are `1 mod 8`. -/
theorem odd_sq_mod_eight {x : ℕ} (hx : Odd x) :
    x ^ 2 % 8 = 1 := by
  rcases hx with ⟨k, rfl⟩
  have hEven : Even (k * (k + 1)) := Nat.even_mul_succ_self k
  rcases hEven with ⟨m, hm⟩
  have hsq : (2 * k + 1) ^ 2 = 8 * m + 1 := by
    nlinarith
  rw [hsq]
  simp

/-- An odd base to an even exponent is `1 mod 8`. -/
theorem odd_pow_even_exp_mod_eight
    {x n : ℕ} (hx : Odd x) (hn : Even n) :
    x ^ n % 8 = 1 := by
  rcases hn with ⟨k, rfl⟩
  rw [pow_add]
  simpa [pow_two] using odd_sq_mod_eight (hx.pow (n := k))

/-- An odd base to an odd exponent has the same residue as the base mod `8`. -/
theorem odd_pow_odd_exp_mod_eight
    {x n : ℕ} (hx : Odd x) (hn : Odd n) :
    x ^ n % 8 = x % 8 := by
  rcases hn with ⟨k, rfl⟩
  have h2k_even : Even (2 * k) := by
    exact ⟨k, Nat.two_mul k⟩
  have heven : x ^ (2 * k) % 8 = 1 :=
    odd_pow_even_exp_mod_eight hx h2k_even
  rw [pow_succ]
  calc
    (x ^ (2 * k) * x) % 8
        = ((x ^ (2 * k) % 8) * (x % 8)) % 8 := by
            rw [Nat.mul_mod]
    _ = (1 * (x % 8)) % 8 := by
            rw [heven]
    _ = x % 8 := by
            simp

/-- From `(1+x) mod 8 = 0` and `x < 8`, infer `x = 7`. -/
theorem mod8_eq_seven_of_one_add_mod8_eq_zero
    {x : ℕ} (hx : x < 8) (h : (1 + x) % 8 = 0) :
    x = 7 := by
  omega

/-- Convert source-sum mod-zero into residue-sum mod-zero. -/
theorem add_mod_eight_zero_of_sum_mod_eight
    {a b : ℕ} (h : (a + b) % 8 = 0) :
    ((a % 8) + (b % 8)) % 8 = 0 := by
  have hrewrite :
      (a + b) % 8 = ((a % 8) + (b % 8)) % 8 := by
    rw [Nat.add_mod]
  rw [← hrewrite]
  exact h

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
