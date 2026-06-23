import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step10ElementaryNumberTheory

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Remaining exponent-coprime target for the pure two-power frontier.

Mathematically this asks for `gcd(u,v)=1` in the model
`p^u + q^v = 2^w`.  This is separated from the mod-8 layer because its usual
proof route uses factorization of `X^d + Y^d` or primitive-divisor style input,
rather than the `{2}` C-surplus identification from Steps 8--9. -/
def ExponentCoprimeGoal (F : NormalForm T P) : Prop :=
  Nat.Coprime F.u F.v

/-- Collected elementary targets beyond the already-realized support/radical,
coefficient, and `{2}` C-surplus layers. -/
structure HardElementaryGoals (F : NormalForm T P) where
  elementary : F.ElementaryConstraintsGoal
  exponent_coprime : F.ExponentCoprimeGoal

/-- Wrapper extracting exponent coprimality from the remaining elementary package. -/
theorem exponentCoprime_of_hardElementaryGoals
    (F : NormalForm T P)
    (H : HardElementaryGoals F) :
    F.ExponentCoprimeGoal :=
  H.exponent_coprime

private theorem odd_not_even_nat {m : ℕ} :
    Odd m → Even m → False := by
  intro hm_odd hm_even
  rcases hm_odd with ⟨a, ha⟩
  rcases hm_even with ⟨b, hb⟩
  have hmod_odd : m % 2 = 1 := by
    rw [ha]
    simp [Nat.add_mod]
  have hmod_even : m % 2 = 0 := by
    rw [hb]
    rw [← Nat.two_mul b]
    exact Nat.mul_mod_right 2 b
  rw [hmod_even] at hmod_odd
  exact (by decide : ¬ (0 : ℕ) = 1) hmod_odd

/-- If a positive odd divisor divides a power of `2`, it must be `1`. -/
private theorem odd_dvd_two_pow_eq_one
    {m w : ℕ} (hm_odd : Odd m) (hm_dvd : m ∣ 2 ^ w) :
    m = 1 := by
  by_contra hm_ne_one
  obtain ⟨r, hr, hrdvd⟩ :=
    Nat.exists_prime_and_dvd hm_ne_one
  have hr_dvd_two_pow : r ∣ 2 ^ w :=
    dvd_trans hrdvd hm_dvd
  have hr_dvd_two : r ∣ 2 :=
    hr.dvd_of_dvd_pow hr_dvd_two_pow
  have hr_eq_two : r = 2 :=
    (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hr_dvd_two
  have htwo_dvd_m : 2 ∣ m := by
    rw [← hr_eq_two]
    exact hrdvd
  have hm_even : Even m := by
    rcases htwo_dvd_m with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    exact Nat.two_mul k
  exact odd_not_even_nat hm_odd hm_even

private theorem even_of_two_dvd {n : ℕ} :
    2 ∣ n → Even n := by
  intro h
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [hk]
  exact Nat.two_mul k

/-- A common divisor `2 | u,v` contradicts the already-proved mod-8 elementary
obstruction. -/
private theorem two_not_common_exponent_divisor
    (F : NormalForm T P) :
    ¬ (2 ∣ F.u ∧ 2 ∣ F.v) := by
  intro h
  rcases h with ⟨hu2, hv2⟩
  have hu_even : Even F.u :=
    even_of_two_dvd hu2
  have hv_even : Even F.v :=
    even_of_two_dvd hv2
  have HE : ElementaryConstraints F :=
    F.elementaryConstraints_real
  exact HE.not_both_exponents_even ⟨hu_even, hv_even⟩

/-- For odd `n`, `X+Y` divides `X^n+Y^n`.

This is the divisibility part of the odd-power factorization, obtained from
`x^n - y^n` by substituting `y := -Y` over `ℤ`. -/
private theorem add_dvd_pow_add_pow_of_odd
    {X Y n : ℕ} (hn : Odd n) :
    X + Y ∣ X ^ n + Y ^ n := by
  have hsub :
      ((X : ℤ) - (-(Y : ℤ))) ∣
        (X : ℤ) ^ n - (-(Y : ℤ)) ^ n :=
    (Commute.all (X : ℤ) (-(Y : ℤ))).sub_dvd_pow_sub_pow n
  have hneg : (-(Y : ℤ)) ^ n = -((Y : ℤ) ^ n) :=
    hn.neg_pow (Y : ℤ)
  have hsub' :
      ((X : ℤ) + (Y : ℤ)) ∣
        (X : ℤ) ^ n + (Y : ℤ) ^ n := by
    simpa [sub_eq_add_neg, hneg] using hsub
  have hcast :
      (((X + Y : ℕ) : ℤ)) ∣
        (((X ^ n + Y ^ n : ℕ) : ℤ)) := by
    simpa [Nat.cast_add, Nat.cast_pow] using hsub'
  exact Int.natCast_dvd_natCast.mp hcast

/-- If `S = A*Q` and `S` is strictly larger than `A`, then the quotient is
larger than `1`. -/
private theorem quotient_gt_one_of_factor_gt
    {A S Q : ℕ}
    (hfactor : S = A * Q)
    (hgt : A < S) :
    1 < Q := by
  by_contra hnot
  have hQle : Q ≤ 1 :=
    Nat.le_of_not_gt hnot
  have hAQle : A * Q ≤ A * 1 :=
    Nat.mul_le_mul_left A hQle
  have hSle : S ≤ A := by
    calc
      S = A * Q := hfactor
      _ ≤ A * 1 := hAQle
      _ = A := by rw [Nat.mul_one]
  exact not_lt_of_ge hSle hgt

/-- If `1 < a` and `2 ≤ n`, then `a < a^n`. -/
private theorem lt_pow_of_one_lt_of_two_le
    {a n : ℕ} (ha : 1 < a) (hn : 2 ≤ n) :
    a < a ^ n := by
  have ha_pos : 0 < a :=
    Nat.lt_trans Nat.zero_lt_one ha
  have hsq : a < a ^ 2 := by
    rw [pow_two]
    nlinarith
  have hmono : a ^ 2 ≤ a ^ n :=
    pow_le_pow_right' (Nat.succ_le_of_lt ha_pos) hn
  exact lt_of_lt_of_le hsq hmono

/-- `X+Y` is even when `X,Y` are odd. -/
private theorem even_add_of_odd_odd
    {X Y : ℕ} (hX : Odd X) (hY : Odd Y) :
    Even (X + Y) := by
  rcases hX with ⟨a, ha⟩
  rcases hY with ⟨b, hb⟩
  refine ⟨a + b + 1, ?_⟩
  rw [ha, hb]
  omega

private theorem pos_of_odd_nat {n : ℕ} (hn : Odd n) :
    0 < n := by
  rcases hn with ⟨k, hk⟩
  rw [hk]
  omega

/-- If `Z` is odd, then `A*Z` is congruent to `A` modulo `2*A`. -/
private theorem mul_odd_mod_two_mul_self
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
private theorem sq_mod_two_mul_add_eq_of_odd_odd
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
/-- Equal residues remain equal after taking powers. -/
private theorem pow_mod_eq_of_mod_eq
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
                rw [← Nat.mul_mod]

private theorem odd_pow_sum_mod_two_mul_sum
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

private theorem odd_binomial_quotient_nat
    {A Y n R : ℕ}
    (hA_even : Even A)
    (hY_odd : Odd Y)
    (hn_odd : Odd n)
    (hY_le_A : Y ≤ A)
    (hfactor : (A - Y) ^ n + Y ^ n = A * R) :
    Odd R := by
  let X : ℕ := A - Y
  have hX_add_Y : X + Y = A := by
    dsimp [X]
    exact Nat.sub_add_cancel hY_le_A
  have hA_pos : 0 < A := by
    have hY_pos : 0 < Y := by
      rcases hY_odd with ⟨k, hk⟩
      rw [hk]
      omega
    exact lt_of_lt_of_le hY_pos hY_le_A
  have hX_odd : Odd X := by
    -- A even, Y odd, X+Y=A, so X odd.
    by_contra hnot
    have hX_even : Even X := Nat.not_odd_iff_even.mp hnot
    have hsum_odd : Odd (X + Y) := by
      rcases hX_even with ⟨a, ha⟩
      rcases hY_odd with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      rw [ha, hb]
      omega
    have hA_odd : Odd A := by
      rw [← hX_add_Y]
      exact hsum_odd
    exact odd_not_even_nat hA_odd hA_even
  have hmod_sum :
      (X ^ n + Y ^ n) % (2 * (X + Y)) = X + Y :=
    odd_pow_sum_mod_two_mul_sum hX_odd hY_odd hn_odd
  have hmod_A :
      (A * R) % (2 * A) = A := by
    rw [← hfactor]
    dsimp [X] at hmod_sum
    simpa [Nat.sub_add_cancel hY_le_A] using hmod_sum
  by_contra hR_not_odd
  have hR_even : Even R :=
    Nat.not_odd_iff_even.mp hR_not_odd
  rcases hR_even with ⟨k, hk⟩
  have hmod_even : (A * R) % (2 * A) = 0 := by
    rw [hk]
    have hrewrite : A * (k + k) = (2 * A) * k := by
      nlinarith
    rw [hrewrite]
    exact Nat.mul_mod_right (2 * A) k
  rw [hmod_even] at hmod_A
  have hA_lt_twoA : A < 2 * A := by
    nlinarith
  have hA_mod : A % (2 * A) = A :=
    Nat.mod_eq_of_lt hA_lt_twoA
  have hzero_ne_A : (0 : ℕ) ≠ A := by
    exact Nat.ne_of_lt hA_pos
  exact hzero_ne_A hmod_A

private theorem odd_quotient_of_odd_add_pow_factor
    {X Y n Q : ℕ}
    (hX_odd : Odd X) (hY_odd : Odd Y) (hn_odd : Odd n)
    (hfactor : X ^ n + Y ^ n = (X + Y) * Q) :
    Odd Q := by
  let A : ℕ := X + Y
  have hA_even : Even A := by
    dsimp [A]
    rcases hX_odd with ⟨a, ha⟩
    rcases hY_odd with ⟨b, hb⟩
    refine ⟨a + b + 1, ?_⟩
    rw [ha, hb]
    omega
  have hY_le_A : Y ≤ A := by
    dsimp [A]
    exact Nat.le_add_left Y X
  have hA_sub_Y : A - Y = X := by
    dsimp [A]
    omega
  have hfactorA : (A - Y) ^ n + Y ^ n = A * Q := by
    rw [hA_sub_Y]
    dsimp [A]
    exact hfactor
  exact odd_binomial_quotient_nat
    hA_even hY_odd hn_odd hY_le_A hfactorA

/-- Standard algebraic factorization input.

This is a classical consequence of the odd-power identity
`X^ℓ + Y^ℓ = (X+Y)(X^(ℓ-1)-X^(ℓ-2)Y+...+Y^(ℓ-1))`,
together with parity and the inequalities `1 < X`, `1 < Y`, `3 ≤ ℓ`.

It is separated from `NormalForm` because it is not an ABC-specific fact. -/
private theorem odd_prime_add_pow_factor_has_odd_gt_one_quotient
    {X Y ℓ : ℕ}
    (hX_odd : Odd X) (hY_odd : Odd Y)
    (hX_gt_one : 1 < X) (hY_gt_one : 1 < Y)
    (hℓ_prime : Nat.Prime ℓ) (hℓ_ne_two : ℓ ≠ 2) :
    ∃ Q : ℕ,
      X ^ ℓ + Y ^ ℓ = (X + Y) * Q ∧ Odd Q ∧ 1 < Q := by
  have hℓ_odd : Odd ℓ :=
    odd_of_prime_ne_two hℓ_prime hℓ_ne_two
  have hdiv : X + Y ∣ X ^ ℓ + Y ^ ℓ :=
    add_dvd_pow_add_pow_of_odd hℓ_odd
  let Q : ℕ := (X ^ ℓ + Y ^ ℓ) / (X + Y)
  have hQeq : X ^ ℓ + Y ^ ℓ = (X + Y) * Q := by
    dsimp [Q]
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel hdiv).symm
  have hQodd : Odd Q :=
    odd_quotient_of_odd_add_pow_factor hX_odd hY_odd hℓ_odd hQeq
  have hℓ_three : 3 ≤ ℓ := by
    have htwo : 2 ≤ ℓ := hℓ_prime.two_le
    omega
  have hℓ_two : 2 ≤ ℓ := by
    exact le_trans (by decide : 2 ≤ 3) hℓ_three
  have hX_lt_pow : X < X ^ ℓ :=
    lt_pow_of_one_lt_of_two_le hX_gt_one hℓ_two
  have hY_lt_pow : Y < Y ^ ℓ :=
    lt_pow_of_one_lt_of_two_le hY_gt_one hℓ_two
  have hsum_gt : X + Y < X ^ ℓ + Y ^ ℓ :=
    Nat.add_lt_add hX_lt_pow hY_lt_pow
  have hQgt : 1 < Q :=
    quotient_gt_one_of_factor_gt hQeq hsum_gt
  exact ⟨Q, hQeq, hQodd, hQgt⟩



/-- Odd common prime exponent obstruction.

If an odd prime `ℓ` divides both exponents in

`p^u + q^v = 2^w`

then writing `u = ℓ*u'`, `v = ℓ*v'` gives

`X^ℓ + Y^ℓ = 2^w`.

For odd `ℓ`, the quotient `(X^ℓ + Y^ℓ)/(X+Y)` is an odd integer greater
than `1`, hence it is an odd divisor of a power of `2`, impossible.

This is the factorization part of exponent-coprimality. -/
private theorem odd_prime_not_common_exponent_divisor
    (F : NormalForm T P)
    {ℓ : ℕ} (hℓ_prime : Nat.Prime ℓ) (hℓ_ne_two : ℓ ≠ 2) :
    ¬ (ℓ ∣ F.u ∧ ℓ ∣ F.v) := by
  intro hcommon
  rcases hcommon with ⟨hu_dvd, hv_dvd⟩
  rcases hu_dvd with ⟨u', hu'⟩
  rcases hv_dvd with ⟨v', hv'⟩
  let X : ℕ := F.p ^ u'
  let Y : ℕ := F.q ^ v'
  have hℓ_odd : Odd ℓ :=
    odd_of_prime_ne_two hℓ_prime hℓ_ne_two
  have hX_odd : Odd X := by
    dsimp [X]
    exact (show Odd (F.p ^ u') from
      (odd_of_prime_ne_two F.p_prime F.p_ne_two).pow)
  have hY_odd : Odd Y := by
    dsimp [Y]
    exact (show Odd (F.q ^ v') from
      (odd_of_prime_ne_two F.q_prime F.q_ne_two).pow)
  have hX_pos : 0 < X := by
    dsimp [X]
    exact Nat.pow_pos F.p_pos
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Nat.pow_pos F.q_pos
  have hXY_pos : 0 < X + Y :=
    Nat.add_pos_left hX_pos Y
  have hsourceXY : X ^ ℓ + Y ^ ℓ = 2 ^ F.w := by
    dsimp [X, Y]
    calc
      (F.p ^ u') ^ ℓ + (F.q ^ v') ^ ℓ
          = F.p ^ (u' * ℓ) + F.q ^ (v' * ℓ) := by
              rw [pow_mul, pow_mul]
      _ = F.p ^ F.u + F.q ^ F.v := by
              rw [hu', hv']
              rw [Nat.mul_comm u' ℓ, Nat.mul_comm v' ℓ]
      _ = 2 ^ F.w := F.source_sum_eq_two_pow
  have hu'_pos : 0 < u' := by
    by_contra hnot
    have hu0 : u' = 0 := Nat.eq_zero_of_not_pos hnot
    have hu_zero : F.u = 0 := by
      rw [hu', hu0, Nat.mul_zero]
    exact (Nat.ne_of_gt F.u_pos) hu_zero
  have hv'_pos : 0 < v' := by
    by_contra hnot
    have hv0 : v' = 0 := Nat.eq_zero_of_not_pos hnot
    have hv_zero : F.v = 0 := by
      rw [hv', hv0, Nat.mul_zero]
    exact (Nat.ne_of_gt F.v_pos) hv_zero
  have hX_gt_one : 1 < X := by
    dsimp [X]
    have hp_le_pow : F.p ≤ F.p ^ u' :=
      self_le_pow_of_pos_exp F.p_pos hu'_pos
    exact lt_of_lt_of_le
      (by decide : 1 < 3)
      (le_trans F.three_le_p hp_le_pow)
  have hY_gt_one : 1 < Y := by
    dsimp [Y]
    have hq_le_pow : F.q ≤ F.q ^ v' :=
      self_le_pow_of_pos_exp F.q_pos hv'_pos
    exact lt_of_lt_of_le
      (by decide : 1 < 5)
      (le_trans F.five_le_q_real hq_le_pow)
  have hfactor :
      ∃ Q : ℕ,
        X ^ ℓ + Y ^ ℓ = (X + Y) * Q ∧ Odd Q ∧ 1 < Q :=
    odd_prime_add_pow_factor_has_odd_gt_one_quotient
      hX_odd hY_odd hX_gt_one hY_gt_one hℓ_prime hℓ_ne_two
  rcases hfactor with ⟨Q, hQeq, hQodd, hQgt⟩
  have hQ_dvd_two_pow : Q ∣ 2 ^ F.w := by
    refine ⟨X + Y, ?_⟩
    rw [← hsourceXY, hQeq, Nat.mul_comm]
  have hQeq_one : Q = 1 :=
    odd_dvd_two_pow_eq_one hQodd hQ_dvd_two_pow
  exact (Nat.ne_of_gt hQgt) hQeq_one

/-- No prime can divide both exponents in the pure two-power model. -/
private theorem no_common_prime_exponent_divisor
    (F : NormalForm T P)
    {ℓ : ℕ} (hℓ_prime : Nat.Prime ℓ) :
    ¬ (ℓ ∣ F.u ∧ ℓ ∣ F.v) := by
  by_cases hℓ2 : ℓ = 2
  · subst ℓ
    exact two_not_common_exponent_divisor F
  · exact odd_prime_not_common_exponent_divisor F hℓ_prime hℓ2

/-- Realization of exponent coprimality in the pure two-power model. -/
theorem exponentCoprime (F : NormalForm T P) :
    F.ExponentCoprimeGoal := by
  rw [ExponentCoprimeGoal]
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hgcd_ne_one
  obtain ⟨ℓ, hℓ_prime, hℓ_dvd_gcd⟩ :=
    Nat.exists_prime_and_dvd hgcd_ne_one
  have hℓ_dvd_u : ℓ ∣ F.u :=
    dvd_trans hℓ_dvd_gcd (Nat.gcd_dvd_left F.u F.v)
  have hℓ_dvd_v : ℓ ∣ F.v :=
    dvd_trans hℓ_dvd_gcd (Nat.gcd_dvd_right F.u F.v)
  exact no_common_prime_exponent_divisor F hℓ_prime
    ⟨hℓ_dvd_u, hℓ_dvd_v⟩

/-- The full remaining elementary package is available for the pure two-power
frontier, modulo the localized arithmetic `sorry`s above. -/
theorem hardElementaryGoals (F : NormalForm T P) :
    HardElementaryGoals F :=
  { elementary := F.elementaryConstraintsGoal
    exponent_coprime := F.exponentCoprime }

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
