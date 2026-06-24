import ABD.ABD3.Views.CollisionFrontierPureTwo3.Step2PrimeBounds

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- Odd and even natural numbers are disjoint. -/
theorem odd_not_even_nat {m : ℕ} :
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

/-- Convert divisibility by `2` into `Even`. -/
theorem even_of_two_dvd {n : ℕ} :
    2 ∣ n → Even n := by
  intro h
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [hk]
  exact Nat.two_mul k

/-- Convert `Even` into divisibility by `2`. -/
theorem two_dvd_of_even {n : ℕ} :
    Even n → 2 ∣ n := by
  intro h
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [hk]
  exact (Nat.two_mul k).symm

/-- A prime different from `2` is odd. -/
theorem odd_of_prime_ne_two {p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    Odd p := by
  rcases hp.eq_two_or_odd with h | h
  · exact False.elim (hp2 h)
  · exact Nat.odd_iff.mpr h

/-- Odd natural numbers are positive. -/
theorem pos_of_odd_nat {n : ℕ} (hn : Odd n) :
    0 < n := by
  rcases hn with ⟨k, hk⟩
  rw [hk]
  omega

/-- If an odd divisor divides a power of `2`, it must be `1`. -/
theorem odd_dvd_two_pow_eq_one
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
  have hm_even : Even m := even_of_two_dvd htwo_dvd_m
  exact odd_not_even_nat hm_odd hm_even

/-- The A prime is an odd prime in the elementary sense. -/
theorem p_is_odd_prime_boundary (F : NormalForm T P) :
    Nat.Prime F.p ∧ F.p ≠ 2 :=
  ⟨F.p_prime, F.p_ne_two⟩

/-- The B prime is an odd prime in the elementary sense. -/
theorem q_is_odd_prime_boundary (F : NormalForm T P) :
    Nat.Prime F.q ∧ F.q ≠ 2 :=
  ⟨F.q_prime, F.q_ne_two⟩

/-- The A base is odd. -/
theorem p_odd (F : NormalForm T P) :
    Odd F.p :=
  odd_of_prime_ne_two F.p_prime F.p_ne_two

/-- The B base is odd. -/
theorem q_odd (F : NormalForm T P) :
    Odd F.q :=
  odd_of_prime_ne_two F.q_prime F.q_ne_two

end NormalForm
end CollisionFrontierPureTwo3
end ABCData
end ABD3
