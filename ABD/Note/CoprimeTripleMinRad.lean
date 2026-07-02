import ABD.Note.CoprimeTriple

/-!
# Minimal radical lower bound for ordered pairwise-coprime triples

This file fills the first arithmetic gap after `ABD.Note.CoprimeTriple`.

Target:

If

* `1 < a < b < c`, and
* `a`, `b`, `c` are pairwise coprime,

then the total radical cost is at least the `{2,3,5}` skeleton:

`log₂ 2 + log₂ 3 + log₂ 5
  ≤ log₂(rad a) + log₂(rad b) + log₂(rad c)`.

The proof is split into two layers:

1. an arithmetic lower bound
   `30 ≤ natRad a * natRad b * natRad c`;
2. a logarithmic bridge from the product lower bound to the `tripleLogRad`
   lower bound.
-/

namespace ABD
namespace Note

/--
A prime divisor of `n` belongs to the support product defining `natRad n`,
hence divides `natRad n`.

`Nat.Prime.factorization_pos_of_dvd` needs the explicit nonzero hypothesis.
-/
theorem prime_dvd_natRad_of_prime_dvd
    {p n : ℕ}
    (hp : Nat.Prime p)
    (hn : n ≠ 0)
    (hpn : p ∣ n) :
    p ∣ natRad n := by
  unfold natRad
  have hpos : 0 < n.factorization p := by
    exact hp.factorization_pos_of_dvd hn hpn
  have hmem : p ∈ n.factorization.support := by
    exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hpos)
  exact Finset.dvd_prod_of_mem id hmem

/--
For `1 < n`, the least prime factor of `n` divides `natRad n`.
-/
theorem minFac_dvd_natRad
    {n : ℕ}
    (hn : 1 < n) :
    Nat.minFac n ∣ natRad n := by
  have hn0 : n ≠ 0 := by
    exact Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)
  have hp : Nat.Prime (Nat.minFac n) := by
    exact Nat.minFac_prime (Nat.ne_of_gt hn)
  have hd : Nat.minFac n ∣ n := by
    exact Nat.minFac_dvd n
  exact prime_dvd_natRad_of_prime_dvd hp hn0 hd

/--
If `a` and `b` are coprime and both exceed `1`, then their least prime factors
are distinct.
-/
theorem minFac_ne_of_coprime
    {a b : ℕ}
    (ha : 1 < a)
    (hab : Nat.Coprime a b) :
    Nat.minFac a ≠ Nat.minFac b := by
  intro h
  let p := Nat.minFac a
  have hp : Nat.Prime p := by
    exact Nat.minFac_prime (Nat.ne_of_gt ha)
  have hpa : p ∣ a := by
    exact Nat.minFac_dvd a
  have hpb : p ∣ b := by
    simpa [p, h] using (Nat.minFac_dvd b)
  have hpgcd : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
  have hpone : p ∣ 1 := by
    simpa [hab.gcd_eq_one] using hpgcd
  exact hp.not_dvd_one hpone

/--
A prime different from `2` is at least `3`.
-/
theorem three_le_of_prime_ne_two
    {p : ℕ}
    (hp : Nat.Prime p)
    (hpne2 : p ≠ 2) :
    3 ≤ p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpgt2 : 2 < p := lt_of_le_of_ne hp2 (Ne.symm hpne2)
  exact Nat.succ_le_of_lt hpgt2

/--
A prime different from `2` and `3` is at least `5`.
-/
theorem five_le_of_prime_ne_two_ne_three
    {p : ℕ}
    (hp : Nat.Prime p)
    (hpne2 : p ≠ 2)
    (hpne3 : p ≠ 3) :
    5 ≤ p := by
  have hp3 : 3 ≤ p :=
    three_le_of_prime_ne_two hp hpne2
  have hpgt3 : 3 < p :=
    lt_of_le_of_ne hp3 (Ne.symm hpne3)
  have hpne4 : p ≠ 4 := by
    intro hp4
    have h4 : Nat.Prime 4 := by simpa [hp4] using hp
    have : ¬ Nat.Prime 4 := by decide
    exact this h4
  omega

/--
If `q` and `r` are distinct primes, neither equal to `2`, then
`2 * q * r ≥ 30`.

This packages the `{2,3,5}` payment when the prime `2` is already fixed.
-/
private theorem two_mul_distinct_odd_primes_ge_30
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hr : Nat.Prime r)
    (hqne2 : q ≠ 2)
    (hrne2 : r ≠ 2)
    (hqr : q ≠ r) :
    30 ≤ 2 * q * r := by
  have hq3 : 3 ≤ q := three_le_of_prime_ne_two hq hqne2
  have hr3 : 3 ≤ r := three_le_of_prime_ne_two hr hrne2
  by_cases hqeq3 : q = 3
  · have hrne3 : r ≠ 3 := by
      intro hr3eq
      exact hqr (by simp [hqeq3, hr3eq])
    have hr5 : 5 ≤ r :=
      five_le_of_prime_ne_two_ne_three hr hrne2 hrne3
    nlinarith
  · have hq5 : 5 ≤ q :=
      five_le_of_prime_ne_two_ne_three hq hqne2 hqeq3
    nlinarith

/--
If none of the three primes is `2`, then the product is already at least `30`.

In fact the weak bound used here is `≥ 45`.
-/
private theorem no_two_distinct_primes_mul_ge_30
    {p q r : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hr : Nat.Prime r)
    (hpq : p ≠ q)
    (hpne2 : p ≠ 2)
    (hqne2 : q ≠ 2)
    (hrne2 : r ≠ 2) :
    30 ≤ p * q * r := by
  have hp3 : 3 ≤ p := three_le_of_prime_ne_two hp hpne2
  have hq3 : 3 ≤ q := three_le_of_prime_ne_two hq hqne2
  have hr3 : 3 ≤ r := three_le_of_prime_ne_two hr hrne2
  by_cases hpeq3 : p = 3
  · have hqne3 : q ≠ 3 := by
      intro hqeq3
      exact hpq (by simp [hpeq3, hqeq3])
    have hq5 : 5 ≤ q :=
      five_le_of_prime_ne_two_ne_three hq hqne2 hqne3
    subst p
    have hqr15 : 15 ≤ q * r := by
      exact Nat.mul_le_mul hq5 hr3
    have h3qr45 : 45 ≤ 3 * (q * r) := by
      exact Nat.mul_le_mul_left 3 hqr15
    have h45 : 45 ≤ 3 * q * r := by
      simpa [Nat.mul_assoc] using h3qr45
    nlinarith
  · have hp5 : 5 ≤ p :=
      five_le_of_prime_ne_two_ne_three hp hpne2 hpeq3
    have hqr9 : 9 ≤ q * r := by
      exact Nat.mul_le_mul hq3 hr3
    have hpqr45 : 45 ≤ p * (q * r) := by
      exact Nat.mul_le_mul hp5 hqr9
    have h45 : 45 ≤ p * q * r := by
      simpa [Nat.mul_assoc] using hpqr45
    nlinarith

/--
Three pairwise distinct primes have product at least `2 * 3 * 5 = 30`.

The order of the three primes does not matter.
-/
theorem three_distinct_prime_mul_ge_30
    {p q r : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hr : Nat.Prime r)
    (hpq : p ≠ q)
    (hpr : p ≠ r)
    (hqr : q ≠ r) :
    30 ≤ p * q * r := by
  by_cases hp2 : p = 2
  · subst p
    have hqne2 : q ≠ 2 := by
      intro hq2
      exact hpq (by simp [hq2])
    have hrne2 : r ≠ 2 := by
      intro hr2
      exact hpr (by simp [hr2])
    exact two_mul_distinct_odd_primes_ge_30 hq hr hqne2 hrne2 hqr
  · by_cases hq2 : q = 2
    · subst q
      have hrne2 : r ≠ 2 := by
        intro hr2
        exact hqr (by simp [hr2])
      have h :=
        two_mul_distinct_odd_primes_ge_30 hp hr hp2 hrne2 hpr
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    · by_cases hr2 : r = 2
      · subst r
        have h :=
          two_mul_distinct_odd_primes_ge_30 hp hq hp2 hq2 hpq
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
      · exact no_two_distinct_primes_mul_ge_30 hp hq hr hpq hp2 hq2 hr2

theorem natRad_pos (n : ℕ) : 0 < natRad n := by
  unfold natRad
  exact Finset.prod_pos (by
    intro x hx
    have hxne : x ≠ 0 := by
      intro hx0
      have hxmem : n.factorization x ≠ 0 := by
        exact Finsupp.mem_support_iff.mp hx
      exact hxmem (by simp [hx0])
    exact Nat.pos_of_ne_zero hxne)

/--
Three divisibility facts multiply componentwise.
-/
private theorem mul3_dvd_mul3
    {x y z X Y Z : ℕ}
    (hx : x ∣ X)
    (hy : y ∣ Y)
    (hz : z ∣ Z) :
    x * y * z ∣ X * Y * Z := by
  rcases hx with ⟨A, hA⟩
  rcases hy with ⟨B, hB⟩
  rcases hz with ⟨C, hC⟩
  refine ⟨A * B * C, ?_⟩
  rw [hA, hB, hC]
  ring

/--
The product of the three least prime factors divides the product of radicals,
hence is bounded above by it.
-/
private theorem minFac_mul_le_natRad_mul
    {a b c : ℕ}
    (ha : 1 < a)
    (hb : 1 < b)
    (hc : 1 < c) :
    Nat.minFac a * Nat.minFac b * Nat.minFac c
      ≤ natRad a * natRad b * natRad c := by
  have hdiv :
      Nat.minFac a * Nat.minFac b * Nat.minFac c
        ∣ natRad a * natRad b * natRad c :=
    mul3_dvd_mul3
      (minFac_dvd_natRad ha)
      (minFac_dvd_natRad hb)
      (minFac_dvd_natRad hc)
  have hpos : 0 < natRad a * natRad b * natRad c := by
    exact Nat.mul_pos
      (Nat.mul_pos (natRad_pos a) (natRad_pos b))
      (natRad_pos c)
  exact Nat.le_of_dvd hpos hdiv

/--
The radical product of an ordered pairwise-coprime triple is at least `30`.

This is the arithmetic heart of the `{2,3,5}` minimal skeleton lower bound.
-/
theorem natRad_mul_ge_30_of_orderedPairwiseCoprime3
    {a b c : ℕ}
    (habc : orderedPairwiseCoprime3 a b c) :
    30 ≤ natRad a * natRad b * natRad c := by
  rcases habc with ⟨ha, hab_lt, hbc_lt, hcop⟩
  rcases hcop with ⟨hab_coprime, hac_coprime, hbc_coprime⟩
  have hb : 1 < b := lt_trans ha hab_lt
  have hc : 1 < c := lt_trans hb hbc_lt
  have hmin30 :
      30 ≤ Nat.minFac a * Nat.minFac b * Nat.minFac c := by
    exact three_distinct_prime_mul_ge_30
      (Nat.minFac_prime (Nat.ne_of_gt ha))
      (Nat.minFac_prime (Nat.ne_of_gt hb))
      (Nat.minFac_prime (Nat.ne_of_gt hc))
      (minFac_ne_of_coprime ha hab_coprime)
      (minFac_ne_of_coprime ha hac_coprime)
      (minFac_ne_of_coprime hb hbc_coprime)
  exact le_trans hmin30 (minFac_mul_le_natRad_mul ha hb hc)

/--
Logarithmic bridge from a product lower bound for radicals to the `{2,3,5}`
minimal skeleton lower bound.
-/
theorem minimalCoprimeTripleLogRad_le_of_natRad_mul_ge_30
    {a b c : ℕ}
    (hprod : 30 ≤ natRad a * natRad b * natRad c) :
    minimalCoprimeTripleLogRad
      ≤ tripleLogRad (natLogRad a) (natLogRad b) (natLogRad c) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h5 : (0 : ℝ) < 5 := by norm_num
  have h30 : (0 : ℝ) < 30 := by norm_num
  have hradA_nat : 0 < natRad a := natRad_pos a
  have hradB_nat : 0 < natRad b := natRad_pos b
  have hradC_nat : 0 < natRad c := natRad_pos c
  have hradA : (0 : ℝ) < (natRad a : ℝ) := by
    exact_mod_cast hradA_nat
  have hradB : (0 : ℝ) < (natRad b : ℝ) := by
    exact_mod_cast hradB_nat
  have hradC : (0 : ℝ) < (natRad c : ℝ) := by
    exact_mod_cast hradC_nat
  have hleft :
      minimalCoprimeTripleLogRad = log2 30 := by
    unfold minimalCoprimeTripleLogRad log2
    rw [show (30 : ℝ) = ((2 : ℝ) * 3) * 5 by norm_num]
    rw [Real.log_mul (mul_pos h2 h3).ne' h5.ne']
    rw [Real.log_mul h2.ne' h3.ne']
    ring
  have hcast :
      ((natRad a * natRad b * natRad c : ℕ) : ℝ)
        = ((natRad a : ℝ) * (natRad b : ℝ)) * (natRad c : ℝ) := by
    norm_num
  have hright :
      tripleLogRad (natLogRad a) (natLogRad b) (natLogRad c)
        = log2 ((natRad a * natRad b * natRad c : ℕ) : ℝ) := by
    unfold tripleLogRad natLogRad log2
    rw [hcast]
    rw [Real.log_mul (mul_pos hradA hradB).ne' hradC.ne']
    rw [Real.log_mul hradA.ne' hradB.ne']
    ring
  have hprodReal :
      (30 : ℝ) ≤ ((natRad a * natRad b * natRad c : ℕ) : ℝ) := by
    exact_mod_cast hprod
  have hlog :
      log2 30 ≤ log2 ((natRad a * natRad b * natRad c : ℕ) : ℝ) := by
    exact log2_le_log2_of_pos_of_le h30 hprodReal
  rw [hleft, hright]
  exact hlog

/--
The actual `{2,3,5}` lower bound for an ordered pairwise-coprime triple.
-/
theorem minimalCoprimeTripleLogRad_le_of_orderedPairwiseCoprime3
    {a b c : ℕ}
    (habc : orderedPairwiseCoprime3 a b c) :
    minimalCoprimeTripleLogRad
      ≤ tripleLogRad (natLogRad a) (natLogRad b) (natLogRad c) := by
  exact minimalCoprimeTripleLogRad_le_of_natRad_mul_ge_30
    (natRad_mul_ge_30_of_orderedPairwiseCoprime3 habc)

/--
The `hmin`-free natural-number version of the minimal skeleton danger theorem.
-/
theorem natTripleDanger_le_minimal_skeleton_of_orderedPairwiseCoprime3
    {α : ℝ} {a b c : ℕ}
    (hα : 0 ≤ α)
    (habc : orderedPairwiseCoprime3 a b c) :
    natTripleDanger α a b c
      ≤ minimalCoprimeTripleDanger α
          (natLogScale a) (natLogScale b) (natLogScale c) := by
  exact natTripleDanger_le_minimal_skeleton_of_min_logRad
    hα
    habc
    (minimalCoprimeTripleLogRad_le_of_orderedPairwiseCoprime3 habc)

end Note
end ABD
