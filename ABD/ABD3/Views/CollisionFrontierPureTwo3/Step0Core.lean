import ABD.ABD3.Views.CollisionFrontierA

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo3

/-- A prime divisor of a prime power divides the base prime. -/
theorem prime_dvd_base_of_dvd_prime_pow
    {p q e : ℕ} (hq : Nat.Prime q)
    (hdiv : q ∣ p ^ e) :
    q ∣ p := by
  exact hq.dvd_of_dvd_pow hdiv

/-- A prime divisor of a prime power with prime base is the base prime. -/
theorem prime_eq_base_of_dvd_prime_pow
    {p q e : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hdiv : q ∣ p ^ e) :
    q = p := by
  have hqp_dvd : q ∣ p :=
    prime_dvd_base_of_dvd_prime_pow hq hdiv
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp_dvd

/-- Prime-power support computation used by the pure two-power normal form. -/
theorem primeSupport_prime_pow_self
    {p e : ℕ} (hp : Nat.Prime p) (he : 0 < e) :
    primeSupport (p ^ e) = ({p} : Support) := by
  ext q
  constructor
  · intro hqmem
    have hqprime : Nat.Prime q := prime_of_mem_primeSupport hqmem
    have hqdiv : q ∣ p ^ e := dvd_of_mem_primeSupport hqmem
    have hqp : q = p := prime_eq_base_of_dvd_prime_pow hp hqprime hqdiv
    simp [hqp]
  · intro hqmem
    have hqp : q = p := by
      simpa using hqmem
    subst q
    have hfac : (p ^ e).factorization p = e := by
      simpa [vp] using
        (Nat.factorization_pow_self (p := p) (n := e) hp)
    unfold primeSupport
    rw [Finsupp.mem_support_iff]
    rw [hfac]
    exact Nat.ne_of_gt he

/-- Prime-power coefficient computation used by synchronization generators. -/
theorem coeffOf_prime_pow_self_natAbs
    {p e : ℕ} (hp : Nat.Prime p) (he : 0 < e) :
    Int.natAbs (coeffOf (p ^ e) p) = e * p ^ (e - 1) := by
  have hfac : vp (p ^ e) p = e := by
    simpa [vp] using
      (Nat.factorization_pow_self (p := p) (n := e) hp)
  have hdiv : p ^ e / p = p ^ (e - 1) := by
    cases e with
    | zero =>
        omega
    | succ k =>
        have hdiv' : p ^ Nat.succ k / p = p ^ k := by
          rw [pow_succ']
          exact Nat.mul_div_cancel_left (p ^ k) hp.pos
        simpa using hdiv'
  calc
    Int.natAbs (coeffOf (p ^ e) p)
        = Int.natAbs ((e : ℤ) * ((p ^ (e - 1) : ℕ) : ℤ)) := by
            simp [coeffOf, hfac, hdiv]
    _ = e * p ^ (e - 1) := by
            rw [Int.natAbs_mul]
            simp

/-- The numerator `N` of a `PowerData` is positive. -/
theorem powerData_N_pos (P : PowerData) : 0 < P.N := by
  exact lt_of_le_of_lt (Nat.zero_le P.M) P.exponent_lt_one

end CollisionFrontierPureTwo3
end ABCData
end ABD3
