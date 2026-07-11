/-
  ABD.ApparitionDepth3.PadicDigit

  Stage 11, first half:
    * extract the ordinary base-p digit from two adjacent reductions of the
      canonical p-adic Teichmuller root;
    * prove the exact natural-number decomposition between the two standard
      representatives.

  These are ordinary p-adic digits.  They are not Witt coefficients.
-/

import ABD.ApparitionDepth3.PadicFiniteBridge

namespace ApparitionDepth3

/-- The ordinary next base-p digit of the branch p-adic root.

It is extracted from the standard representative modulo `p^(r+1)` by division
by `p^r`.  The lower `r` digits are recovered separately by compatibility. -/
noncomputable def branchPadicDigitNat
    (g p d j r : Nat) [Fact p.Prime] : Nat :=
  branchPadicRepresentative g p d j (r + 1) / p ^ r

/-- The same ordinary p-adic digit, viewed in the residue field `ZMod p`. -/
noncomputable def branchPadicDigit
    (g p d j r : Nat) [Fact p.Prime] : ZMod p :=
  (branchPadicDigitNat g p d j r : ZMod p)

/-- Every standard representative is smaller than its modulus. -/
theorem branchPadicRepresentative_lt_modulus
    {g p d j r : Nat} [Fact p.Prime] :
    branchPadicRepresentative g p d j r < p ^ r := by
  unfold branchPadicRepresentative
  exact ZMod.val_lt _

/-- Adjacent standard representatives are equal modulo the lower precision. -/
theorem branchPadicRepresentative_succ_cast
    {g p d j r : Nat} [Fact p.Prime] :
    (branchPadicRepresentative g p d j (r + 1) : ZMod (p ^ r)) =
      (branchPadicRepresentative g p d j r : ZMod (p ^ r)) := by
  have hdiv : p ^ r ∣ p ^ (r + 1) :=
    pow_dvd_pow p (Nat.le_succ r)
  have hhigh := congrArg
    (ZMod.castHom hdiv (ZMod (p ^ r)))
    (branchPadicRepresentative_cast
      (g := g) (p := p) (d := d) (j := j) (r := r + 1))
  have hhigh' :
      (branchPadicRepresentative g p d j (r + 1) : ZMod (p ^ r)) =
        (ZMod.cast (branchPadicReduction g p d j (r + 1)) : ZMod (p ^ r)) := by
    simpa only [ZMod.castHom_apply, ZMod.cast_natCast hdiv] using hhigh
  calc
    (branchPadicRepresentative g p d j (r + 1) : ZMod (p ^ r)) =
        (ZMod.cast (branchPadicReduction g p d j (r + 1)) : ZMod (p ^ r)) :=
      hhigh'
    _ = branchPadicReduction g p d j r :=
      branchPadicReduction_compat (Nat.le_succ r)
    _ = (branchPadicRepresentative g p d j r : ZMod (p ^ r)) :=
      (branchPadicRepresentative_cast
        (g := g) (p := p) (d := d) (j := j) (r := r)).symm

/-- The remainder of the upper representative modulo `p^r` is exactly the
lower representative. -/
theorem branchPadicRepresentative_succ_mod
    {g p d j r : Nat} [Fact p.Prime] :
    branchPadicRepresentative g p d j (r + 1) % p ^ r =
      branchPadicRepresentative g p d j r := by
  let upper := branchPadicRepresentative g p d j (r + 1)
  let lower := branchPadicRepresentative g p d j r
  have hcast : (upper : ZMod (p ^ r)) = (lower : ZMod (p ^ r)) := by
    simpa only [upper, lower] using
      (branchPadicRepresentative_succ_cast
        (g := g) (p := p) (d := d) (j := j) (r := r))
  have hmodEq : upper ≡ lower [MOD p ^ r] :=
    (ZMod.natCast_eq_natCast_iff upper lower (p ^ r)).mp hcast
  change upper % p ^ r = lower % p ^ r at hmodEq
  have hlower : lower < p ^ r := by
    simpa only [lower] using
      (branchPadicRepresentative_lt_modulus
        (g := g) (p := p) (d := d) (j := j) (r := r))
  simpa only [upper, lower, Nat.mod_eq_of_lt hlower] using hmodEq

/-- Exact adjacent-coordinate decomposition of the p-adic root.

The representative modulo `p^(r+1)` consists of the representative modulo
`p^r`, followed by the single ordinary digit `branchPadicDigitNat`. -/
theorem branchPadicRepresentative_succ_decomposition
    {g p d j r : Nat} [Fact p.Prime] :
    branchPadicRepresentative g p d j (r + 1) =
      branchPadicRepresentative g p d j r +
        branchPadicDigitNat g p d j r * p ^ r := by
  let upper := branchPadicRepresentative g p d j (r + 1)
  calc
    upper = upper % p ^ r + p ^ r * (upper / p ^ r) :=
      (Nat.mod_add_div upper (p ^ r)).symm
    _ = branchPadicRepresentative g p d j r +
        branchPadicDigitNat g p d j r * p ^ r := by
      rw [show upper % p ^ r = branchPadicRepresentative g p d j r by
        simpa only [upper] using
          (branchPadicRepresentative_succ_mod
            (g := g) (p := p) (d := d) (j := j) (r := r))]
      simp only [branchPadicDigitNat, upper, Nat.mul_comm]

/-- The extracted ordinary digit is a genuine base-p digit. -/
theorem branchPadicDigitNat_lt_prime
    {g p d j r : Nat} [Fact p.Prime] :
    branchPadicDigitNat g p d j r < p := by
  let upper := branchPadicRepresentative g p d j (r + 1)
  let lower := branchPadicRepresentative g p d j r
  let digit := branchPadicDigitNat g p d j r
  have hupper : upper < p ^ (r + 1) := by
    simpa only [upper] using
      (branchPadicRepresentative_lt_modulus
        (g := g) (p := p) (d := d) (j := j) (r := r + 1))
  have hdecomp : upper = lower + digit * p ^ r := by
    simpa only [upper, lower, digit] using
      (branchPadicRepresentative_succ_decomposition
        (g := g) (p := p) (d := d) (j := j) (r := r))
  by_contra hnot
  have hp_le : p ≤ digit := Nat.le_of_not_gt hnot
  have hmul : p * p ^ r ≤ digit * p ^ r :=
    Nat.mul_le_mul_right (p ^ r) hp_le
  have hterm : digit * p ^ r ≤ upper := by
    calc
      digit * p ^ r ≤ lower + digit * p ^ r := Nat.le_add_left _ _
      _ = upper := hdecomp.symm
  have hpow : p ^ (r + 1) ≤ upper := by
    rw [pow_succ, Nat.mul_comm]
    exact hmul.trans hterm
  exact (Nat.not_le_of_lt hupper) hpow

/-- The upper standard representative is literally the one-step corrected
representative using the extracted ordinary p-adic digit. -/
theorem branchPadicRepresentative_succ_eq_corrected
    {g p d j r : Nat} [Fact p.Prime] :
    branchPadicRepresentative g p d j (r + 1) =
      correctedRepresentative
        (branchPadicRepresentative g p d j r)
        (branchPadicDigitNat g p d j r) p r := by
  simpa only [correctedRepresentative] using
    (branchPadicRepresentative_succ_decomposition
      (g := g) (p := p) (d := d) (j := j) (r := r))

/-- Coordinate form in `ZMod (p^(r+1))`. -/
theorem branchPadicReduction_succ_eq_corrected
    {g p d j r : Nat} [Fact p.Prime] :
    branchPadicReduction g p d j (r + 1) =
      (correctedRepresentative
        (branchPadicRepresentative g p d j r)
        (branchPadicDigitNat g p d j r) p r : ZMod (p ^ (r + 1))) := by
  calc
    branchPadicReduction g p d j (r + 1) =
        (branchPadicRepresentative g p d j (r + 1) : ZMod (p ^ (r + 1))) :=
      (branchPadicRepresentative_cast
        (g := g) (p := p) (d := d) (j := j) (r := r + 1)).symm
    _ = (correctedRepresentative
          (branchPadicRepresentative g p d j r)
          (branchPadicDigitNat g p d j r) p r : ZMod (p ^ (r + 1))) := by
      rw [branchPadicRepresentative_succ_eq_corrected]

end ApparitionDepth3
