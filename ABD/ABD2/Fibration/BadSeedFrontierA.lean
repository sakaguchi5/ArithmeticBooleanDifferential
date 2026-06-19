import ABD.ABD2.Fibration.Frontier

namespace ABD2
namespace ABCTriple

/-- A named local condition for A-frontier analysis: the Wronskian form is not
identically zero on the full tangent module.

This is deliberately profile-free.  The point of the A-reduction is that the
profile gcd condition cannot create a genuine base obstruction once the profile
has a nonzero gcd; it only asks whether the Wronskian form itself is the zero
linear form. -/
def HasNonzeroWronskianDirection (T : ABCTriple) : Prop :=
  ∃ x : T.FullTangent, T.Wronskian x ≠ 0

/-- The profile gcd dilation of any tangent is automatically compatible with the
AB base of that profile.

This is the key full-rank observation: `P.gcd • x` always satisfies
`P.gcd ∣ abTarget`.  Hence `ABBase P` contains the full-rank scaled copy
`P.gcd • T.FullTangent`. -/
theorem profileGcd_smul_mem_ABBase
    (T : ABCTriple) (P : T.CImageProfile) (x : T.FullTangent) :
    P.gcd • x ∈ T.ABBase P := by
  change P.gcd ∣ T.abTarget (P.gcd • x)
  rw [T.abTarget_smul]
  simp

/-- Scaling by the nonzero profile gcd preserves Wronskian nonvanishing. -/
theorem Wronskian_ne_zero_of_profileGcd_smul
    (T : ABCTriple) (P : T.CImageProfile) {x : T.FullTangent}
    (hx : T.Wronskian x ≠ 0) :
    T.Wronskian (P.gcd • x) ≠ 0 := by
  intro hzero
  rw [T.Wronskian_smul] at hzero
  have hmul : P.gcd * T.Wronskian x = 0 := by
    simpa using hzero
  exact hx ((mul_eq_zero.mp hmul).resolve_left P.gcd_ne_zero)

/-- If a profile is bad, then the Wronskian form vanishes on every tangent.

Indeed, `P.gcd • x` lies in `ABBase P`; badness puts it in the Wronskian
kernel; since `P.gcd ≠ 0`, torsion-freeness of `ℤ` forces `Wronskian x = 0`. -/
theorem Wronskian_eq_zero_of_badSeed
    (T : ABCTriple) (P : T.CImageProfile)
    (hbad : T.BadSeed P) (x : T.FullTangent) :
    T.Wronskian x = 0 := by
  have hbase : P.gcd • x ∈ T.ABBase P :=
    T.profileGcd_smul_mem_ABBase P x
  have hle : T.ABBase P ≤ T.BaseWronskianKernel :=
    (T.badSeed_iff_ABBase_le_BaseWronskianKernel P).1 hbad
  have hker : P.gcd • x ∈ T.BaseWronskianKernel := hle hbase
  have hscaled : T.Wronskian (P.gcd • x) = 0 := by
    simpa using hker
  rw [T.Wronskian_smul] at hscaled
  have hmul : P.gcd * T.Wronskian x = 0 := by
    simpa using hscaled
  exact (mul_eq_zero.mp hmul).resolve_left P.gcd_ne_zero

/-- A profile is bad exactly when the Wronskian form is globally zero.

This removes the profile-specific gcd congruence from the A-frontier: because
`P.gcd` is nonzero, the compatible base is large enough to detect any nonzero
Wronskian direction. -/
theorem badSeed_iff_forall_Wronskian_eq_zero
    (T : ABCTriple) (P : T.CImageProfile) :
    T.BadSeed P ↔ ∀ x : T.FullTangent, T.Wronskian x = 0 := by
  constructor
  · intro hbad x
    exact T.Wronskian_eq_zero_of_badSeed P hbad x
  · intro hzero
    apply (T.badSeed_iff_ABBase_le_BaseWronskianKernel P).2
    intro x _hx
    change T.Wronskian x = 0
    exact hzero x

/-- Fibration-frontier version of `badSeed_iff_forall_Wronskian_eq_zero`. -/
theorem badSeedFrontier_iff_forall_Wronskian_eq_zero
    (T : ABCTriple) (P : T.CImageProfile) :
    T.BadSeedFrontier P ↔ ∀ x : T.FullTangent, T.Wronskian x = 0 := by
  exact (T.badSeedFrontier_iff_badSeed P).trans
    (T.badSeed_iff_forall_Wronskian_eq_zero P)

/-- Any nonzero Wronskian direction gives a good base point for every nonzero-gcd
profile.

The good base point is the scaled direction `P.gcd • x`: it is automatically
compatible and remains Wronskian-nondegenerate. -/
theorem hasGoodBasePoint_of_hasNonzeroWronskianDirection
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasNonzeroWronskianDirection) :
    T.HasGoodBasePoint P := by
  rcases h with ⟨x, hx⟩
  refine ⟨P.gcd • x, ?_, ?_⟩
  · exact T.profileGcd_smul_mem_ABBase P x
  · intro hker
    have hzero : T.Wronskian (P.gcd • x) = 0 := by
      simpa using hker
    exact (T.Wronskian_ne_zero_of_profileGcd_smul P hx) hzero

/-- A good base point is the same thing as a nonzero Wronskian direction.

This is the clean local solution of A: the only possible BadSeedFrontier is the
case where the Wronskian form is identically zero.  The C-profile congruence
itself cannot create a bad seed obstruction. -/
theorem hasGoodBasePoint_iff_hasNonzeroWronskianDirection
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasGoodBasePoint P ↔ T.HasNonzeroWronskianDirection := by
  constructor
  · intro hgood
    rcases hgood with ⟨x, _hxbase, hxnotker⟩
    refine ⟨x, ?_⟩
    intro hzero
    apply hxnotker
    change T.Wronskian x = 0
    exact hzero
  · intro h
    exact T.hasGoodBasePoint_of_hasNonzeroWronskianDirection P h

/-- Absence of the A-frontier is equivalent to the existence of one nonzero
Wronskian direction. -/
theorem not_badSeedFrontier_iff_hasNonzeroWronskianDirection
    (T : ABCTriple) (P : T.CImageProfile) :
    ¬ T.BadSeedFrontier P ↔ T.HasNonzeroWronskianDirection := by
  exact (T.not_badSeedFrontier_iff_hasGoodBasePoint P).trans
    (T.hasGoodBasePoint_iff_hasNonzeroWronskianDirection P)

/-- Forward elimination form: once the Wronskian form is not globally zero, the
BadSeedFrontier is absent for every nonzero-gcd C-image profile. -/
theorem not_badSeedFrontier_of_hasNonzeroWronskianDirection
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasNonzeroWronskianDirection) :
    ¬ T.BadSeedFrontier P := by
  exact (T.not_badSeedFrontier_iff_hasNonzeroWronskianDirection P).2 h

/-- Contrapositive form: if the A-frontier appears, then the Wronskian form is
identically zero. -/
theorem forall_Wronskian_eq_zero_of_badSeedFrontier
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.BadSeedFrontier P) :
    ∀ x : T.FullTangent, T.Wronskian x = 0 := by
  exact (T.badSeedFrontier_iff_forall_Wronskian_eq_zero P).1 h

end ABCTriple
end ABD2
