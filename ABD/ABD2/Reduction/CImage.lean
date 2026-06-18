import ABD.ABD2.Pasten.All

namespace ABD2
namespace ABCTriple

/-- A deliberately abstract profile for the C-side image.

ABD2 separates the Boolean-mask module theory from the arithmetic work needed to
identify the image of the C-linear form with a concrete gcd.  The old ABD
Theorem 3 can later provide such a profile with `gcd = cCoeffGCD`. -/
structure CImageProfile (T : ABCTriple) where
  gcd : ℤ
  gcd_ne_zero : gcd ≠ 0 := by decide

/-- C-side derivative form, still on the full tangent module but seeing only the
C mask by the general mask theorem. -/
def cLinearForm (T : ABCTriple) (x : T.FullTangent) : ℤ :=
  formalDeriv T.support (T.maskC x) T.c

/-- AB-side target that the C-side must absorb. -/
def abTarget (T : ABCTriple) (x : T.FullTangent) : ℤ :=
  formalDeriv T.support (T.maskA x) T.a +
    formalDeriv T.support (T.maskB x) T.b

/-- An AB seed is compatible with a C-image profile when its target is divisible
by the profiled C-image generator. -/
def CProfileCompatible (T : ABCTriple) (P : T.CImageProfile) (x : T.FullTangent) : Prop :=
  P.gcd ∣ T.abTarget x

/-- A concrete C-lift for a given AB seed.

It preserves the A/B masks of the seed and adjusts the C side so that the
C-linear form realizes the AB target of the seed. -/
structure HasCLift (T : ABCTriple) (x lift : T.FullTangent) : Prop where
  maskA_eq : T.maskA lift = T.maskA x
  maskB_eq : T.maskB lift = T.maskB x
  c_balance : T.cLinearForm lift = T.abTarget x

/-- A C-lift preserves the AB target. -/
theorem abTarget_eq_of_HasCLift
    (T : ABCTriple) (x lift : T.FullTangent)
    (h : T.HasCLift x lift) :
    T.abTarget lift = T.abTarget x := by
  unfold ABCTriple.abTarget
  rw [h.maskA_eq, h.maskB_eq]

/-- A C-lift satisfies block balance. -/
theorem BlockBalance_of_HasCLift
    (T : ABCTriple) (x lift : T.FullTangent)
    (h : T.HasCLift x lift) :
    T.BlockBalance lift := by
  unfold ABCTriple.BlockBalance
  calc
    T.abTarget lift = T.abTarget x := T.abTarget_eq_of_HasCLift x lift h
    _ = T.cLinearForm lift := h.c_balance.symm

end ABCTriple
end ABD2
