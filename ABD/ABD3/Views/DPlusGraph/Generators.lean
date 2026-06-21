import ABD.ABD3.Views.DPlusGraph.Absorption

namespace ABD3

namespace ABCData

/-- Natural absolute value of the A-side coefficient scale. -/
def coeffAbsA (T : ABCData) (p : ℕ) : ℕ :=
  Int.natAbs (T.coeffA p)

/-- Natural absolute value of the B-side coefficient scale. -/
def coeffAbsB (T : ABCData) (p : ℕ) : ℕ :=
  Int.natAbs (T.coeffB p)

/-- Natural absolute value of the C-side coefficient scale.  This is definitionally
compatible with the graph-side C-port scale introduced earlier. -/
def coeffAbsC (T : ABCData) (p : ℕ) : ℕ :=
  Int.natAbs (T.coeffC p)

@[simp] theorem coeffAbsC_eq_cPortCoeffNat
    (T : ABCData) (p : ℕ) :
    T.coeffAbsC p = T.CPortCoeffNat p := rfl

/-- Abstract certificate that `gA` and `gB` are the coefficient-image generators
for the A/B scalar sides.

The current D+ graph layer should not import ABD2.  Instead of pretending that an
implementation-specific gcd construction is canonical, we package the facts that
will be needed by the arithmetic graph argument: each side has a generator and
that generator divides all corresponding coefficient scales on its support. -/
structure CoeffGCDGenerators (T : ABCData) where
  gA : ℕ
  gB : ℕ
  gA_dvd_coeffA : ∀ ⦃p : ℕ⦄, p ∈ T.supportA → gA ∣ T.coeffAbsA p
  gB_dvd_coeffB : ∀ ⦃p : ℕ⦄, p ∈ T.supportB → gB ∣ T.coeffAbsB p

/-- Forget the coefficient-gcd certificate down to the two arithmetic sync
generators used by the ABD3 graph. -/
def arithmeticSyncGeneratorsOfCoeffGCD
    (T : ABCData) (H : T.CoeffGCDGenerators) : ArithmeticSyncGenerators :=
  { gA := H.gA, gB := H.gB }

@[simp] theorem arithmeticSyncGeneratorsOfCoeffGCD_gA
    (T : ABCData) (H : T.CoeffGCDGenerators) :
    (T.arithmeticSyncGeneratorsOfCoeffGCD H).gA = H.gA := rfl

@[simp] theorem arithmeticSyncGeneratorsOfCoeffGCD_gB
    (T : ABCData) (H : T.CoeffGCDGenerators) :
    (T.arithmeticSyncGeneratorsOfCoeffGCD H).gB = H.gB := rfl

/-- A named proposition for the future concrete gcd construction. -/
def HasCoeffGCDGenerators (T : ABCData) : Prop :=
  Nonempty (CoeffGCDGenerators T)

/-- Coefficient-gcd data immediately gives arithmetic sync generators. -/
theorem hasArithmeticSyncGenerators_of_hasCoeffGCDGenerators
    (T : ABCData) :
    T.HasCoeffGCDGenerators → Nonempty ArithmeticSyncGenerators := by
  rintro ⟨H⟩
  exact ⟨T.arithmeticSyncGeneratorsOfCoeffGCD H⟩

end ABCData

end ABD3
