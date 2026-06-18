import ABD.ABD.Core.SupportLemmas
import ABD.ABD.Differential.TripleCandidate
import ABD.ABD.Differential.LeibnizCoeff
import ABD.ABD.Differential.DerivCoeffLocal

namespace ABD

/-- Support hypotheses under which the Leibniz rule is meant to be applied.

The full arithmetic theorem is intentionally separated from the support shape.
This predicate only isolates the exact support coverage assumptions consumed by
the supported Leibniz theorem. -/
def LeibnizSupport (S : Finset ℕ) (m n : ℕ) : Prop :=
  Supports S m ∧ Supports S n

/-- `formalDeriv` satisfies Leibniz on all inputs supported by `S`. -/
def SupportedLeibnizTheorem (S : Finset ℕ) : Prop :=
  ∀ (x : Tangent S) (m n : ℕ), LeibnizSupport S m n → LeibnizOn S x m n

/-- Coefficient-level version of the supported Leibniz theorem. -/
def SupportedCoeffLeibnizTheorem (S : Finset ℕ) : Prop :=
  ∀ m n : ℕ, LeibnizSupport S m n → DerivCoeffLeibnizOn S m n

/-- Build a Leibniz support hypothesis from the two component support facts. -/
theorem leibnizSupport_of_supports {S : Finset ℕ} {m n : ℕ}
    (hm : Supports S m) (hn : Supports S n) : LeibnizSupport S m n :=
  ⟨hm, hn⟩

/-- The left input of a supported Leibniz pair is supported. -/
theorem LeibnizSupport.left {S : Finset ℕ} {m n : ℕ}
    (h : LeibnizSupport S m n) : Supports S m :=
  h.1

/-- The right input of a supported Leibniz pair is supported. -/
theorem LeibnizSupport.right {S : Finset ℕ} {m n : ℕ}
    (h : LeibnizSupport S m n) : Supports S n :=
  h.2

/-- The zero tangent satisfies the supported Leibniz target. -/
theorem zeroTangent_supportedLeibniz (S : Finset ℕ) :
    ∀ m n : ℕ, LeibnizSupport S m n → LeibnizOn S (zeroTangent S) m n := by
  intro m n _
  simp

/-- A coefficient-level theorem plus the formal coefficient bridge yields the
supported Leibniz theorem. -/
theorem supportedLeibnizTheorem_of_coeff {S : Finset ℕ}
    (Hcoeff : SupportedCoeffLeibnizTheorem S)
    (Hbridge : CoeffLeibnizBridge S) : SupportedLeibnizTheorem S := by
  intro x m n hmn
  exact Hbridge x m n (Hcoeff m n hmn)

/-- A coefficient-level theorem yields the supported Leibniz theorem, using the
theoremized coefficient-to-sum bridge. -/
theorem supportedLeibnizTheorem_of_supportedCoeff {S : Finset ℕ}
    (Hcoeff : SupportedCoeffLeibnizTheorem S) : SupportedLeibnizTheorem S :=
  supportedLeibnizTheorem_of_coeff Hcoeff (coeffLeibnizBridge S)

/-- Prime-shaped supports satisfy the supported coefficient theorem. -/
theorem supportedCoeffLeibnizTheorem_of_primeSupport
    {S : Finset ℕ} (hS : PrimeSupport S) :
    SupportedCoeffLeibnizTheorem S := by
  intro m n _
  exact derivCoeffLeibnizOn_of_primeSupport hS m n

/-- Prime-shaped supports satisfy the supported Leibniz theorem. -/
theorem supportedLeibnizTheorem_of_primeSupport
    {S : Finset ℕ} (hS : PrimeSupport S) : SupportedLeibnizTheorem S :=
  supportedLeibnizTheorem_of_supportedCoeff
    (supportedCoeffLeibnizTheorem_of_primeSupport hS)

/-- In an additive triple, the pair `(a,b)` is supported by the triple support. -/
theorem ABCTriple.leibnizSupport_ab (T : ABCTriple) :
    LeibnizSupport T.support T.a T.b :=
  leibnizSupport_of_supports T.supports_a T.supports_b

/-- In an additive triple, the pair `(a,c)` is supported by the triple support. -/
theorem ABCTriple.leibnizSupport_ac (T : ABCTriple) :
    LeibnizSupport T.support T.a T.c :=
  leibnizSupport_of_supports T.supports_a T.supports_c

/-- In an additive triple, the pair `(b,c)` is supported by the triple support. -/
theorem ABCTriple.leibnizSupport_bc (T : ABCTriple) :
    LeibnizSupport T.support T.b T.c :=
  leibnizSupport_of_supports T.supports_b T.supports_c

/-- The triple support satisfies the supported coefficient theorem. -/
theorem ABCTriple.supportedCoeffLeibnizTheorem (T : ABCTriple) :
    SupportedCoeffLeibnizTheorem T.support :=
  supportedCoeffLeibnizTheorem_of_primeSupport T.hasPrimeSupport

/-- The triple support satisfies the supported Leibniz theorem. -/
theorem ABCTriple.supportedLeibnizTheorem (T : ABCTriple) :
    SupportedLeibnizTheorem T.support :=
  supportedLeibnizTheorem_of_supportedCoeff T.supportedCoeffLeibnizTheorem

/-- Once the supported Leibniz theorem is proved for the triple support, every
triple-level differential candidate obtains the Leibniz rule for `(a,b)`. -/
theorem DifferentialCandidate.leibniz_ab_of_supported {T : ABCTriple}
    (h : DifferentialCandidate T) (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.b :=
  H h.x T.a T.b T.leibnizSupport_ab

/-- Same bridge for `(a,c)`. -/
theorem DifferentialCandidate.leibniz_ac_of_supported {T : ABCTriple}
    (h : DifferentialCandidate T) (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.c :=
  H h.x T.a T.c T.leibnizSupport_ac

/-- Same bridge for `(b,c)`. -/
theorem DifferentialCandidate.leibniz_bc_of_supported {T : ABCTriple}
    (h : DifferentialCandidate T) (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.b T.c :=
  H h.x T.b T.c T.leibnizSupport_bc

/-- A supported coefficient theorem is enough to get `(a,b)` Leibniz for a
triple-level differential candidate. -/
theorem DifferentialCandidate.leibniz_ab_of_supportedCoeff {T : ABCTriple}
    (h : DifferentialCandidate T) (Hcoeff : SupportedCoeffLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.b :=
  h.leibniz_ab_of_supported (supportedLeibnizTheorem_of_supportedCoeff Hcoeff)

/-- Same supported-coefficient bridge for `(a,c)`. -/
theorem DifferentialCandidate.leibniz_ac_of_supportedCoeff {T : ABCTriple}
    (h : DifferentialCandidate T) (Hcoeff : SupportedCoeffLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.c :=
  h.leibniz_ac_of_supported (supportedLeibnizTheorem_of_supportedCoeff Hcoeff)

/-- Same supported-coefficient bridge for `(b,c)`. -/
theorem DifferentialCandidate.leibniz_bc_of_supportedCoeff {T : ABCTriple}
    (h : DifferentialCandidate T) (Hcoeff : SupportedCoeffLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.b T.c :=
  h.leibniz_bc_of_supported (supportedLeibnizTheorem_of_supportedCoeff Hcoeff)

/-- A differential candidate obtains `(a,b)` Leibniz on its own triple support. -/
theorem DifferentialCandidate.leibniz_ab {T : ABCTriple}
    (h : DifferentialCandidate T) : LeibnizOn T.support h.x T.a T.b :=
  h.leibniz_ab_of_supported T.supportedLeibnizTheorem

/-- A differential candidate obtains `(a,c)` Leibniz on its own triple support. -/
theorem DifferentialCandidate.leibniz_ac {T : ABCTriple}
    (h : DifferentialCandidate T) : LeibnizOn T.support h.x T.a T.c :=
  h.leibniz_ac_of_supported T.supportedLeibnizTheorem

/-- A differential candidate obtains `(b,c)` Leibniz on its own triple support. -/
theorem DifferentialCandidate.leibniz_bc {T : ABCTriple}
    (h : DifferentialCandidate T) : LeibnizOn T.support h.x T.b T.c :=
  h.leibniz_bc_of_supported T.supportedLeibnizTheorem

end ABD
