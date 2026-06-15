import ABD.Core.SupportLemmas
import ABD.Differential.TripleCandidate

namespace ABD

/-- Support hypotheses under which the Leibniz rule is meant to be applied.

The full arithmetic theorem is intentionally not asserted here.  This file
only isolates the exact support coverage assumptions that the later proof of
`formalDeriv`'s Leibniz rule should consume.
-/
def LeibnizSupport (S : Finset ℕ) (m n : ℕ) : Prop :=
  Supports S m ∧ Supports S n

/-- Future target: `formalDeriv` satisfies Leibniz on all inputs supported by
`S`.  Keeping this as a named proposition lets higher layers depend on the
shape of the theorem without pretending that the hard arithmetic proof is done.
-/
def SupportedLeibnizTheorem (S : Finset ℕ) : Prop :=
  ∀ (x : Tangent S) (m n : ℕ),
    LeibnizSupport S m n → LeibnizOn S x m n

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

/-- Once the supported Leibniz theorem is proved for the triple support, every
triple-level differential candidate obtains the Leibniz rule for `(a,b)`.
-/
theorem DifferentialCandidate.leibniz_ab_of_supported
    {T : ABCTriple} (h : DifferentialCandidate T)
    (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.b :=
  H h.x T.a T.b T.leibnizSupport_ab

/-- Same bridge for `(a,c)`. -/
theorem DifferentialCandidate.leibniz_ac_of_supported
    {T : ABCTriple} (h : DifferentialCandidate T)
    (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.c :=
  H h.x T.a T.c T.leibnizSupport_ac

/-- Same bridge for `(b,c)`. -/
theorem DifferentialCandidate.leibniz_bc_of_supported
    {T : ABCTriple} (h : DifferentialCandidate T)
    (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.b T.c :=
  H h.x T.b T.c T.leibnizSupport_bc

end ABD
