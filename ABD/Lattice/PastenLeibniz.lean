import ABD.Differential.LeibnizSupport
import ABD.Lattice.PastenCandidate

namespace ABD

/-- A Pasten candidate inherits the Leibniz rule for `(a,b)` once the supported
Leibniz theorem has been proved on the triple support. -/
theorem PastenCandidate.leibniz_ab_of_supported {T : ABCTriple}
    (h : PastenCandidate T) (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.b :=
  H h.x T.a T.b T.leibnizSupport_ab

/-- Same bridge for `(a,c)`. -/
theorem PastenCandidate.leibniz_ac_of_supported {T : ABCTriple}
    (h : PastenCandidate T) (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.c :=
  H h.x T.a T.c T.leibnizSupport_ac

/-- Same bridge for `(b,c)`. -/
theorem PastenCandidate.leibniz_bc_of_supported {T : ABCTriple}
    (h : PastenCandidate T) (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.b T.c :=
  H h.x T.b T.c T.leibnizSupport_bc

/-- Coefficient-level theorem plus the coefficient bridge is enough to supply
`(a,b)` Leibniz for a Pasten candidate. -/
theorem PastenCandidate.leibniz_ab_of_coeff {T : ABCTriple}
    (h : PastenCandidate T)
    (Hcoeff : SupportedCoeffLeibnizTheorem T.support)
    (Hbridge : CoeffLeibnizBridge T.support) :
    LeibnizOn T.support h.x T.a T.b :=
  h.leibniz_ab_of_supported (supportedLeibnizTheorem_of_coeff Hcoeff Hbridge)

/-- Same coefficient bridge for `(a,c)`. -/
theorem PastenCandidate.leibniz_ac_of_coeff {T : ABCTriple}
    (h : PastenCandidate T)
    (Hcoeff : SupportedCoeffLeibnizTheorem T.support)
    (Hbridge : CoeffLeibnizBridge T.support) :
    LeibnizOn T.support h.x T.a T.c :=
  h.leibniz_ac_of_supported (supportedLeibnizTheorem_of_coeff Hcoeff Hbridge)

/-- Same coefficient bridge for `(b,c)`. -/
theorem PastenCandidate.leibniz_bc_of_coeff {T : ABCTriple}
    (h : PastenCandidate T)
    (Hcoeff : SupportedCoeffLeibnizTheorem T.support)
    (Hbridge : CoeffLeibnizBridge T.support) :
    LeibnizOn T.support h.x T.b T.c :=
  h.leibniz_bc_of_supported (supportedLeibnizTheorem_of_coeff Hcoeff Hbridge)

/-- A supported coefficient theorem is enough to supply `(a,b)` Leibniz for a
Pasten candidate, because the coefficient-to-sum bridge has now been theoremized. -/
theorem PastenCandidate.leibniz_ab_of_supportedCoeff {T : ABCTriple}
    (h : PastenCandidate T) (Hcoeff : SupportedCoeffLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.b :=
  h.leibniz_ab_of_supported (supportedLeibnizTheorem_of_supportedCoeff Hcoeff)

/-- Same supported-coefficient bridge for `(a,c)`. -/
theorem PastenCandidate.leibniz_ac_of_supportedCoeff {T : ABCTriple}
    (h : PastenCandidate T) (Hcoeff : SupportedCoeffLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.c :=
  h.leibniz_ac_of_supported (supportedLeibnizTheorem_of_supportedCoeff Hcoeff)

/-- Same supported-coefficient bridge for `(b,c)`. -/
theorem PastenCandidate.leibniz_bc_of_supportedCoeff {T : ABCTriple}
    (h : PastenCandidate T) (Hcoeff : SupportedCoeffLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.b T.c :=
  h.leibniz_bc_of_supported (supportedLeibnizTheorem_of_supportedCoeff Hcoeff)

/-- A Pasten candidate now obtains `(a,b)` Leibniz on its own triple support. -/
theorem PastenCandidate.leibniz_ab {T : ABCTriple}
    (h : PastenCandidate T) : LeibnizOn T.support h.x T.a T.b :=
  h.leibniz_ab_of_supported T.supportedLeibnizTheorem

/-- A Pasten candidate now obtains `(a,c)` Leibniz on its own triple support. -/
theorem PastenCandidate.leibniz_ac {T : ABCTriple}
    (h : PastenCandidate T) : LeibnizOn T.support h.x T.a T.c :=
  h.leibniz_ac_of_supported T.supportedLeibnizTheorem

/-- A Pasten candidate now obtains `(b,c)` Leibniz on its own triple support. -/
theorem PastenCandidate.leibniz_bc {T : ABCTriple}
    (h : PastenCandidate T) : LeibnizOn T.support h.x T.b T.c :=
  h.leibniz_bc_of_supported T.supportedLeibnizTheorem

/-- Small Pasten candidates inherit the same `(a,b)` Leibniz rule. -/
theorem SmallPastenCandidate.leibniz_ab {T : ABCTriple} {B : ℤ}
    (h : SmallPastenCandidate T B) : LeibnizOn T.support h.x T.a T.b :=
  (h.toPastenCandidate).leibniz_ab

/-- Small Pasten candidates inherit the same `(a,c)` Leibniz rule. -/
theorem SmallPastenCandidate.leibniz_ac {T : ABCTriple} {B : ℤ}
    (h : SmallPastenCandidate T B) : LeibnizOn T.support h.x T.a T.c :=
  (h.toPastenCandidate).leibniz_ac

/-- Small Pasten candidates inherit the same `(b,c)` Leibniz rule. -/
theorem SmallPastenCandidate.leibniz_bc {T : ABCTriple} {B : ℤ}
    (h : SmallPastenCandidate T B) : LeibnizOn T.support h.x T.b T.c :=
  (h.toPastenCandidate).leibniz_bc

end ABD
