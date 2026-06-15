import ABD.Differential.LeibnizSupport
import ABD.Lattice.PastenCandidate

namespace ABD

/-- A Pasten candidate inherits the Leibniz rule for `(a,b)` once the supported
Leibniz theorem has been proved on the triple support. -/
theorem PastenCandidate.leibniz_ab_of_supported
    {T : ABCTriple} (h : PastenCandidate T)
    (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.b :=
  H h.x T.a T.b T.leibnizSupport_ab

/-- Same bridge for `(a,c)`. -/
theorem PastenCandidate.leibniz_ac_of_supported
    {T : ABCTriple} (h : PastenCandidate T)
    (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.c :=
  H h.x T.a T.c T.leibnizSupport_ac

/-- Same bridge for `(b,c)`. -/
theorem PastenCandidate.leibniz_bc_of_supported
    {T : ABCTriple} (h : PastenCandidate T)
    (H : SupportedLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.b T.c :=
  H h.x T.b T.c T.leibnizSupport_bc

/-- Coefficient-level theorem plus the coefficient bridge is enough to supply
`(a,b)` Leibniz for a Pasten candidate. -/
theorem PastenCandidate.leibniz_ab_of_coeff
    {T : ABCTriple} (h : PastenCandidate T)
    (Hcoeff : SupportedCoeffLeibnizTheorem T.support)
    (Hbridge : CoeffLeibnizBridge T.support) :
    LeibnizOn T.support h.x T.a T.b :=
  h.leibniz_ab_of_supported (supportedLeibnizTheorem_of_coeff Hcoeff Hbridge)

/-- Same coefficient bridge for `(a,c)`. -/
theorem PastenCandidate.leibniz_ac_of_coeff
    {T : ABCTriple} (h : PastenCandidate T)
    (Hcoeff : SupportedCoeffLeibnizTheorem T.support)
    (Hbridge : CoeffLeibnizBridge T.support) :
    LeibnizOn T.support h.x T.a T.c :=
  h.leibniz_ac_of_supported (supportedLeibnizTheorem_of_coeff Hcoeff Hbridge)

/-- Same coefficient bridge for `(b,c)`. -/
theorem PastenCandidate.leibniz_bc_of_coeff
    {T : ABCTriple} (h : PastenCandidate T)
    (Hcoeff : SupportedCoeffLeibnizTheorem T.support)
    (Hbridge : CoeffLeibnizBridge T.support) :
    LeibnizOn T.support h.x T.b T.c :=
  h.leibniz_bc_of_supported (supportedLeibnizTheorem_of_coeff Hcoeff Hbridge)

/-- A supported coefficient theorem is enough to supply `(a,b)` Leibniz for a
Pasten candidate, because the coefficient-to-sum bridge has now been
theoremized. -/
theorem PastenCandidate.leibniz_ab_of_supportedCoeff
    {T : ABCTriple} (h : PastenCandidate T)
    (Hcoeff : SupportedCoeffLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.b :=
  h.leibniz_ab_of_supported (supportedLeibnizTheorem_of_supportedCoeff Hcoeff)

/-- Same supported-coefficient bridge for `(a,c)`. -/
theorem PastenCandidate.leibniz_ac_of_supportedCoeff
    {T : ABCTriple} (h : PastenCandidate T)
    (Hcoeff : SupportedCoeffLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.a T.c :=
  h.leibniz_ac_of_supported (supportedLeibnizTheorem_of_supportedCoeff Hcoeff)

/-- Same supported-coefficient bridge for `(b,c)`. -/
theorem PastenCandidate.leibniz_bc_of_supportedCoeff
    {T : ABCTriple} (h : PastenCandidate T)
    (Hcoeff : SupportedCoeffLeibnizTheorem T.support) :
    LeibnizOn T.support h.x T.b T.c :=
  h.leibniz_bc_of_supported (supportedLeibnizTheorem_of_supportedCoeff Hcoeff)

end ABD
