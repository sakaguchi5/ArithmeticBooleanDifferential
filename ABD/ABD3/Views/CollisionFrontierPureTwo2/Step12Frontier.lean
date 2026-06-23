import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step11ExponentCoprimeGoal

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2

/-- Pure two-power desynchronized frontier in natural bottom-up form:
there is a pure normal form, the triple is radical-small, and the pure generators
have no accepted arithmetic edge. -/
def DesyncFrontier (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : NormalForm T P,
    T.RadicalSmall P ∧
      T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R

/-- Explicit desynchronized frontier: the radical-small predicate has been
expanded to `(2*p*q)^N < (2^w)^M`, while the no-accepted-edge predicate is kept. -/
def ExplicitDesyncFrontier (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : NormalForm T P,
    F.ExplicitRadicalSmall ∧
      T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R

/-- Explicit three-rejection frontier: the concrete normal form supplied by
Steps 8--9.  Radical-smallness is explicit, and no accepted arithmetic edge has
been replaced by the three rejections `A-B`, `A-C₂`, and `B-C₂`. -/
def ExplicitThreeRejectionFrontier (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : NormalForm T P,
    F.ExplicitRadicalSmall ∧ F.ThreeRejections R

/-- Strengthened frontier with the elementary parity/mod-8 package. -/
def ExplicitThreeRejectionElementaryFrontier
    (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : NormalForm T P,
    F.ExplicitRadicalSmall ∧ F.ThreeRejections R ∧ F.ElementaryConstraintsGoal

/-- Final strengthened frontier with both the elementary parity/mod-8 package and
exponent coprimality.  This is the endpoint of Steps 8--12 after the localized
arithmetic `sorry`s in Steps 10--11 are accepted. -/
def ExplicitThreeRejectionHardElementaryFrontier
    (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : NormalForm T P,
    F.ExplicitRadicalSmall ∧ F.ThreeRejections R ∧ NormalForm.HardElementaryGoals F

/-- Radical-small expansion at the frontier level. -/
theorem desyncFrontier_iff_explicit
    (T : ABCData) (P : PowerData) (R : ℕ) :
    DesyncFrontier T P R ↔ ExplicitDesyncFrontier T P R := by
  constructor
  · intro hfrontier
    rcases hfrontier with ⟨F, hsmall, hno⟩
    exact ⟨F, F.explicitRadicalSmall_of_radicalSmall hsmall, hno⟩
  · intro hfrontier
    rcases hfrontier with ⟨F, hsmall, hno⟩
    exact ⟨F, F.radicalSmall_of_explicitRadicalSmall hsmall, hno⟩

/-- Main Step 12 bridge.  The old C-surplus input is gone: Step 8 proves
`CSurplusPorts = {2}` from radical-smallness, and Step 9 converts the abstract
no-accepted-edge predicate into the three concrete rejections. -/
theorem explicitThreeRejectionFrontier_of_desyncFrontier
    (T : ABCData) (P : PowerData) (R : ℕ) :
    DesyncFrontier T P R → ExplicitThreeRejectionFrontier T P R := by
  intro hfrontier
  rcases hfrontier with ⟨F, hsmall, hno⟩
  have hthree : F.ThreeRejections R :=
    F.threeRejections_of_noAcceptedArithmeticEdge_of_radicalSmall R hsmall hno
  exact ⟨F, F.explicitRadicalSmall_of_radicalSmall hsmall, hthree⟩

/-- The elementary layer is now theorem-supplied by Step 10, so the elementary
frontier no longer needs an external `Helem` argument. -/
theorem explicitThreeRejectionElementaryFrontier_of_desyncFrontier
    (T : ABCData) (P : PowerData) (R : ℕ) :
    DesyncFrontier T P R → ExplicitThreeRejectionElementaryFrontier T P R := by
  intro hfrontier
  rcases explicitThreeRejectionFrontier_of_desyncFrontier
      (T := T) (P := P) (R := R) hfrontier with
    ⟨F, hsmall, hthree⟩
  exact ⟨F, hsmall, hthree, NormalForm.elementaryConstraintsGoal F⟩

/-- Final Step 12 bridge with both elementary constraints and exponent
coprimality.  The only remaining debt is the localized arithmetic `sorry`s in
Steps 10--11, not the ABD3 frontier plumbing. -/
theorem explicitThreeRejectionHardElementaryFrontier_of_desyncFrontier
    (T : ABCData) (P : PowerData) (R : ℕ) :
    DesyncFrontier T P R → ExplicitThreeRejectionHardElementaryFrontier T P R := by
  intro hfrontier
  rcases explicitThreeRejectionFrontier_of_desyncFrontier
      (T := T) (P := P) (R := R) hfrontier with
    ⟨F, hsmall, hthree⟩
  exact ⟨F, hsmall, hthree, NormalForm.hardElementaryGoals F⟩

end CollisionFrontierPureTwo2
end ABCData
end ABD3
