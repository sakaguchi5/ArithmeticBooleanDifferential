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

/-- Explicit three-rejection frontier: the final concrete normal form for the
pure two-power branch. -/
def ExplicitThreeRejectionFrontier (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : NormalForm T P,
    F.ExplicitRadicalSmall ∧ F.ThreeRejections R

/-- Optional strengthened final frontier, adding the elementary-number-theory
constraints once those goals are realized. -/
def ExplicitThreeRejectionElementaryFrontier
    (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : NormalForm T P,
    F.ExplicitRadicalSmall ∧ F.ThreeRejections R ∧ F.ElementaryConstraintsGoal

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

/-- The remaining local C-surplus realization goal for the whole pure-two folder:
radical-smallness makes `2` a positive C-surplus port.
Once this is proved, the final bridge below becomes unconditional. -/
def CSurplusSingletonRealGoal (T : ABCData) (P : PowerData) : Prop :=
  NormalForm.TwoMemCSurplusGoal (T := T) (P := P)

/-- Final bottom-up bridge: assuming only the isolated local C-surplus extraction
`2 ∈ CSurplusPorts` from radical-smallness, the pure desynchronized frontier is
converted to the explicit inequality plus the three concrete gcd/lcm rejections.

All support, radical, and coefficient factories from the exploratory folder have
been eliminated before this point. -/
theorem explicitThreeRejectionFrontier_of_desyncFrontier
    (T : ABCData) (P : PowerData) (R : ℕ)
    (Hports : CSurplusSingletonRealGoal T P) :
    DesyncFrontier T P R → ExplicitThreeRejectionFrontier T P R := by
  intro hfrontier
  rcases hfrontier with ⟨F, hsmall, hno⟩
  have hthree : F.ThreeRejections R :=
    (F.noAcceptedArithmeticEdge_iff_threeRejections_of_radicalSmall R Hports hsmall).mp hno
  exact ⟨F, F.explicitRadicalSmall_of_radicalSmall hsmall, hthree⟩

/-- If the elementary layer is also realized, the final frontier can be enriched
with the mod-8/parity package. -/
theorem explicitThreeRejectionElementaryFrontier_of_desyncFrontier
    (T : ABCData) (P : PowerData) (R : ℕ)
    (Hports : CSurplusSingletonRealGoal T P)
    (Helem : ∀ F : NormalForm T P, F.ElementaryConstraintsGoal) :
    DesyncFrontier T P R → ExplicitThreeRejectionElementaryFrontier T P R := by
  intro hfrontier
  rcases explicitThreeRejectionFrontier_of_desyncFrontier
      (T := T) (P := P) (R := R) Hports hfrontier with
    ⟨F, hsmall, hthree⟩
  exact ⟨F, hsmall, hthree, Helem F⟩

end CollisionFrontierPureTwo2
end ABCData
end ABD3
