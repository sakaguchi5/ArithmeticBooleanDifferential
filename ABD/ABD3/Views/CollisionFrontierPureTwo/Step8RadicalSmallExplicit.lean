import ABD.ABD3.Views.CollisionFrontierPureTwo.Step7CoeffScaleFactoryReal

namespace ABD3
namespace ABCData
namespace PureTwoPowerNormalForm

variable {T : ABCData} {P : PowerData}

/-- The explicit radical-small inequality expected in the pure two-power model.

Mathematically this is

  `(2*p*q)^N < (2^w)^M`,

because the model has `A = p^u`, `B = q^v`, and `C = 2^w`, so the radical
for the triple should be `2*p*q`.  The actual radical computation is isolated in
`PureRadicalFacts` below. -/
def ExplicitRadicalSmall (F : PureTwoPowerNormalForm T P) : Prop :=
  (((2 * F.p * F.q : ℕ) : ℤ) ^ P.N) < (((2 ^ F.w : ℕ) : ℤ) ^ P.M)

/-- Step 8 local radical facts for the pure two-power model.

This package isolates the support/radical reconstruction part.  Once one proves
`radABC = 2*p*q` from `supportA={p}`, `supportB={q}`, and `supportC={2}`, the
bidirectional radical-small specialization below becomes unconditional. -/
structure PureRadicalFacts (F : PureTwoPowerNormalForm T P) where
  hradABC : T.radABC = 2 * F.p * F.q

/-- Proposition form for future real radical computation. -/
def HasPureRadicalFacts (F : PureTwoPowerNormalForm T P) : Prop :=
  Nonempty (PureRadicalFacts F)

/-- Step 8 core theorem: under the pure radical facts, ABD3 `RadicalSmall` is
exactly the explicit inequality `(2*p*q)^N < (2^w)^M`.

This is intentionally bidirectional.  The only remaining arithmetic input is the
radical reconstruction fact `radABC = 2*p*q`. -/
theorem radicalSmall_iff_explicit_of_radicalFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureRadicalFacts F) :
    T.RadicalSmall P ↔ F.ExplicitRadicalSmall := by
  unfold RadicalSmall RadicalSmallInt ExplicitRadicalSmall
  rw [H.hradABC, F.C_eq_two_pow]

/-- Forward direction of the Step 8 specialization. -/
theorem explicitRadicalSmall_of_radicalSmall_of_radicalFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureRadicalFacts F)
    (hsmall : T.RadicalSmall P) :
    F.ExplicitRadicalSmall :=
  (F.radicalSmall_iff_explicit_of_radicalFacts H).mp hsmall

/-- Reverse direction of the Step 8 specialization. -/
theorem radicalSmall_of_explicitRadicalSmall_of_radicalFacts
    (F : PureTwoPowerNormalForm T P)
    (H : PureRadicalFacts F)
    (hsmall : F.ExplicitRadicalSmall) :
    T.RadicalSmall P :=
  (F.radicalSmall_iff_explicit_of_radicalFacts H).mpr hsmall

end PureTwoPowerNormalForm

/-- Explicit version of the pure two-power desynchronized frontier:
`RadicalSmall` has been replaced by `(2*p*q)^N < (2^w)^M`. -/
def PureTwoPowerExplicitDesyncFrontier
    (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : PureTwoPowerNormalForm T P,
    F.ExplicitRadicalSmall ∧
      T.NoAcceptedArithmeticEdge P F.pureSyncGenerators R

/-- Explicit version of the pure two-power three-rejection frontier:
`RadicalSmall` has been replaced by `(2*p*q)^N < (2^w)^M`. -/
def PureTwoPowerExplicitThreeRejectionFrontier
    (T : ABCData) (P : PowerData) (R : ℕ) : Prop :=
  ∃ F : PureTwoPowerNormalForm T P,
    F.ExplicitRadicalSmall ∧ F.ThreeRejections R

/-- Bidirectional frontier-level specialization for the desynchronized frontier.

After providing radical facts for every pure normal form, the old frontier and
the explicit `(2*p*q)^N < (2^w)^M` frontier are equivalent. -/
theorem pureTwoPowerDesyncFrontier_iff_explicit_of_radicalFacts
    (T : ABCData) (P : PowerData) (R : ℕ)
    (H : ∀ F : PureTwoPowerNormalForm T P, F.PureRadicalFacts) :
    T.PureTwoPowerDesyncFrontier P R ↔
      T.PureTwoPowerExplicitDesyncFrontier P R := by
  constructor
  · intro hfrontier
    rcases hfrontier with ⟨F, hsmall, hno⟩
    exact ⟨F, F.explicitRadicalSmall_of_radicalSmall_of_radicalFacts (H F) hsmall, hno⟩
  · intro hfrontier
    rcases hfrontier with ⟨F, hsmall, hno⟩
    exact ⟨F, F.radicalSmall_of_explicitRadicalSmall_of_radicalFacts (H F) hsmall, hno⟩

/-- Bidirectional frontier-level specialization for the three-rejection frontier.

This is the clean Step 8 target after Step 7: the dangerous pure two-power
three-rejection frontier is exactly the explicit inequality plus the three
gcd/lcm rejections. -/
theorem pureTwoPowerThreeRejectionFrontier_iff_explicit_of_radicalFacts
    (T : ABCData) (P : PowerData) (R : ℕ)
    (H : ∀ F : PureTwoPowerNormalForm T P, F.PureRadicalFacts) :
    T.PureTwoPowerThreeRejectionFrontier P R ↔
      T.PureTwoPowerExplicitThreeRejectionFrontier P R := by
  constructor
  · intro hfrontier
    rcases hfrontier with ⟨F, hsmall, hthree⟩
    exact ⟨F, F.explicitRadicalSmall_of_radicalSmall_of_radicalFacts (H F) hsmall, hthree⟩
  · intro hfrontier
    rcases hfrontier with ⟨F, hsmall, hthree⟩
    exact ⟨F, F.radicalSmall_of_explicitRadicalSmall_of_radicalFacts (H F) hsmall, hthree⟩

/-- Combine Step 7 and Step 8: a pure desynchronized frontier reduces to the
explicit inequality plus the three concrete rejections, assuming singleton C-port
and pure radical reconstruction. -/
theorem explicitThreeRejectionFrontier_of_desyncFrontier_of_radicalFacts
    (T : ABCData) (P : PowerData) (R : ℕ)
    (hports : T.CSurplusPorts P = {2})
    (H : ∀ F : PureTwoPowerNormalForm T P, F.PureRadicalFacts) :
    T.PureTwoPowerDesyncFrontier P R →
      T.PureTwoPowerExplicitThreeRejectionFrontier P R := by
  intro hfrontier
  have hthree : T.PureTwoPowerThreeRejectionFrontier P R :=
    T.threeRejectionFrontier_of_desyncFrontier_real P R hports hfrontier
  exact (T.pureTwoPowerThreeRejectionFrontier_iff_explicit_of_radicalFacts P R H).mp hthree

/-- A named future goal: realize the pure radical facts from the support
normal form alone.  This is the remaining support/radical reconstruction step
behind the unconditional Step 8 equivalence. -/
def PureRadicalFactsRealGoal (T : ABCData) (P : PowerData) : Prop :=
  ∀ F : PureTwoPowerNormalForm T P, F.PureRadicalFacts

end ABCData
end ABD3
