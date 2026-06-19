import ABD.ABD2.Fibration.Qualitative
import ABD.ABD2.Fibration.SmallLift

namespace ABD2
namespace ABCTriple

/-- A fixed seed has C-lift cost at most `B` when its C-fiber contains a
coordinate-small point with bound `B`.

This is just a named cost-style alias for `HasSmallFiberOver`.  Later phases can
replace the coordinate gauge or strengthen the bound without changing the
fibration routing statements below. -/
def SeedLiftCostAtMost
    (T : ABCTriple) (seed : T.FullTangent) (B : ℤ) : Prop :=
  T.HasSmallFiberOver seed B

@[simp]
theorem seedLiftCostAtMost_iff_hasSmallFiberOver
    (T : ABCTriple) (seed : T.FullTangent) (B : ℤ) :
    T.SeedLiftCostAtMost seed B ↔ T.HasSmallFiberOver seed B := by
  rfl

/-- A fixed seed has some finite C-lift bound if it has a small fiber point for
some integer bound `B`.

This intentionally forgets the quality of the bound.  The point of Phase 5 is to
separate finite existence from later power-saving estimates. -/
def HasFiniteSmallFiberOver
    (T : ABCTriple) (seed : T.FullTangent) : Prop :=
  ∃ B : ℤ, T.HasSmallFiberOver seed B

/-- A profile has a finite small section if some bound `B` works over some good
base point. -/
def HasFiniteSmallSection
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∃ B : ℤ, T.SmallSectionExists P B

@[simp]
theorem hasFiniteSmallSection_iff_exists_smallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasFiniteSmallSection P ↔ ∃ B : ℤ, T.SmallSectionExists P B := by
  rfl

/-- A small section at a concrete bound is, in particular, a finite small
section. -/
theorem hasFiniteSmallSection_of_smallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.SmallSectionExists P B) :
    T.HasFiniteSmallSection P := by
  exact ⟨B, h⟩

/-- Fixed-bound small block lifts are equivalent to fixed-bound small sections,
so their finite versions are equivalent as well. -/
theorem hasFiniteSmallSection_iff_exists_hasSmallBlockLift
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasFiniteSmallSection P ↔ ∃ B : ℤ, T.HasSmallBlockLift P B := by
  constructor
  · intro h
    rcases h with ⟨B, hsection⟩
    exact ⟨B, (T.smallSectionExists_iff_hasSmallBlockLift P).1 hsection⟩
  · intro h
    rcases h with ⟨B, hblock⟩
    exact ⟨B, (T.smallSectionExists_iff_hasSmallBlockLift P).2 hblock⟩

/-- A small block lift at a concrete bound gives a finite small section. -/
theorem hasFiniteSmallSection_of_hasSmallBlockLift
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.HasSmallBlockLift P B) :
    T.HasFiniteSmallSection P := by
  exact (T.hasFiniteSmallSection_iff_exists_hasSmallBlockLift P).2 ⟨B, h⟩

/-- Finite small section, expanded as: there is a good base point whose fiber has
some finite small point. -/
theorem hasFiniteSmallSection_iff_exists_goodBasePoint_and_finiteSmallFiber
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasFiniteSmallSection P ↔
      ∃ seed : T.FullTangent,
        T.GoodBasePoint P seed ∧ T.HasFiniteSmallFiberOver seed := by
  constructor
  · intro h
    rcases h with ⟨B, seed, hgood, hfiber⟩
    exact ⟨seed, hgood, ⟨B, hfiber⟩⟩
  · intro h
    rcases h with ⟨seed, hgood, B, hfiber⟩
    exact ⟨B, seed, hgood, hfiber⟩

/-- Existence of a strict candidate satisfying some finite coordinate bound. -/
def HasFiniteSmallStrictCandidate (T : ABCTriple) : Prop :=
  ∃ B : ℤ, ∃ x : T.FullTangent,
    T.StrictCandidate x ∧ T.SmallTangent x B

/-- A finite small section produces a finite small strict candidate. -/
theorem hasFiniteSmallStrictCandidate_of_hasFiniteSmallSection
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasFiniteSmallSection P) :
    T.HasFiniteSmallStrictCandidate := by
  rcases h with ⟨B, hsection⟩
  exact ⟨B, T.hasSmallStrictCandidate_of_smallSectionExists P hsection⟩

/-- Concrete-bound version of the finite small strict-candidate routing. -/
theorem hasFiniteSmallStrictCandidate_of_smallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.SmallSectionExists P B) :
    T.HasFiniteSmallStrictCandidate := by
  exact T.hasFiniteSmallStrictCandidate_of_hasFiniteSmallSection P
    (T.hasFiniteSmallSection_of_smallSectionExists P h)

/-- Forgetting the finite bound, a finite small strict candidate is a strict
candidate. -/
theorem hasStrictCandidate_of_hasFiniteSmallStrictCandidate
    (T : ABCTriple)
    (h : T.HasFiniteSmallStrictCandidate) :
    T.HasStrictCandidate := by
  rcases h with ⟨_B, x, hstrict, _hsmall⟩
  exact ⟨x, hstrict⟩

/-- A finite small section also gives an ordinary strict candidate. -/
theorem hasStrictCandidate_of_hasFiniteSmallSection
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasFiniteSmallSection P) :
    T.HasStrictCandidate := by
  exact T.hasStrictCandidate_of_hasFiniteSmallStrictCandidate
    (T.hasFiniteSmallStrictCandidate_of_hasFiniteSmallSection P h)

namespace RealizedCImageProfile

/-- Realized-profile wrapper: a finite small section routes to a finite small
strict candidate. -/
theorem hasFiniteSmallStrictCandidate_of_hasFiniteSmallSection
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (h : T.HasFiniteSmallSection R.profile) :
    T.HasFiniteSmallStrictCandidate := by
  exact T.hasFiniteSmallStrictCandidate_of_hasFiniteSmallSection R.profile h

/-- Realized-profile wrapper: a finite small section routes to an ordinary strict
candidate after forgetting the bound. -/
theorem hasStrictCandidate_of_hasFiniteSmallSection
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (h : T.HasFiniteSmallSection R.profile) :
    T.HasStrictCandidate := by
  exact T.hasStrictCandidate_of_hasFiniteSmallSection R.profile h

end RealizedCImageProfile

end ABCTriple
end ABD2
