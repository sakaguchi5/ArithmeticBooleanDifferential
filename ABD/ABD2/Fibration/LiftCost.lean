import ABD.ABD2.Fibration.FiniteBound

namespace ABD2
namespace ABCTriple

/-- A C-lift cost bound for a fixed seed.

`CLiftCostAtMost seed B` means that the C-fiber over `seed` contains a
coordinate-small lift with bound `B`.  This is a cost-style name for the same
fixed-bound fiber condition introduced earlier; later phases can replace this
with sharper estimates without changing the fibration routing layer. -/
def CLiftCostAtMost
    (T : ABCTriple) (seed : T.FullTangent) (B : ℤ) : Prop :=
  T.HasSmallFiberOver seed B

@[simp]
theorem cLiftCostAtMost_iff_hasSmallFiberOver
    (T : ABCTriple) (seed : T.FullTangent) (B : ℤ) :
    T.CLiftCostAtMost seed B ↔ T.HasSmallFiberOver seed B := by
  rfl

@[simp]
theorem cLiftCostAtMost_iff_seedLiftCostAtMost
    (T : ABCTriple) (seed : T.FullTangent) (B : ℤ) :
    T.CLiftCostAtMost seed B ↔ T.SeedLiftCostAtMost seed B := by
  rfl

/-- Explicit witness data for a fixed-seed lift-cost bound.

This is intentionally elementary: one concrete lift in the fiber, together with
a proof that it satisfies the chosen coordinate bound. -/
structure ExplicitCLiftCostData
    (T : ABCTriple) (seed : T.FullTangent) (B : ℤ) where
  lift : T.FullTangent
  lift_mem : lift ∈ T.FiberOver seed
  small : T.SmallTangent lift B

/-- Prop-level existence of explicit lift-cost data. -/
def HasExplicitSmallCLiftData
    (T : ABCTriple) (seed : T.FullTangent) (B : ℤ) : Prop :=
  Nonempty (T.ExplicitCLiftCostData seed B)

/-- Explicit lift-cost data gives the corresponding cost bound. -/
theorem cLiftCostAtMost_of_explicitCLiftCostData
    (T : ABCTriple) {seed : T.FullTangent} {B : ℤ}
    (d : T.ExplicitCLiftCostData seed B) :
    T.CLiftCostAtMost seed B := by
  exact ⟨d.lift, d.lift_mem, d.small⟩

/-- A cost bound is exactly the existence of explicit lift-cost data. -/
theorem hasExplicitSmallCLiftData_iff_cLiftCostAtMost
    (T : ABCTriple) (seed : T.FullTangent) (B : ℤ) :
    T.HasExplicitSmallCLiftData seed B ↔ T.CLiftCostAtMost seed B := by
  constructor
  · intro h
    rcases h with ⟨d⟩
    exact T.cLiftCostAtMost_of_explicitCLiftCostData d
  · intro h
    rcases h with ⟨lift, hlift, hsmall⟩
    exact ⟨{ lift := lift, lift_mem := hlift, small := hsmall }⟩

/-- A concrete C-lift has a finite cost bound: use its crude coordinate bound. -/
theorem cLiftCostAtMost_coordinateBound_of_hasCLift
    (T : ABCTriple) (seed lift : T.FullTangent)
    (h : T.HasCLift seed lift) :
    T.CLiftCostAtMost seed (T.coordinateBound lift) := by
  exact ⟨lift, h, T.smallTangent_coordinateBound lift⟩

/-- A concrete C-lift also supplies explicit lift-cost data at its coordinate
bound. -/
theorem hasExplicitSmallCLiftData_coordinateBound_of_hasCLift
    (T : ABCTriple) (seed lift : T.FullTangent)
    (h : T.HasCLift seed lift) :
    T.HasExplicitSmallCLiftData seed (T.coordinateBound lift) := by
  exact (T.hasExplicitSmallCLiftData_iff_cLiftCostAtMost
    seed (T.coordinateBound lift)).2
      (T.cLiftCostAtMost_coordinateBound_of_hasCLift seed lift h)

/-- Profile-level lift cost at a fixed bound: some good base point has a
C-fiber point whose cost is at most `B`. -/
def ProfileLiftCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) : Prop :=
  ∃ seed : T.FullTangent,
    T.GoodBasePoint P seed ∧ T.CLiftCostAtMost seed B

/-- Profile lift cost is the same fixed-bound object as `SmallSectionExists`, but
named from the cost-estimation viewpoint. -/
theorem profileLiftCostAtMost_iff_smallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) (B : ℤ) :
    T.ProfileLiftCostAtMost P B ↔ T.SmallSectionExists P B := by
  constructor
  · intro h
    rcases h with ⟨seed, hgood, hcost⟩
    exact ⟨seed, hgood, hcost⟩
  · intro h
    rcases h with ⟨seed, hgood, hfiber⟩
    exact ⟨seed, hgood, hfiber⟩

/-- A fixed-bound small section gives a profile lift-cost bound. -/
theorem profileLiftCostAtMost_of_smallSectionExists
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.SmallSectionExists P B) :
    T.ProfileLiftCostAtMost P B := by
  exact (T.profileLiftCostAtMost_iff_smallSectionExists P B).2 h

/-- A profile lift-cost bound gives a fixed-bound small section. -/
theorem smallSectionExists_of_profileLiftCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.ProfileLiftCostAtMost P B) :
    T.SmallSectionExists P B := by
  exact (T.profileLiftCostAtMost_iff_smallSectionExists P B).1 h

/-- Finite profile lift cost: some bound works for some good base point. -/
def HasFiniteProfileLiftCost
    (T : ABCTriple) (P : T.CImageProfile) : Prop :=
  ∃ B : ℤ, T.ProfileLiftCostAtMost P B

/-- Finite profile lift cost is the same as finite small-section existence. -/
theorem hasFiniteProfileLiftCost_iff_hasFiniteSmallSection
    (T : ABCTriple) (P : T.CImageProfile) :
    T.HasFiniteProfileLiftCost P ↔ T.HasFiniteSmallSection P := by
  constructor
  · intro h
    rcases h with ⟨B, hcost⟩
    exact ⟨B, (T.profileLiftCostAtMost_iff_smallSectionExists P B).1 hcost⟩
  · intro h
    rcases h with ⟨B, hsection⟩
    exact ⟨B, (T.profileLiftCostAtMost_iff_smallSectionExists P B).2 hsection⟩

/-- A solved qualitative fibration automatically has finite profile lift cost. -/
theorem hasFiniteProfileLiftCost_of_qualitativeFibrationSolved
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.QualitativeFibrationSolved P) :
    T.HasFiniteProfileLiftCost P := by
  exact (T.hasFiniteProfileLiftCost_iff_hasFiniteSmallSection P).2
    (T.hasFiniteSmallSection_of_qualitativeFibrationSolved P h)

/-- A profile lift-cost bound routes to a small strict candidate at the same
bound. -/
theorem hasSmallStrictCandidate_of_profileLiftCostAtMost
    (T : ABCTriple) (P : T.CImageProfile) {B : ℤ}
    (h : T.ProfileLiftCostAtMost P B) :
    ∃ x : T.FullTangent, T.StrictCandidate x ∧ T.SmallTangent x B := by
  exact T.hasSmallStrictCandidate_of_smallSectionExists P
    (T.smallSectionExists_of_profileLiftCostAtMost P h)

/-- Finite profile lift cost routes to a finite small strict candidate. -/
theorem hasFiniteSmallStrictCandidate_of_hasFiniteProfileLiftCost
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasFiniteProfileLiftCost P) :
    T.HasFiniteSmallStrictCandidate := by
  exact T.hasFiniteSmallStrictCandidate_of_hasFiniteSmallSection P
    ((T.hasFiniteProfileLiftCost_iff_hasFiniteSmallSection P).1 h)

/-- Forgetting the bound, finite profile lift cost gives an ordinary strict
candidate. -/
theorem hasStrictCandidate_of_hasFiniteProfileLiftCost
    (T : ABCTriple) (P : T.CImageProfile)
    (h : T.HasFiniteProfileLiftCost P) :
    T.HasStrictCandidate := by
  exact T.hasStrictCandidate_of_hasFiniteSmallSection P
    ((T.hasFiniteProfileLiftCost_iff_hasFiniteSmallSection P).1 h)

namespace RealizedCImageProfile

/-- Realized-profile wrapper: finite lift cost is equivalent to finite small
section. -/
theorem hasFiniteProfileLiftCost_iff_hasFiniteSmallSection
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.HasFiniteProfileLiftCost R.profile ↔ T.HasFiniteSmallSection R.profile := by
  exact T.hasFiniteProfileLiftCost_iff_hasFiniteSmallSection R.profile

/-- Realized-profile wrapper: finite lift cost is equivalent to qualitative
fibration. -/
theorem hasFiniteProfileLiftCost_iff_qualitativeFibrationSolved
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.HasFiniteProfileLiftCost R.profile ↔ T.QualitativeFibrationSolved R.profile := by
  exact (R.hasFiniteProfileLiftCost_iff_hasFiniteSmallSection).trans
    R.hasFiniteSmallSection_iff_qualitativeFibrationSolved

/-- Realized-profile wrapper: finite lift cost is equivalent to strict-candidate
existence. -/
theorem hasFiniteProfileLiftCost_iff_hasStrictCandidate
    {T : ABCTriple} (R : T.RealizedCImageProfile) :
    T.HasFiniteProfileLiftCost R.profile ↔ T.HasStrictCandidate := by
  exact (R.hasFiniteProfileLiftCost_iff_hasFiniteSmallSection).trans
    R.hasFiniteSmallSection_iff_hasStrictCandidate

/-- Realized-profile forward form from strict candidates to finite lift cost. -/
theorem hasFiniteProfileLiftCost_of_hasStrictCandidate
    {T : ABCTriple} (R : T.RealizedCImageProfile)
    (hstrict : T.HasStrictCandidate) :
    T.HasFiniteProfileLiftCost R.profile := by
  exact (R.hasFiniteProfileLiftCost_iff_hasStrictCandidate).2 hstrict

end RealizedCImageProfile

/-- Canonical Phase 8 equivalence under `1 < c`: strict candidates are exactly
finite lift-cost solutions over the concrete gcd profile. -/
theorem hasFiniteProfileLiftCost_iff_hasStrictCandidate_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c) :
    T.HasFiniteProfileLiftCost ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) ↔
      T.HasStrictCandidate := by
  exact (T.hasFiniteProfileLiftCost_iff_hasFiniteSmallSection
      ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile)).trans
    (T.hasFiniteSmallSection_iff_hasStrictCandidate_of_one_lt_c hblocks hc)

/-- Canonical forward form: strict candidates produce finite profile lift cost over
concrete gcd profile. -/
theorem hasFiniteProfileLiftCost_of_hasStrictCandidate_of_one_lt_c
    (T : ABCTriple) (hblocks : T.SupportBlocksDecompose)
    (hc : 1 < T.c)
    (hstrict : T.HasStrictCandidate) :
    T.HasFiniteProfileLiftCost ((T.cImageGCDWitness_of_one_lt_c hblocks hc).profile) := by
  exact (T.hasFiniteProfileLiftCost_iff_hasStrictCandidate_of_one_lt_c hblocks hc).2 hstrict

end ABCTriple
end ABD2
