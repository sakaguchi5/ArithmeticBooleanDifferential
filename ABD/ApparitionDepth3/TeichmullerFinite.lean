/-
  ABD.ApparitionDepth3.TeichmullerFinite

  Finite Teichmuller generation from concrete primitive-root branches.
-/

import ABD.ApparitionDepth3.BranchGenerator

namespace ApparitionDepth3

/-- A finite Teichmuller lift on the concrete `(g,p,d,j)` branch. -/
def TeichmullerLiftAtLevel
    (g p d j omega r : Nat) : Prop :=
  LiftAtLevel (branchSeed g p d j) omega p d r

/-- Existence and uniqueness of a finite Teichmuller lift at precision `p^r`. -/
def ExistsUniqueTeichmullerLiftAtLevel
    (g p d j r : Nat) : Prop :=
  ExistsUniqueLiftAtLevel (branchSeed g p d j) p d r

/-- Concrete primitive-root branch data have a unique finite Teichmuller lift
at every positive level. -/
theorem existsUniqueTeichmullerLiftAtLevel
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    ExistsUniqueTeichmullerLiftAtLevel g p d j r := by
  unfold ExistsUniqueTeichmullerLiftAtLevel
  exact existsUniqueLiftAtLevel_of_simpleRoot
    (branchSeed_simpleRoot hcopG hprimitive hparams) hrPos

/-- Equality modulo `p^r`, for positive `r`, descends to equality modulo `p`. -/
theorem zmodEq_modP_of_primePower_eq
    {x y p r : Nat}
    (hrPos : 0 < r)
    (hxy : (x : ZMod (p ^ r)) = (y : ZMod (p ^ r))) :
    (x : ZMod p) = (y : ZMod p) := by
  have hdiv : p ∣ p ^ r := by
    cases r with
    | zero => exact False.elim ((Nat.not_lt_zero 0) hrPos)
    | succ k =>
        rw [pow_succ]
        exact dvd_mul_left p (p ^ k)
  let red : ZMod (p ^ r) →+* ZMod p := ZMod.castHom hdiv (ZMod p)
  have hmap := congrArg red hxy
  simpa only [red, ZMod.castHom_apply, ZMod.cast_natCast hdiv] using hmap

/-- Coprimality transfers across equality of residue classes. -/
theorem coprime_of_zmod_eq_of_coprime
    {x y p : Nat}
    (hxy : (x : ZMod p) = (y : ZMod p))
    (hy : y.Coprime p) :
    x.Coprime p := by
  apply (ZMod.isUnit_iff_coprime x p).mp
  have hyUnit : IsUnit ((y : Nat) : ZMod p) :=
    (ZMod.isUnit_iff_coprime y p).mpr hy
  rw [hxy]
  exact hyUnit

/-- Exact multiplicative order transfers across equality modulo `p`. -/
theorem orderModIs_of_zmod_eq
    {x y p d : Nat}
    {hx : x.Coprime p} {hy : y.Coprime p}
    (hxy : (x : ZMod p) = (y : ZMod p))
    (hord : OrderModIs y p d hy) :
    OrderModIs x p d hx := by
  unfold OrderModIs orderMod at hord ⊢
  have hu : unitMod x p hx = unitMod y p hy := by
    apply Units.ext
    simpa [coe_unitMod] using hxy
  rw [hu]
  exact hord

/-- The public data carried by every positive base in a finite Teichmuller
residue class. -/
structure TeichmullerClassResult
    (ell p d r : Nat) : Prop where
  coprime : ell.Coprime p
  exactOrder : OrderModIs ell p d coprime
  rootAtLevel : RootAtLevel ell p d r
  firstWithDepth : FirstAppearsWithDepthAtLeast ell p d r

/-- Every positive natural representative in the generated class has exact
first apparition `d` and depth at least `r`. -/
theorem teichmullerClassResult
    {g p d j omega r ell : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (hlift : TeichmullerLiftAtLevel g p d j omega r)
    (hellClass : (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)))
    (hellPos : 0 < ell) :
    TeichmullerClassResult ell p d r := by
  have hellOmegaP : (ell : ZMod p) = (omega : ZMod p) :=
    zmodEq_modP_of_primePower_eq hrPos hellClass
  have homegaSeed :
      (omega : ZMod p) = (branchSeed g p d j : ZMod p) := hlift.1
  have hellSeed :
      (ell : ZMod p) = (branchSeed g p d j : ZMod p) :=
    hellOmegaP.trans homegaSeed
  have hcopSeed : (branchSeed g p d j).Coprime p := branchSeed_coprime hcopG
  have hellCop : ell.Coprime p :=
    coprime_of_zmod_eq_of_coprime hellSeed hcopSeed
  have hseedOrder :
      OrderModIs (branchSeed g p d j) p d hcopSeed :=
    branchSeed_orderModIs hcopG hprimitive hparams
  have hellOrder : OrderModIs ell p d hellCop :=
    orderModIs_of_zmod_eq hellSeed hseedOrder
  have hellRoot : RootAtLevel ell p d r :=
    rootAtLevel_of_baseInBranchAtLevel
      (seed := branchSeed g p d j) ⟨hellClass, hlift⟩
  have hellDepth : DepthAtLeast ell p d r :=
    depthAtLeast_of_rootAtLevel_of_base_pos hellPos hellRoot
  have hellFirstDepth : FirstAppearsWithDepthAtLeast ell p d r :=
    firstWithDepth_of_order_and_depth hellOrder
      (branchParams_d_pos hparams) hellPos hellDepth
  exact ⟨hellCop, hellOrder, hellRoot, hellFirstDepth⟩

/-- The canonical lifted representative itself has exact first apparition and
at least the requested depth. -/
theorem teichmullerLift_firstAppearsWithDepthAtLeast
    {g p d j omega r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (hlift : TeichmullerLiftAtLevel g p d j omega r) :
    FirstAppearsWithDepthAtLeast omega p d r := by
  have hsimple := branchSeed_simpleRoot hcopG hprimitive hparams
  have homegaPos : 0 < omega :=
    liftRepresentative_pos_of_simpleRoot hsimple hlift
  exact (teichmullerClassResult hcopG hprimitive hparams hrPos hlift rfl homegaPos).firstWithDepth

/-- Existence of a concrete finite Teichmuller representative together with its
apparition-depth conclusion. -/
theorem exists_teichmullerLift_with_firstDepth
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    ∃ omega : Nat,
      TeichmullerLiftAtLevel g p d j omega r ∧
        FirstAppearsWithDepthAtLeast omega p d r := by
  rcases existsUniqueTeichmullerLiftAtLevel hcopG hprimitive hparams hrPos with
    ⟨omega, hlift, _hunique⟩
  exact ⟨omega, hlift,
    teichmullerLift_firstAppearsWithDepthAtLeast
      hcopG hprimitive hparams hrPos hlift⟩

end ApparitionDepth3
