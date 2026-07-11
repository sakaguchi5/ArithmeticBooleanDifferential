/-
  ABD.ApparitionDepth3.PrimitiveDivisor

  Primitive prime divisors expressed through the existing apparition language.
-/

import ABD.ApparitionDepth3.TeichmullerFinite

namespace ApparitionDepth3

/-- `p` is a primitive prime divisor of `ell^d - 1`: it appears at the positive
exponent `d` and at no earlier positive exponent. -/
def PrimitivePrimeDivisor (ell p d : Nat) : Prop :=
  p.Prime ∧ 0 < d ∧ AppearsAt ell p d ∧
    ∀ m : Nat, 0 < m → m < d → ¬ AppearsAt ell p m

/-- Primitive-prime-divisor language is exactly primality plus first
apparition. -/
theorem primitivePrimeDivisor_iff_prime_and_firstAppears
    {ell p d : Nat} :
    PrimitivePrimeDivisor ell p d ↔ p.Prime ∧ FirstAppearsAt ell p d := by
  unfold PrimitivePrimeDivisor FirstAppearsAt
  constructor
  · rintro ⟨hp, hdPos, happ, hmin⟩
    exact ⟨hp, hdPos, happ, hmin⟩
  · rintro ⟨hp, hdPos, happ, hmin⟩
    exact ⟨hp, hdPos, happ, hmin⟩

/-- A first apparition at a prime is a primitive prime divisor statement. -/
theorem primitivePrimeDivisor_of_firstAppears
    {ell p d : Nat} [Fact p.Prime]
    (hfirst : FirstAppearsAt ell p d) :
    PrimitivePrimeDivisor ell p d :=
  (primitivePrimeDivisor_iff_prime_and_firstAppears).mpr
    ⟨Fact.out, hfirst⟩

/-- A primitive prime divisor first appears at its stated exponent. -/
theorem firstAppearsAt_of_primitivePrimeDivisor
    {ell p d : Nat}
    (hprimitive : PrimitivePrimeDivisor ell p d) :
    FirstAppearsAt ell p d :=
  (primitivePrimeDivisor_iff_prime_and_firstAppears).mp hprimitive |>.2

/-- Every positive base in a concrete finite Teichmuller class has `p` as a
primitive prime divisor at exponent `d`. -/
theorem teichmullerClass_primitivePrimeDivisor
    {g p d j omega r ell : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (hlift : TeichmullerLiftAtLevel g p d j omega r)
    (hellClass : (ell : ZMod (p ^ r)) = (omega : ZMod (p ^ r)))
    (hellPos : 0 < ell) :
    PrimitivePrimeDivisor ell p d := by
  have hresult :=
    teichmullerClassResult hcopG hprimitive hparams hrPos hlift hellClass hellPos
  exact primitivePrimeDivisor_of_firstAppears hresult.firstWithDepth.1

/-- The canonical finite Teichmuller representative has `p` as a primitive
prime divisor at exponent `d`. -/
theorem teichmullerLift_primitivePrimeDivisor
    {g p d j omega r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r)
    (hlift : TeichmullerLiftAtLevel g p d j omega r) :
    PrimitivePrimeDivisor omega p d := by
  have hsimple := branchSeed_simpleRoot hcopG hprimitive hparams
  have homegaPos : 0 < omega :=
    liftRepresentative_pos_of_simpleRoot hsimple hlift
  exact teichmullerClass_primitivePrimeDivisor
    hcopG hprimitive hparams hrPos hlift rfl homegaPos

/-- Stage 4-6 synthesis: a primitive generator and branch parameters produce a
unique finite lift whose first apparition, depth, and primitive-divisor status
are all controlled. -/
theorem exists_teichmullerLift_with_primitiveDepth
    {g p d j r : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hparams : BranchParams p d j)
    (hrPos : 0 < r) :
    ∃ omega : Nat,
      TeichmullerLiftAtLevel g p d j omega r ∧
      FirstAppearsWithDepthAtLeast omega p d r ∧
      PrimitivePrimeDivisor omega p d := by
  rcases existsUniqueTeichmullerLiftAtLevel hcopG hprimitive hparams hrPos with
    ⟨omega, hlift, _hunique⟩
  exact ⟨omega, hlift,
    teichmullerLift_firstAppearsWithDepthAtLeast
      hcopG hprimitive hparams hrPos hlift,
    teichmullerLift_primitivePrimeDivisor
      hcopG hprimitive hparams hrPos hlift⟩

end ApparitionDepth3
