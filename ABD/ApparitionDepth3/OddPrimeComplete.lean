/-
  ABD.ApparitionDepth3.OddPrimeComplete

  Stage 16:
    complete synthesis for odd target primes.  Every exact-order-d residue has
    one unique branch index, and every branch carries the global finite/p-adic/
    Witt/carry/exact-depth synthesis.
-/

import ABD.ApparitionDepth3.BranchClassification

namespace ApparitionDepth3

/-- Standard natural representative of an arbitrary p-adic integer at level r. -/
noncomputable def padicLevelRepresentative
    {p : Nat} [Fact p.Prime] (theta : ℤ_[p]) (r : Nat) : Nat :=
  (PadicInt.toZModPow r theta).val

/-- Casting the standard representative recovers the finite p-adic coordinate. -/
theorem padicLevelRepresentative_cast
    {p r : Nat} [Fact p.Prime] (theta : ℤ_[p]) :
    (padicLevelRepresentative theta r : ZMod (p ^ r)) =
      PadicInt.toZModPow r theta := by
  unfold padicLevelRepresentative
  exact ZMod.natCast_zmod_val _

/-- The standard representative of a p-adic d-th root is a finite root at every level. -/
theorem padicLevelRepresentative_rootAtLevel
    {p d r : Nat} [Fact p.Prime] (theta : ℤ_[p])
    (hroot : theta ^ d = 1) :
    RootAtLevel (padicLevelRepresentative theta r) p d r := by
  unfold RootAtLevel
  rw [padicLevelRepresentative_cast]
  rw [← map_pow, hroot, map_one]

theorem zmodPowOne_transport_natCast
    {p r a b : Nat} [Fact p.Prime]
    (hrOne : 1 ≤ r)
    (h :
      (ZMod.cast (a : ZMod (p ^ r)) : ZMod (p ^ 1)) =
        (b : ZMod (p ^ 1))) :
    (a : ZMod p) = (b : ZMod p) := by
  let e : ZMod (p ^ 1) ≃+* ZMod p :=
    ZMod.ringEquivCongr (pow_one p)
  have hpOneDvd : p ^ 1 ∣ p ^ r :=
    pow_dvd_pow p hrOne
  have hleft :
      e (ZMod.cast (a : ZMod (p ^ r)) : ZMod (p ^ 1)) =
        (a : ZMod p) := by
    rw [ZMod.cast_natCast hpOneDvd a]
    simp
  have hright :
      e (b : ZMod (p ^ 1)) = (b : ZMod p) := by
    simp
  calc
    (a : ZMod p) =
        e (ZMod.cast (a : ZMod (p ^ r)) : ZMod (p ^ 1)) :=
      hleft.symm
    _ = e (b : ZMod (p ^ 1)) := congrArg e h
    _ = (b : ZMod p) := hright

/-- Positive finite coordinates of the same p-adic integer have the same
reduction modulo p as its level-one coordinate. -/
theorem padicLevelRepresentative_modP
    {p r : Nat} [Fact p.Prime] (theta : ℤ_[p])
    (hrPos : 0 < r) :
    (padicLevelRepresentative theta r : ZMod p) =
      (padicLevelRepresentative theta 1 : ZMod p) := by
  have hrOne : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hrPos.ne'
  have hcompat := PadicInt.cast_toZModPow 1 r hrOne theta
  have hlevelOne :
      (ZMod.cast
          (padicLevelRepresentative theta r : ZMod (p ^ r)) :
          ZMod (p ^ 1)) =
        (padicLevelRepresentative theta 1 : ZMod (p ^ 1)) := by
    calc
      (ZMod.cast
          (padicLevelRepresentative theta r : ZMod (p ^ r)) :
          ZMod (p ^ 1)) =
          ZMod.cast (PadicInt.toZModPow r theta) := by
            exact congrArg
              (fun z : ZMod (p ^ r) =>
                (ZMod.cast z : ZMod (p ^ 1)))
              (padicLevelRepresentative_cast theta)
      _ = PadicInt.toZModPow 1 theta := hcompat
      _ = (padicLevelRepresentative theta 1 : ZMod (p ^ 1)) :=
        (padicLevelRepresentative_cast theta).symm
  exact zmodPowOne_transport_natCast hrOne hlevelOne

/-- Strong p-adic inverse classification.  A p-adic d-th root whose level-one
residue has exact order d is exactly one of the classified branch roots. -/
theorem existsUnique_branchIndex_for_padicRoot
    {g p d : Nat} [Fact p.Prime]
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hdvd : d ∣ p - 1)
    (hdPos : 0 < d)
    (theta : ℤ_[p])
    (hroot : theta ^ d = 1)
    (hcopTheta : (padicLevelRepresentative theta 1).Coprime p)
    (horderTheta :
      OrderModIs (padicLevelRepresentative theta 1) p d hcopTheta) :
    ∃! j : {j : Nat // BranchIndex d j},
      theta = branchPadicRoot g p d j := by
  rcases existsUnique_branchIndex_for_residue
      hcopG hprimitive hdvd hdPos hcopTheta horderTheta with
    ⟨j, hjSeed, hjUnique⟩
  have htheta : theta = branchPadicRoot g p d j := by
    apply PadicInt.ext_of_toZModPow.mp
    intro r
    cases r with
    | zero =>
        letI : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.mpr (by simp)
        apply Subsingleton.elim
    | succ n =>
        have hrPos : 0 < n + 1 := Nat.succ_pos n
        let omega := padicLevelRepresentative theta (n + 1)
        have homegaSeed :
            BranchSeedModP (branchSeed g p d j) omega p := by
          unfold BranchSeedModP
          have hmodP := padicLevelRepresentative_modP theta hrPos
          exact hmodP.trans hjSeed
        have homegaRoot : RootAtLevel omega p d (n + 1) := by
          simpa only [omega] using
            (padicLevelRepresentative_rootAtLevel theta hroot)
        have hlift : TeichmullerLiftAtLevel g p d j omega (n + 1) :=
          ⟨homegaSeed, homegaRoot⟩
        have heq := teichmullerLift_eq_branchPadicReduction
          hcopG hprimitive ⟨hdvd, j.property⟩ hrPos hlift
        exact (padicLevelRepresentative_cast theta).symm.trans heq
  refine ⟨j, htheta, ?_⟩
  intro j' htheta'
  apply hjUnique
  let e : ZMod (p ^ 1) ≃+* ZMod p := ZMod.ringEquivCongr (pow_one p)
  have hred := congrArg (PadicInt.toZModPow 1) htheta'
  change PadicInt.toZModPow 1 theta =
    branchPadicReduction g p d j' 1 at hred
  have hred' :
      PadicInt.toZModPow 1 theta =
        (branchSeed g p d j' : ZMod (p ^ 1)) := by
    rw [branchPadicReduction_one] at hred
    exact hred
  have hrep :
      (padicLevelRepresentative theta 1 : ZMod (p ^ 1)) =
        (branchSeed g p d j' : ZMod (p ^ 1)) :=
    (padicLevelRepresentative_cast theta).trans hred'
  have htransport := congrArg e hrep
  simpa using htransport


/-- A practical version of the odd-prime package with the generator-coprimality
proof stored explicitly, avoiding proof reconstruction in clients. -/
structure OddPrimeCompleteSynthesis
    (g p d : Nat) [Fact p.Prime] (hcopG : g.Coprime p) where
  oddPrime : p ≠ 2
  divisor : d ∣ p - 1
  orderPositive : 0 < d
  primitive : PrimitiveRootModP g p hcopG
  branchSynthesis : ∀ j : Nat, BranchIndex d j →
    GlobalApparitionSynthesisResult g p d j
  unitClassification : ∀ y : (ZMod p)ˣ, orderOf y = d →
    ∃! j : {j : Nat // BranchIndex d j},
      y = branchUnit g p d j hcopG
  residueClassification : ∀ (ell : Nat) (hcopEll : ell.Coprime p),
    OrderModIs ell p d hcopEll →
      ∃! j : {j : Nat // BranchIndex d j},
        (ell : ZMod p) = (branchSeed g p d j : ZMod p)
  padicClassification : ∀ (theta : ℤ_[p])
      (_hroot : theta ^ d = 1)
      (hcopTheta : (padicLevelRepresentative theta 1).Coprime p),
    OrderModIs (padicLevelRepresentative theta 1) p d hcopTheta →
      ∃! j : {j : Nat // BranchIndex d j},
        theta = branchPadicRoot g p d j

/-- Complete odd-prime synthesis, including inverse branch classification. -/
noncomputable def oddPrimeCompleteSynthesis
    {g p d : Nat} [Fact p.Prime]
    (hpOdd : p ≠ 2)
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hdvd : d ∣ p - 1)
    (hdPos : 0 < d) :
    OddPrimeCompleteSynthesis g p d hcopG := by
  refine
    { oddPrime := hpOdd
      divisor := hdvd
      orderPositive := hdPos
      primitive := hprimitive
      branchSynthesis := ?_
      unitClassification := ?_
      residueClassification := ?_
      padicClassification := ?_ }
  · intro j hj
    exact globalApparitionSynthesis hcopG hprimitive ⟨hdvd, hj⟩
  · intro y hy
    exact existsUnique_branchIndex_for_unit
      hcopG hprimitive hdvd hdPos y hy
  · intro ell hcopEll horder
    exact existsUnique_branchIndex_for_residue
      hcopG hprimitive hdvd hdPos hcopEll horder
  · intro theta hroot hcopTheta horderTheta
    exact existsUnique_branchIndex_for_padicRoot
      hcopG hprimitive hdvd hdPos theta hroot hcopTheta horderTheta

/-- Existence spelling of the strongest odd-prime result. -/
theorem exists_oddPrimeCompleteSynthesis
    {g p d : Nat} [Fact p.Prime]
    (hpOdd : p ≠ 2)
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hdvd : d ∣ p - 1)
    (hdPos : 0 < d) :
    Nonempty (OddPrimeCompleteSynthesis g p d hcopG) :=
  ⟨oddPrimeCompleteSynthesis hpOdd hcopG hprimitive hdvd hdPos⟩

/-- A p-adic integer is determined by all of its finite reductions.  This is the
final uniqueness bridge used after inverse branch classification identifies the
level-one branch. -/
theorem padic_eq_branchPadicRoot_of_all_reductions
    {g p d j : Nat} [Fact p.Prime]
    (theta : ℤ_[p])
    (hred : ∀ r : Nat,
      PadicInt.toZModPow r theta = branchPadicReduction g p d j r) :
    theta = branchPadicRoot g p d j := by
  apply PadicInt.ext_of_toZModPow.mp
  intro r
  simpa only [branchPadicReduction] using hred r

/-- Compact all-branches statement: every valid branch index has a global
synthesis and every exact-order residue selects exactly one of them. -/
theorem oddPrime_allBranches_and_complete
    {g p d : Nat} [Fact p.Prime]
    (hpOdd : p ≠ 2)
    (hcopG : g.Coprime p)
    (hprimitive : PrimitiveRootModP g p hcopG)
    (hdvd : d ∣ p - 1)
    (hdPos : 0 < d) :
    (∀ j : Nat, BranchIndex d j →
      Nonempty (GlobalApparitionSynthesisResult g p d j)) ∧
    (∀ y : (ZMod p)ˣ, orderOf y = d →
      ∃! j : {j : Nat // BranchIndex d j},
        y = branchUnit g p d j hcopG) := by
  let h := oddPrimeCompleteSynthesis
    hpOdd hcopG hprimitive hdvd hdPos
  exact ⟨fun j hj => ⟨h.branchSynthesis j hj⟩, h.unitClassification⟩

end ApparitionDepth3
