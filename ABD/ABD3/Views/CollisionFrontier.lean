import ABD.ABD3.Views.DPlusGraph.Frontier

namespace ABD3
namespace ABCData

def ResidualRadical (_T : ABCData) (s : ℕ) : ℕ :=
  radOfSupport (primeSupport s)

structure OnePlaceCollisionData (T : ABCData) where
  p : ℕ
  q : ℕ
  r : ℕ
  s : ℕ
  u : ℕ
  v : ℕ
  w : ℕ
  hp : Nat.Prime p
  hq : Nat.Prime q
  hr : Nat.Prime r
  hs_pos : 0 < s
  hw_pos : 0 < w
  hA : T.A.val = p ^ u
  hB : T.B.val = q ^ v
  hC : T.C.val = r ^ w * s
  hcop_core_residual : Nat.Coprime r s

namespace OnePlaceCollisionData

def residualRadical {T : ABCData} (D : T.OnePlaceCollisionData) : ℕ :=
  T.ResidualRadical D.s

theorem core_dvd_C {T : ABCData} (D : T.OnePlaceCollisionData) :
    D.r ^ D.w ∣ T.C.val := by
  exact ⟨D.s, D.hC⟩

theorem core_dvd_source_sum {T : ABCData} (D : T.OnePlaceCollisionData) :
    D.r ^ D.w ∣ D.p ^ D.u + D.q ^ D.v := by
  refine ⟨D.s, ?_⟩
  rw [← D.hA, ← D.hB, T.h_add, D.hC]

def SingleSurplusCore {T : ABCData}
    (D : T.OnePlaceCollisionData) (P : PowerData) : Prop :=
  T.CSurplusPorts P = {D.r}

def ResidualDeficit {T : ABCData}
    (D : T.OnePlaceCollisionData) (P : PowerData) : Prop :=
  ∀ ⦃l : ℕ⦄, l ∈ primeSupport D.s →
    l ∈ T.supportC ∧ T.ExponentSurplusAt P l ≤ 0

def PrimesContainedIn {T : ABCData}
    (D : T.OnePlaceCollisionData) (S : Finset ℕ) : Prop :=
  D.p ∈ S ∧ D.q ∈ S ∧ D.r ∈ S ∧
    ∀ ⦃l : ℕ⦄, l ∈ primeSupport D.s → l ∈ S

end OnePlaceCollisionData

def SinglePositiveCPort (T : ABCData) (P : PowerData) : Prop :=
  ∃ r : ℕ, T.CSurplusPorts P = {r}

def RankOneOneDesyncFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.LowABSupportRank ∧
    T.NonExceptional ∧
      T.RadicalSmall P ∧
        T.SinglePositiveCPort P ∧
          T.NoAcceptedArithmeticEdge P G R

def EfficientOnePlaceCollisionFrontier
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.RankOneOneDesyncFrontier P G R ∧
    ∃ D : T.OnePlaceCollisionData,
      D.SingleSurplusCore P ∧ D.ResidualDeficit P

def RankOneOneDesyncToEfficientCollisionGoal
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  T.RankOneOneDesyncFrontier P G R →
    T.EfficientOnePlaceCollisionFrontier P G R

theorem onePlaceCollision_of_rankOneOneDesync
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : T.RankOneOneDesyncToEfficientCollisionGoal P G R)
    (hfrontier : T.RankOneOneDesyncFrontier P G R) :
    ∃ D : T.OnePlaceCollisionData,
      D.SingleSurplusCore P ∧ D.ResidualDeficit P := by
  rcases hgoal hfrontier with ⟨_, hD⟩
  exact hD

def FixedSupportCollisionFinitenessGoal
    (S : Finset ℕ) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ) : Prop :=
  ∃ reps : List ABCData,
    ∀ T : ABCData,
      T.EfficientOnePlaceCollisionFrontier P G R →
        (∃ D : T.OnePlaceCollisionData,
          D.SingleSurplusCore P ∧ D.ResidualDeficit P ∧ D.PrimesContainedIn S) →
            T ∈ reps

theorem fixedSupport_collision_finite
    (S : Finset ℕ) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R : ℕ)
    (hgoal : FixedSupportCollisionFinitenessGoal S P G R) :
    ∃ reps : List ABCData,
      ∀ T : ABCData,
        T.EfficientOnePlaceCollisionFrontier P G R →
          (∃ D : T.OnePlaceCollisionData,
            D.SingleSurplusCore P ∧ D.ResidualDeficit P ∧ D.PrimesContainedIn S) →
              T ∈ reps := by
  exact hgoal

def ThinCollisionExceptional (T : ABCData) (_P : PowerData) : Prop :=
  T.SupportSmallExceptional ∨ T.UnitBoundary

def OnePlaceResidualGrowthOrThinGoal
    (T : ABCData) (P : PowerData) (K : ℕ) : Prop :=
  ∀ D : T.OnePlaceCollisionData,
    D.SingleSurplusCore P →
      D.ResidualDeficit P →
        K ≤ D.residualRadical ∨ T.ThinCollisionExceptional P

theorem residualGrowth_or_thin_of_efficientOnePlaceCollision
    (T : ABCData) (P : PowerData) (K : ℕ)
    (hgoal : T.OnePlaceResidualGrowthOrThinGoal P K)
    (D : T.OnePlaceCollisionData)
    (hcore : D.SingleSurplusCore P)
    (hdef : D.ResidualDeficit P) :
    K ≤ D.residualRadical ∨ T.ThinCollisionExceptional P := by
  exact hgoal D hcore hdef

theorem rankOneOneDesync_frontier_residualGrowth_or_thin
    (T : ABCData) (P : PowerData)
    (G : ArithmeticSyncGenerators) (R K : ℕ)
    (hclass : T.RankOneOneDesyncToEfficientCollisionGoal P G R)
    (hdich : T.OnePlaceResidualGrowthOrThinGoal P K)
    (hfrontier : T.RankOneOneDesyncFrontier P G R) :
    ∃ D : T.OnePlaceCollisionData,
      K ≤ D.residualRadical ∨ T.ThinCollisionExceptional P := by
  rcases T.onePlaceCollision_of_rankOneOneDesync P G R hclass hfrontier with
    ⟨D, hcore, hdef⟩
  exact ⟨D, hdich D hcore hdef⟩

end ABCData
end ABD3
