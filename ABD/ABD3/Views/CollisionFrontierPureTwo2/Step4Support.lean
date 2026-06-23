import ABD.ABD3.Views.CollisionFrontierPureTwo2.Step3Equation

namespace ABD3
namespace ABCData
namespace CollisionFrontierPureTwo2
namespace NormalForm

variable {T : ABCData} {P : PowerData}

/-- A-side support is the singleton `{p}`. -/
theorem supportA_eq_singleton_p (F : NormalForm T P) :
    T.supportA = ({F.p} : Support) := by
  have h := primeSupport_prime_pow_self F.p_prime F.u_pos
  simpa [supportA, F.A_eq_p_pow_u] using h

/-- B-side support is the singleton `{q}`. -/
theorem supportB_eq_singleton_q (F : NormalForm T P) :
    T.supportB = ({F.q} : Support) := by
  have h := primeSupport_prime_pow_self F.q_prime F.v_pos
  simpa [supportB, F.B_eq_q_pow_v] using h

/-- C-side support is the singleton `{2}`. -/
theorem supportC_eq_singleton_two (F : NormalForm T P) :
    T.supportC = ({2} : Support) := by
  have h := primeSupport_prime_pow_self Nat.prime_two F.w_pos
  simpa [supportC, F.C_eq_two_pow] using h

/-- The A prime is not the C prime `2`, by primitive support disjointness. -/
theorem p_ne_two (F : NormalForm T P) :
    F.p ≠ 2 := by
  intro hp2
  rcases T.supportBlocksDisjoint with ⟨_hAB, hAC, _hBC⟩
  have hpA : F.p ∈ T.supportA := by
    rw [F.supportA_eq_singleton_p]
    simp
  have h2A : 2 ∈ T.supportA := by
    simpa [hp2] using hpA
  have h2C : 2 ∈ T.supportC := by
    rw [F.supportC_eq_singleton_two]
    simp
  have hmem : 2 ∈ T.supportA ∩ T.supportC :=
    Finset.mem_inter.mpr ⟨h2A, h2C⟩
  have hbad : 2 ∈ (∅ : Support) := by
    rw [← hAC]
    exact hmem
  simp at hbad

/-- The B prime is not the C prime `2`, by primitive support disjointness. -/
theorem q_ne_two (F : NormalForm T P) :
    F.q ≠ 2 := by
  intro hq2
  rcases T.supportBlocksDisjoint with ⟨_hAB, _hAC, hBC⟩
  have hqB : F.q ∈ T.supportB := by
    rw [F.supportB_eq_singleton_q]
    simp
  have h2B : 2 ∈ T.supportB := by
    simpa [hq2] using hqB
  have h2C : 2 ∈ T.supportC := by
    rw [F.supportC_eq_singleton_two]
    simp
  have hmem : 2 ∈ T.supportB ∩ T.supportC :=
    Finset.mem_inter.mpr ⟨h2B, h2C⟩
  have hbad : 2 ∈ (∅ : Support) := by
    rw [← hBC]
    exact hmem
  simp at hbad

/-- The two A/B base primes are distinct because the normal form stores `p < q`. -/
theorem p_ne_q (F : NormalForm T P) :
    F.p ≠ F.q :=
  ne_of_lt F.p_lt_q

/-- The full ABC support is exactly the three-point support `{2,p,q}`. -/
theorem supportABC_eq_three (F : NormalForm T P) :
    T.supportABC = ({2, F.p, F.q} : Support) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ({F.p} : Support) ∪ ({F.q} : Support) ∪ ({2} : Support) := by
      simpa [supportABC, F.supportA_eq_singleton_p, F.supportB_eq_singleton_q,
        F.supportC_eq_singleton_two] using hx
    have hx_or : x = F.p ∨ x = F.q ∨ x = 2 := by
      simpa using hx'
    rcases hx_or with hxp | hxq | hx2
    · subst x; simp
    · subst x; simp
    · subst x; simp
  · intro hx
    have hx_or : x = 2 ∨ x = F.p ∨ x = F.q := by
      simpa using hx
    have hx_union : x ∈ ({F.p} : Support) ∪ ({F.q} : Support) ∪ ({2} : Support) := by
      rcases hx_or with hx2 | hxp | hxq
      · subst x; simp
      · subst x; simp
      · subst x; simp
    simpa [supportABC, F.supportA_eq_singleton_p, F.supportB_eq_singleton_q,
      F.supportC_eq_singleton_two] using hx_union

/-- The A-support prime belongs to the full support. -/
theorem p_mem_supportABC (F : NormalForm T P) :
    F.p ∈ T.supportABC := by
  rw [F.supportABC_eq_three]
  simp

/-- The B-support prime belongs to the full support. -/
theorem q_mem_supportABC (F : NormalForm T P) :
    F.q ∈ T.supportABC := by
  rw [F.supportABC_eq_three]
  simp

/-- The C-support prime `2` belongs to the full support. -/
theorem two_mem_supportABC (F : NormalForm T P) :
    2 ∈ T.supportABC := by
  rw [F.supportABC_eq_three]
  simp

end NormalForm
end CollisionFrontierPureTwo2
end ABCData
end ABD3
