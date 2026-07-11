/-
  ABD.ApparitionDepth3.HenselConcrete

  Assembly of the three concrete local facts into HenselLocalData.
-/

import ABD.ApparitionDepth3.HenselUniqueness

namespace ApparitionDepth3

/-- A simple root modulo a prime supplies all local data required by the finite
Hensel kernel: descent, one-step existence, and one-step uniqueness. -/
theorem henselLocalData_of_simpleRoot
    {seed p d : Nat} [Fact p.Prime]
    (hsimple : SimpleRootModP seed p d) :
    HenselLocalData seed p d :=
  henselLocalData_intro
    (henselRootDescent_actual p d)
    (henselOneStepExists_of_simpleRoot hsimple)
    (henselOneStepUnique_of_simpleRoot hsimple)

/-- Seed-simple-root spelling. -/
theorem henselLocalData_of_seedSimpleRoot
    {seed p d : Nat} [Fact p.Prime]
    (hsimple : SeedSimpleRootModP seed p d) :
    HenselLocalData seed p d :=
  henselLocalData_of_simpleRoot hsimple

end ApparitionDepth3
