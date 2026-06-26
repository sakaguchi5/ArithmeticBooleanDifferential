import ABD.BQD.Calculus.Addition

namespace ABD
namespace BQD
namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- One local carry step as a Boolean recurrence.

`generate ∨ (propagate ∧ carry)` is the usual carry-lookahead recurrence.
This proposition-level version is useful before choosing an ordered bit universe. -/
def nextCarryProp (generate propagate carry : Prop) : Prop :=
  generate ∨ (propagate ∧ carry)

/-- Abstract carry mask update on a common universe.

This is not yet a shifted bit-carry.  It records the local Boolean rule:
new carry positions are generated positions, plus propagated incoming carry. -/
def carryStep (D : Decomp α) (incoming : Finset α) : Finset α :=
  D.Generate ∪ (D.Propagate ∩ incoming)

@[simp] theorem carryStep_def (D : Decomp α) (incoming : Finset α) :
    D.carryStep incoming = D.Generate ∪ (D.Propagate ∩ incoming) := rfl

@[simp] theorem carryStep_empty (D : Decomp α) :
    D.carryStep ∅ = D.Generate := by
  ext x
  simp [carryStep]


end Decomp
end BQD
end ABD
