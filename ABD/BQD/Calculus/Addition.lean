import ABD.BQD.Calculus.Core

namespace ABD
namespace BQD
namespace Decomp

variable {α : Type u} [DecidableEq α]

/-- Carry-generate region for two 0/1 inputs: both active. -/
def Generate (D : Decomp α) : Finset α :=
  D.B

/-- Carry-propagate region for two 0/1 inputs: exactly one active. -/
def Propagate (D : Decomp α) : Finset α :=
  D.LO ∪ D.RO

/-- Carry-kill region for two 0/1 inputs: neither active. -/
def Kill (D : Decomp α) : Finset α :=
  D.N

/-- Sum bits before incoming carry are exactly the propagate region. -/
def SumNoCarry (D : Decomp α) : Finset α :=
  D.Propagate

@[simp] theorem Generate_eq_B (D : Decomp α) :
    D.Generate = D.B := rfl

@[simp] theorem Propagate_eq_exclusive (D : Decomp α) :
    D.Propagate = D.exclusive := rfl

@[simp] theorem Kill_eq_N (D : Decomp α) :
    D.Kill = D.N := rfl

@[simp] theorem SumNoCarry_eq_Propagate (D : Decomp α) :
    D.SumNoCarry = D.Propagate := rfl

end Decomp
end BQD
end ABD
