module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial NumberField
open Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

section Numbers

variable {n : ℕ}

def Interlace (lam : DomWeight (n + 1)) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, lam.w i.succ ≤ sg.w i ∧ sg.w i ≤ lam.w i.castSucc

def EqualLast (lam : DomWeight (n + 1)) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, i.val + 1 = n → sg.w i = lam.w (Fin.last n)



def dZero (lam : DomWeight (n + 1)) (sg : DomWeight n) : ℤ := ∑ i : Fin n, (sg.w i - lam.w i.succ)

def rangeSet (lam : DomWeight (n + 1)) (sg : DomWeight n) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w i.succ) (min (lam.w i.castSucc) (lam.w i.succ + dZero lam sg))


end Numbers

section Capelli

variable (K : Type) [Field K] (n : ℕ)




variable {n}


end Capelli

section Tensors

variable (K : Type) [Field K] {n : ℕ}




variable {ι : Type} [Fintype ι]



end Tensors

section Maps

variable (K : Type) [Field K] {n : ℕ} {ι : Type} [Fintype ι]

instance finiteVV (lam : ι → DomWeight n) : Module.Finite K (VV K lam) := Module.Finite.of_basis (bVV K lam)

variable [CharZero K]

variable {K}

end Maps

section Statement

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators
