module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.BrPairF

variable {K ι : Type} [Field K] [Fintype ι] {n N : ℕ}

def brPairF (σ : ι → DomWeight n) (hN : N = n + 1) (Λ : ι → DomWeight N) :
    VV K Λ →ₗ[K] (VV K fun τ => (σ τ).dual) →ₗ[K] K :=
  (pairBK σ).compl₁₂ (Formalism.L2.Col.Br.brStd hN Λ σ) (GlobalTheory.FunObj.funEquiv σ).symm.toLinearMap

theorem brPairF_apply (σ : ι → DomWeight n) (hN : N = n + 1) (Λ : ι → DomWeight N) (u : VV K Λ)
    (v : VV K fun τ => (σ τ).dual) :
    brPairF σ hN Λ u v = pairBK σ (Formalism.L2.Col.Br.brStd hN Λ σ u) ((GlobalTheory.FunObj.funEquiv σ).symm v) := rfl

end GlobalTheory.BrPairF

end
