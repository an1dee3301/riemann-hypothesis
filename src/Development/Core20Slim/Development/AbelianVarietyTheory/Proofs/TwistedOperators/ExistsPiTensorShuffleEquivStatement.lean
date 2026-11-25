module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorShuffleEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_piTensor_tmul_piTensor_linearEquiv_piTensor_tmul : ∀ (ι : Type) [Fintype ι] (F V : ι → Type) [∀ τ, AddCommGroup (F τ)] [∀ τ, Module ℂ (F τ)] [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)], ∃ e : ((⨂[ℂ] τ, F τ) ⊗[ℂ] (⨂[ℂ] τ, V τ)) ≃ₗ[ℂ] (⨂[ℂ] τ, (F τ ⊗[ℂ] V τ)), ∀ (f : ∀ τ, F τ) (v : ∀ τ, V τ), e (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (fun τ => f τ ⊗ₜ[ℂ] v τ) := by
  first | exact @GlobalTheory.exists_piTensor_shuffle_equiv | exact GlobalTheory.exists_piTensor_shuffle_equiv | (intros; apply GlobalTheory.exists_piTensor_shuffle_equiv <;> assumption)
