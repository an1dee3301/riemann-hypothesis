module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Function.Basic

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_tprod_of_commute_at_each_place : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V W : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (R : ∀ τ, Set ((V τ →ₗ[ℂ] V τ) × (W τ →ₗ[ℂ] W τ))) (Q : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ W), (∀ τ, ∀ p ∈ R τ, Q ∘ₗ PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : V σ →ₗ[ℂ] V σ)) τ p.1) = PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : W σ →ₗ[ℂ] W σ)) τ p.2) ∘ₗ Q) → Q ∈ Submodule.span ℂ {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] W τ, (∀ τ, ∀ p ∈ R τ, t τ ∘ₗ p.1 = p.2 ∘ₗ t τ) ∧ T = PiTensorProduct.map t} := by
  first | exact @GlobalTheory.PiTensorCommute.mem_span_map_of_commute | exact GlobalTheory.PiTensorCommute.mem_span_map_of_commute | (intros; apply GlobalTheory.PiTensorCommute.mem_span_map_of_commute <;> assumption)
