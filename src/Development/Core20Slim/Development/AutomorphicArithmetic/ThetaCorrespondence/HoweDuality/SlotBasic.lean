module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.PartStable
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation

@[expose] public section

open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.slotFacts :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι), (⨆ r : M₀ × (∀ j, M j), LinearMap.range (intersection_update_fsHerm_neg_one i r)) = ⊤ ∧ ∀ (g : Module.End ℂ (M i)) (r : M₀ × (∀ j, M j)) (x : M i), factorOp i g (intersection_update_fsHerm_neg_one i r x) = intersection_update_fsHerm_neg_one i r (g x) := by
  intro ι _ _ M₀ _ _ M _ _ i
  refine ⟨?_, ?_⟩
  · rw [Submodule.eq_top_iff']
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul x₀ w =>
      induction w using PiTensorProduct.induction_on with
      | smul_tprod c y =>
        rw [TensorProduct.tmul_smul]
        refine Submodule.smul_mem _ c ?_
        refine Submodule.mem_iSup_of_mem (x₀, y) ⟨y i, ?_⟩
        rw [position_apply]
        simp only [Function.update_eq_self]
      | add a b ha hb =>
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ha hb
  · intro g r x
    rw [position_apply, position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
