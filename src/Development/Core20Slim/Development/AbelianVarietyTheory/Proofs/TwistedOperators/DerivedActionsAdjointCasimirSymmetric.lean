module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FockTensor

theorem derived_adjoint_and_casimir (p q : ℕ) (T : GrpData p q) (πU : URep T) (V₁ V₂ : Type)
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V₁) (a₂ : Mat p q →ₗ[ℂ] Module.End ℂ V₂)
    (E₁ : V₁ →ₗ[ℂ] πU.H) (E₂ : V₂ →ₗ[ℂ] πU.H)
    (h₁ : ∀ Y ∈ upq p q, ∀ x,
      HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E₁ x)) (E₁ (a₁ Y x)) 0)
    (h₂ : ∀ Y ∈ upq p q, ∀ y,
      HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E₂ y)) (E₂ (a₂ Y y)) 0) :
    (∀ Z x y, inner ℂ (E₁ (a₁ Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (a₂ (adjZ Z) y))) ∧
      ∀ x y, inner ℂ (E₁ (casimir a₁ x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (casimir a₂ y)) := by
  have hreal : ∀ Y ∈ upq p q, ∀ x y,
      inner ℂ (E₁ (a₁ Y x)) (E₂ y) = - inner ℂ (E₁ x) (E₂ (a₂ Y y)) := by
    intro Y hY x y
    have h := (h₁ Y hY x).inner ℂ (h₂ Y hY y)
    simp only [inner_pi_pi] at h
    have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
    simp only [zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h0
    linear_combination h0
  have hZ : ∀ Z x y, inner ℂ (E₁ (a₁ Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (a₂ (adjZ Z) y)) := by
    intro Z x y
    obtain ⟨X, hX, Y, hY, rfl⟩ := exists_upq_add Z
    rw [adjZ_add, adjZ_smul, (mem_upq_iff X).1 hX, (mem_upq_iff Y).1 hY]
    simp only [map_add (f := _), map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_neg_right, hreal X hX, hreal Y hY]
    rfl
  refine ⟨hZ, fun x y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [casimir, LinearMap.sum_apply, map_sum, sum_inner, inner_sum, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hZ, hZ, adjZ_Eab, adjZ_Eab]
  simp only [map_smul, LinearMap.smul_apply, inner_smul_right]
  linear_combination (sgnIx b * sgnIx b * inner ℂ (E₁ x) (E₂ (a₂ (Eab a b) (a₂ (Eab b a) y)))) *
    sgnIx_mul_self a + inner ℂ (E₁ x) (E₂ (a₂ (Eab a b) (a₂ (Eab b a) y))) * sgnIx_mul_self b

end GlobalTheory.FockTensor
