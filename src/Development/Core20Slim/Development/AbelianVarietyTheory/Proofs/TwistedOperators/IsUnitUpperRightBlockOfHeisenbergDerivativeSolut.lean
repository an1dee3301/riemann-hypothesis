module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open MeasureTheory

noncomputable section

namespace GlobalTheory.FockFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem isUnit_of_injective_clm (B : V →L[ℝ] V) (h : Function.Injective B) : IsUnit B := by
  have hs : Function.Surjective (B : V →ₗ[ℝ] V) := LinearMap.injective_iff_surjective.mp h
  let e : V ≃ₗ[ℝ] V := LinearEquiv.ofBijective (B : V →ₗ[ℝ] V) ⟨h, hs⟩
  let e' : V ≃L[ℝ] V := e.toContinuousLinearEquiv
  refine ⟨(ContinuousLinearEquiv.unitsEquiv ℝ V).symm e', ?_⟩
  ext x; rfl

theorem dense_pair_ne_zero (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (q x₀ : V) (hx : β x₀ q ≠ 0) :
    Dense {x | β x q ≠ 0} := by
  have hint : interior ((LinearMap.ker (β.flip q) : Submodule ℝ V) : Set V) = ∅ := by
    by_contra hne
    have := Submodule.eq_top_of_nonempty_interior' _ (Set.nonempty_iff_ne_empty.mpr hne)
    apply hx
    have : x₀ ∈ LinearMap.ker (β.flip q) := by rw [this]; trivial
    simpa using this
  have := interior_eq_empty_iff_dense_compl.mp hint
  convert this using 1
  ext x; simp

theorem isUnit_blockB_of_solution (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hβ : ∀ q, (∀ x, β x q = 0) → q = 0)
    (J : (V × V) →ₗ[ℝ] (V × V)) (g : V → ℂ) (hg : Continuous g) (hg0 : g ≠ 0)
    (hJ : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) :
    IsUnit (blockB J) := by
  apply isUnit_of_injective_clm
  refine (injective_iff_map_eq_zero (blockB J)).mpr ?_
  intro q hq
  apply hβ q
  by_contra hne
  push_neg at hne
  obtain ⟨x₀, hx₀⟩ := hne
  have hzero : ∀ x, β x q ≠ 0 → g x = 0 := by
    intro x hx
    have h := hJ (0, q) x
    have h1 : (J (0, q)).1 = 0 := by rw [← blockB_apply]; exact hq
    simp only [GlobalTheory.GaussLine.dHeis, h1, map_zero] at h
    have key : (((β x q : ℝ) : ℂ) + Complex.I * ((β x (J (0, q)).2 : ℝ) : ℂ)) * g x = 0 := by
      have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
        have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      have h2 : (2 * Real.pi : ℂ) * ((((β x q : ℝ) : ℂ) + Complex.I * ((β x (J (0, q)).2 : ℝ) : ℂ)) * g x) = 0 := by
        linear_combination (-1 : ℂ) * h + (2 * Real.pi * ((β x q : ℝ) : ℂ) * g x) * Complex.I_sq
      exact (mul_eq_zero.mp h2).resolve_left hpi
    rcases mul_eq_zero.mp key with h3 | h3
    · exfalso; apply hx
      have := congrArg Complex.re h3
      simpa using this
    · exact h3
  apply hg0
  have hd := dense_pair_ne_zero β q x₀ hx₀
  exact Continuous.ext_on hd hg continuous_const (fun x hx => hzero x hx)
