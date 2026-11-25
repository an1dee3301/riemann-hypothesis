module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DifferentiableAtLimitOfDirectionalDerivsConvergeStatement
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

open scoped ContDiff Topology

namespace GlobalTheory

theorem contDiff_of_class_tendstoLocallyUniformly : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  intro E _ _ A _ v c hc P hP
  have key : ∀ φ, P φ → Differentiable ℝ φ ∧ ∃ (α χ : A → E → ℂ), (∀ a, ContDiff ℝ ∞ (α a)) ∧
      (∀ a, P (χ a)) ∧ fderiv ℝ φ =
        fun y => ∑ a, (α a y * φ y + χ a y) • ((c a).smulRight (1 : ℂ)) := by
    intro φ hφ
    obtain ⟨g, hg, hlim, hd⟩ := hP φ hφ
    choose α hα χ hχ hlim' using hd
    have h := GlobalTheory.T.differentiableAt_limit_of_directional_derivs_converge v c hc φ g (fun a y => α a y * φ y + χ a y) hg hlim hlim'
    refine ⟨fun y => (h y).1, α, χ, hα, hχ, ?_⟩
    funext y
    ext x
    conv_lhs => rw [← hc x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, (h y).2, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  have main : ∀ n : ℕ, ∀ φ, P φ → ContDiff ℝ n φ := by
    intro n
    induction n with
    | zero =>
      intro φ hφ
      simpa using (key φ hφ).1.continuous
    | succ n ih =>
      intro φ hφ
      obtain ⟨hd, α, χ, hα, hχ, hf⟩ := key φ hφ
      have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) φ := by
        rw [contDiff_succ_iff_fderiv]
        refine ⟨hd, by simp, ?_⟩
        rw [hf]
        refine ContDiff.sum fun a _ => ?_
        have h1 : ContDiff ℝ n (α a) := (hα a).of_le (by exact_mod_cast le_top)
        exact ((h1.mul (ih φ hφ)).add (ih _ (hχ a))).smul contDiff_const
      exact_mod_cast this
  intro φ hφ
  exact contDiff_infty.2 fun n => main n φ hφ

end GlobalTheory
