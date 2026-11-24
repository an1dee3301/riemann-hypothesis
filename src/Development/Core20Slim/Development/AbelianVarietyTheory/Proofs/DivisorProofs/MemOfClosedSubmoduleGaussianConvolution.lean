module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianMulMultilinearDiagonalMemSchwartzSubmoduStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumGaussianConvolutionSeriesTermIntegralStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSeminormGaussianConvolutionSeriesTermStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminormsStatement
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
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
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Bornology.BoundedOperation
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.ConvSeries

theorem mem_of_conv_gaussian : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
      u ∈ M := by
  intro E _ _ _ _ _ M hM hℓ b c hb hc hg h u hu
  have ht : ∀ j, ∃ t ∈ M, ∀ y, t y = term b c h j y := by
    intro j
    obtain ⟨t, htM, ht⟩ := GlobalTheory.T.gaussian_mul_multilinear_diagonal_mem_schwartzSubmodule E M hℓ c hc hg j (coef b c h j)
    refine ⟨(((2 * c) ^ j / (j.factorial : ℝ) : ℝ) : ℂ) • t, M.smul_mem _ htM, fun y => ?_⟩
    simp only [SchwartzMap.smul_apply, ht, term, smul_eq_mul]
    ring
  choose t htM hty using ht
  have hs : Summable t := GlobalTheory.T.summable_schwartz_of_summable_seminorms E t (GlobalTheory.T.summable_seminorm_gaussianConvolutionSeriesTerm E b c hb hc h t hty)
  have hL := hs.hasSum
  have hev : ∀ y, (∑' j, t j) y = u y := by
    intro y
    let φ : SchwartzMap E ℂ →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ)
    have h1 : HasSum (fun j => t j y) ((∑' j, t j) y) := hL.mapL φ
    have h2 : HasSum (fun j => t j y) (u y) := by
      rw [hu y]
      exact (GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral E b c hb hc h y).congr_fun (fun j => hty j y)
    exact h1.unique h2
  have hLu : (∑' j, t j) = u := SchwartzMap.ext hev
  rw [← hLu]
  exact hM.mem_of_tendsto hL (Eventually.of_forall fun s => M.sum_mem fun j _ => htM j)

end GlobalTheory.ConvSeries
