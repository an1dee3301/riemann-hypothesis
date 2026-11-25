module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim

theorem tendsto_fouInf_div_integral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∀ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets → ∀ t : Ainf F, Filter.Tendsto (fun k => fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) Filter.atTop (nhds 1) := by
  intro F _ _ ψ hψ laminf _ ρ hρ hsupp t
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hg_cont : Continuous fun x : Ainf F => psiInf F ψ (x * t) := by
    have h1 : Continuous fun x : Ainf F => pairA F (x * t) 0 :=
      (continuous_mul_const t).prodMk continuous_const
    exact hψ.1.comp h1
  have hg0 : psiInf F ψ (0 * t) = 1 := by
    have h0 : pairA F (0 * t) 0 = 0 := by
      rw [zero_mul]
      rfl
    show ψ (pairA F (0 * t) 0) = 1
    rw [h0, AddChar.map_zero_eq_one]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hU : (fun x : Ainf F => psiInf F ψ (x * t)) ⁻¹' Metric.ball 1 (ε / 2) ∈ nhds (0 : Ainf F) := by
    apply hg_cont.continuousAt.preimage_mem_nhds
    rw [hg0]
    exact Metric.ball_mem_nhds _ (half_pos hε)
  filter_upwards [Filter.tendsto_smallSets_iff.1 hsupp _ hU] with k hk
  obtain ⟨hc, hcs, hnn, hI⟩ := hρ k
  have hint : Integrable (ρ k) laminf := hc.integrable_of_hasCompactSupport hcs
  have hc1 : Continuous fun x => (ρ k x : ℂ) := Complex.continuous_ofReal.comp hc
  have hcs1 : HasCompactSupport fun x => (ρ k x : ℂ) := hcs.comp_left Complex.ofReal_zero
  have hi1 : Integrable (fun x => (ρ k x : ℂ)) laminf := hc1.integrable_of_hasCompactSupport hcs1
  have hi2 : Integrable (fun x => (ρ k x : ℂ) * psiInf F ψ (x * t)) laminf :=
    (hc1.mul hg_cont).integrable_of_hasCompactSupport
      (hcs1.mul_right (f' := fun x => psiInf F ψ (x * t)))
  have key : fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)
      = ∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf := by
    unfold fouInf
    rw [← integral_complex_ofReal, ← integral_sub hi2 hi1]
    congr 1
    ext x
    ring
  have hIc : ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hI.ne'
  have hsplit : fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) - 1
      = (fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) := by
    rw [sub_div, div_self hIc]
  have hbound : ‖∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf‖ ≤ ∫ x, ρ k x * (ε / 2) ∂laminf := by
    apply norm_integral_le_of_norm_le (hint.mul_const _)
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn x)]
    by_cases hx : x ∈ tsupport (ρ k)
    · have h := hk hx
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
      exact mul_le_mul_of_nonneg_left h.le (hnn x)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [integral_mul_const] at hbound
  rw [dist_eq_norm, hsplit, key, norm_div, Complex.norm_real, Real.norm_of_nonneg hI.le, div_lt_iff₀ hI]
  nlinarith

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim
