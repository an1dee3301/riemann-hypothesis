module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem map_withDensity_of_jacobian_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (J : E → ℝ) (ψ : E → E) (hψ : Continuous ψ)
    (hb : Function.Bijective ψ)
    (h : ∀ B, ∃ P : E →L[ℝ] E, HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) :
    Measure.map ψ (μ.withDensity fun B => ENNReal.ofReal (J B)) =
      μ.withDensity fun B => ENNReal.ofReal (J B) := by

  choose P hP hJ using h
  have hm : Measurable ψ := hψ.measurable
  ext A hA
  rw [Measure.map_apply hm hA, withDensity_apply _ hA, withDensity_apply _ (hm hA)]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hm hA)
    (fun x _ => (hP x).hasFDerivWithinAt) hb.injective.injOn (fun y => ENNReal.ofReal (J y))
  rw [Set.image_preimage_eq A hb.surjective] at hcv
  rw [hcv]
  refine lintegral_congr (fun x => ?_)
  rw [← ENNReal.ofReal_mul (abs_nonneg _), hJ x]

theorem map_withDensity_of_jacobian : ∀ (p q : ℕ) (J : (Fin p → Fin q → ℂ) → ℝ) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous J → Continuous ψ → Function.Bijective ψ → (∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) → Measure.map ψ (volume.withDensity fun B => ENNReal.ofReal (J B)) = volume.withDensity fun B => ENNReal.ofReal (J B) := by

  intro p q J ψ _ hψ hb h
  haveI hrow : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; infer_instance
  haveI hall : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  exact map_withDensity_of_jacobian_gen (volume : Measure (Fin p → Fin q → ℂ)) J ψ hψ hb h

end GlobalTheory
