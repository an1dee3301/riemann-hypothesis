module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Init.Core
public import Init.Data.Function
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem lowerIntegral_to_integral_coords : ∀ (X U Y : Type) [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace Y] (G : Type) [MeasurableSpace G] (ν : Measure X) (νU : Measure U) (μ : Measure Y) [SFinite νU] [SFinite μ] (i : X → G) (p : U → Y → G) (Inv : (G → G) → Prop), Measurable i → Measurable (Function.uncurry p) → ∀ (Dom : Set G), (∀ f : G → ENNReal, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → ∫⁻ x, f (i x) ∂ν = ∫⁻ u, ∫⁻ y, f (p u y) ∂μ ∂νU) → ∀ f : G → ℂ, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → Integrable (fun x => f (i x)) ν → Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) ∧ ∫ x, f (i x) ∂ν = ∫ u, ∫ y, f (p u y) ∂μ ∂νU := by
  intro X U Y _ _ _ G _ ν νU μ _ _ i p Inv hi hp Dom H f hf hinv hfi
  have hpm : Measurable (fun q : U × Y => p q.1 q.2) := hp

  have hprod : ∀ g : G → ENNReal, Measurable g → (∀ t, Inv t → ∀ n ∈ Dom, g (t n) = g n) →
      ∫⁻ x, g (i x) ∂ν = ∫⁻ q, g (p q.1 q.2) ∂(νU.prod μ) := by
    intro g hg hgi
    rw [H g hg hgi, lintegral_prod (fun q : U × Y => g (p q.1 q.2)) (hg.comp hpm).aemeasurable]
  have hint : Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) := by
    refine ⟨(hf.comp hpm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have := hprod (fun n => ‖f n‖ₑ) hf.enorm (fun t ht n hn => by simp only [hinv t ht n hn])
    rw [← this]
    exact hfi.2
  refine ⟨hint, ?_⟩
  rw [← integral_prod _ hint]

  have hreal : ∀ g : G → ℝ, Measurable g → (∀ t, Inv t → ∀ n ∈ Dom, g (t n) = g n) →
      Integrable (fun x => g (i x)) ν → Integrable (fun q : U × Y => g (p q.1 q.2)) (νU.prod μ) →
      ∫ x, g (i x) ∂ν = ∫ q, g (p q.1 q.2) ∂(νU.prod μ) := by
    intro g hg hgi h1 h2
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2]
    have e1 := hprod (fun n => ENNReal.ofReal (g n)) (ENNReal.measurable_ofReal.comp hg)
      (fun t ht n hn => by simp only [hgi t ht n hn])
    have e2 := hprod (fun n => ENNReal.ofReal (- g n)) (ENNReal.measurable_ofReal.comp hg.neg)
      (fun t ht n hn => by simp only [hgi t ht n hn])
    rw [e1, e2]
  apply Complex.ext
  · have a := integral_re hfi; have b := integral_re hint
    simp only [RCLike.re_to_complex] at a b
    rw [← a, ← b]
    exact hreal (fun n => (f n).re) (Complex.measurable_re.comp hf)
      (fun t ht n hn => by simp only [hinv t ht n hn]) hfi.re hint.re
  · have a := integral_im hfi; have b := integral_im hint
    simp only [RCLike.im_to_complex] at a b
    rw [← a, ← b]
    exact hreal (fun n => (f n).im) (Complex.measurable_im.comp hf)
      (fun t ht n hn => by simp only [hinv t ht n hn]) hfi.im hint.im

end GlobalTheory
