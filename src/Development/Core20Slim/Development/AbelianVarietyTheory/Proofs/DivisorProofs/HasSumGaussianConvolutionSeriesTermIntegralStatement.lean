module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumGaussianConvolutionSeriesTermIntegral
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ) (y : E),
    HasSum (fun k => GlobalTheory.ConvSeries.term b c h k y)
      (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.ConvSeries.hasSum_term_integral | exact GlobalTheory.ConvSeries.hasSum_term_integral | (intros; apply GlobalTheory.ConvSeries.hasSum_term_integral <;> assumption)
