module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSeriesUniformTube
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_series_uniform_tube : ∀ (ι X T : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] [TopologicalSpace T]
    (t : ι → ℂ × ℂ → T → X) (Ω : Set (ℝ × ℝ)),
    (∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g) →
    (∀ r, Continuous fun y : (ℂ × ℂ) × T => t r y.1 y.2) →
    (∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : ι → ℝ, Summable u ∧
      ∀ l ∈ PositivityTheory.RgEis.tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r) →
    PositivityTheory.RgEis.TubeGood (fun l g => ∑' r, t r l g) Ω ∧
      ∀ l ∈ PositivityTheory.RgEis.tube Ω, ∀ g, Summable fun r => ‖t r l g‖ := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum | exact GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum <;> assumption)
