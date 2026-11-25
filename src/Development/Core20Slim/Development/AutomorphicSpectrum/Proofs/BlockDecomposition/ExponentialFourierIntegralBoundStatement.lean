module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialFourierIntegralBound
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_fourier_integral_bound : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (φ : ℝ × ℝ → X) (l : ℂ × ℂ) (ε M : ℝ), 0 < ε → Continuous φ → (∀ t : ℝ × ℝ, ‖φ t‖ ≤ M * Real.exp (-rdot (l.1.re, l.2.re) t) * Real.exp (-ε * (|t.1| + |t.2|))) → Integrable (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) ∧ ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖ ≤ M * (2 / ε) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.integrable_and_norm_integral_le | exact GlobalTheory.CompanionTheory.TubeFourier.integrable_and_norm_integral_le | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.integrable_and_norm_integral_le <;> assumption)
