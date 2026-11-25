module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianTubeTransformBound
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_tube_transform_bound : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (G : ℂ × ℂ → X) (x : ℝ × ℝ) (M : ℝ), (∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) → ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.pi * Real.exp (-rdot x t) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.norm_phi_le | exact GlobalTheory.CompanionTheory.TubeFourier.norm_phi_le | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.norm_phi_le <;> assumption)
