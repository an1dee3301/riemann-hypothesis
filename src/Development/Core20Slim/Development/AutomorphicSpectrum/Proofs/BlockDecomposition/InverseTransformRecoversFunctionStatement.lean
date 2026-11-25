module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseTransformRecoversFunction
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_transform_recovers_function : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (G : ℂ × ℂ → X) (x : ℝ × ℝ), Continuous (fun y => G (pt x y)) → (∃ M : ℝ, ∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) → Continuous (phi G x) → (∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))) → ∀ y : ℝ × ℝ, inv (phi G x) (pt x y) = G (pt x y) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq | exact GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq <;> assumption)
