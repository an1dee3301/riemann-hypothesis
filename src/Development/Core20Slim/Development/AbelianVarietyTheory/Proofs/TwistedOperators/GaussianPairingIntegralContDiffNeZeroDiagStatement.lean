module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiag
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) →
    (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => ∫ x, Complex.exp (M p.1 x x) * starRingEnd ℂ (Complex.exp (M p.2 x x)) ∂μ) ∧
    ∀ u, ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M u x x)) ∂μ ≠ 0 := by
  first | exact @GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | exact GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | (intros; apply GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero <;> assumption)
