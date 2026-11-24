module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZero
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series : ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 := by
  first | exact @GlobalTheory.continuousAt_charSeries_coef_zero | exact GlobalTheory.continuousAt_charSeries_coef_zero | (intros; apply GlobalTheory.continuousAt_charSeries_coef_zero <;> assumption)
