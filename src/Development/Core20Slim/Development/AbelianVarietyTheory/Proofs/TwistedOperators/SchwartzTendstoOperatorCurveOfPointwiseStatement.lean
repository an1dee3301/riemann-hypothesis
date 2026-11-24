module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwise
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
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
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_tendsto_operatorCurve_of_pointwise : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  first | exact @GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise | exact GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise | (intros; apply GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise <;> assumption)
