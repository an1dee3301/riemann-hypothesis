module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Max
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem schwartz_iteratedFDeriv_tendsto_zero_cocompact
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (j : ℕ) :
    Tendsto (fun z => iteratedFDeriv ℝ j f z) (cocompact E) (𝓝 0) := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  obtain ⟨C, -, hC⟩ := f.decay 1 j
  have hn : Tendsto (fun z : E => ‖z‖) (cocompact E) atTop := by first | exact tendsto_norm_cocompact_atTop | exact tendsto_norm_cocompact_atTop _
  have h0 : Tendsto (fun z : E => C / ‖z‖) (cocompact E) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [hn.eventually_gt_atTop 0] with z hz
  rw [le_div_iff₀ hz, mul_comm]
  simpa using hC z

end GlobalTheory
