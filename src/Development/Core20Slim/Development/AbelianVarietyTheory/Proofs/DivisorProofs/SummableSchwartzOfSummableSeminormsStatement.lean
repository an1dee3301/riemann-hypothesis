module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzOfSummableSeminorms
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_schwartz_of_summable_seminorms : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℕ → SchwartzMap E ℂ),
    (∀ k n, Summable (fun j => SchwartzMap.seminorm ℂ k n (t j))) → Summable t := by
  first | exact @GlobalTheory.ConvSeries.summable_of_summable_seminorm | exact GlobalTheory.ConvSeries.summable_of_summable_seminorm | (intros; apply GlobalTheory.ConvSeries.summable_of_summable_seminorm <;> assumption)
