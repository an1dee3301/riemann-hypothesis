module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinset
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tprod_complement_split_finset : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι), Summable (fun v => |a v - 1|) → S ⊆ S' → ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut | exact GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut | (intros; apply GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut <;> assumption)
