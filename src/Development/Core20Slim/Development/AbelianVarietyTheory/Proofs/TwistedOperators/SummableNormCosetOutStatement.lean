module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNormCosetOut
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_norm_coset_out' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G), IsOpen (K : Set G) → μ K = 1 → ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) → Integrable F μ → Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  first | exact @GlobalTheory.summable_norm_coset_out | exact GlobalTheory.summable_norm_coset_out | (intros; apply GlobalTheory.summable_norm_coset_out <;> assumption)
