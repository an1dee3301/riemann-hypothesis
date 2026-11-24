module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Equicontinuity

@[expose] public section

open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem schwartz_tendsto_apply_of_tendsto_pointwise :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  intro V _ _ _ S hS g g₀ hg
  haveI : BarrelledSpace ℂ (SchwartzMap V ℂ) := schwartzMap_barrelledSpace V
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  have hq := schwartz_withSeminorms ℂ V ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ fun n => S (u n)) := by
    refine hq.banach_steinhaus (𝓕 := fun n => S (u n)) ?_
    intro k f
    exact ((hq.continuous_seminorm k).tendsto f).comp ((hS f).comp hu) |>.bddAbove_range
  have hE := hUE.equicontinuous g₀
  have h1 : Tendsto (fun n => (S (u n) g₀, S (u n) (g (u n)))) atTop (𝓤 (SchwartzMap V ℂ)) := by
    intro U hU
    have := (hg.comp hu).eventually (hE U hU)
    rw [Filter.mem_map]
    exact this.mono fun n hn => hn n
  exact ((hS g₀).comp hu).congr_uniformity h1

end GlobalTheory
