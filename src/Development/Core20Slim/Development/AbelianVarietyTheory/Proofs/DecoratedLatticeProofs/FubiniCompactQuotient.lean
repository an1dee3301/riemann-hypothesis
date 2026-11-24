module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Init.Core
public import Init.Data.Function
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped Pointwise

namespace GlobalTheory

theorem fubini_compact_quotient : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] (Γ : Subgroup H), Countable Γ → DiscreteTopology Γ → (∃ K : Set H, IsCompact K ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 μ → ∀ (X : Type) [MeasurableSpace X] (m : Measure X) [SFinite m] (f : H → X → ℂ), Measurable (Function.uncurry f) → (∀ γ ∈ Γ, ∀ h x, f (γ * h) x = f h x) → (∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ h ∈ K, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B) → Integrable (Function.uncurry f) ((μ.restrict 𝓕).prod m) := by
  intro H _ _ _ _ _ _ _ _ μ _ Γ hΓc hΓd hK 𝓕 h𝓕 X _ m _ f hf hinv hB
  obtain ⟨K, hKc, hKcov⟩ := hK
  obtain ⟨B, hB⟩ := hB K hKc
  haveI : Countable Γ := hΓc

  have hbd : ∀ h, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B := by
    intro h
    obtain ⟨γ, hγ, hk⟩ := hKcov h
    have := hB _ hk
    simpa only [hinv γ hγ h] using this

  have hfin : μ 𝓕 < ⊤ := by
    have hcover : 𝓕 ⊆ ⋃ g : Γ, (g • K) := by
      intro h _
      obtain ⟨γ, hγ, hk⟩ := hKcov h
      refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
      refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
      simp [Subgroup.smul_def]
    have hle : μ 𝓕 ≤ μ K := by
      calc μ 𝓕 = μ ((⋃ g : Γ, (g • K)) ∩ 𝓕) := by
              rw [Set.inter_eq_right.2 hcover]
        _ = μ (⋃ g : Γ, (g • K ∩ 𝓕)) := by rw [Set.iUnion_inter]
        _ ≤ ∑' g : Γ, μ (g • K ∩ 𝓕) := measure_iUnion_le _
        _ = μ K := (h𝓕.measure_eq_tsum K).symm
    exact hle.trans_lt hKc.measure_lt_top
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hm : AEMeasurable (fun z : H × X => ‖Function.uncurry f z‖ₑ) ((μ.restrict 𝓕).prod m) :=
    hf.enorm.aemeasurable
  rw [HasFiniteIntegral, lintegral_prod _ hm]
  calc ∫⁻ h, ∫⁻ x, ‖Function.uncurry f (h, x)‖ₑ ∂m ∂(μ.restrict 𝓕)
      ≤ ∫⁻ _, (B : ENNReal) ∂(μ.restrict 𝓕) := lintegral_mono (fun h => hbd h)
    _ = B * μ 𝓕 := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin

end GlobalTheory
