module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLiftCont

theorem continuous_integral_of_cocompact {G H : Type*} [TopologicalSpace G] [LocallyCompactSpace G]
    [FirstCountableTopology G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K : G → H → ℂ)
    (hK : Continuous fun p : G × H => K p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ g h, K g (γ * h) = K g h) :
    Continuous fun g => ∫ h in 𝓕, K g h ∂μ := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds g₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hK.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕) := by
    exact hconst.re
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ hconst' ?_
  · refine Filter.Eventually.of_forall fun g => ?_
    exact (hK.comp (Continuous.prodMk_right g)).aestronglyMeasurable
  · filter_upwards [hN₀] with g hg
    refine Filter.Eventually.of_forall fun h => ?_
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hinv γ hγ]
    exact hM (g, c) ⟨hg, hc⟩
  · refine Filter.Eventually.of_forall fun h => ?_
    exact (hK.comp (Continuous.prodMk_left h)).continuousAt


end GlobalTheory.DefLiftCont
