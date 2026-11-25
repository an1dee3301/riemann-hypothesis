module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuotientMeasureTower
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_measure_tower : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕 : Set G) (𝓕₁ : Set G₁), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (Q : Type) [Countable Q] (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ u ∈ Γ₁, ∀ g, φ (ι u * g) = φ g) → ∫⁻ h in 𝓕, ∑' q, φ (r q * h) ∂μ = ∫⁻ h in 𝓕, ∑' q, (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * (r q * h)) ∂μ₁ ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_average | exact GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_average | (intros; apply GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_average <;> assumption)
