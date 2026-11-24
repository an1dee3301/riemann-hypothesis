module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory

namespace GlobalTheory


open MeasureTheory in
theorem _root_.GlobalTheory.mean_periodic_indep_of_covolume_one :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (μ μ' : Measure G) (𝓕 𝓕' : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → μ'.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕' μ' → μ' 𝓕' = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ∫ x in 𝓕', Φ x ∂μ' := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov μ μ' 𝓕 𝓕' hμ h𝓕 h𝓕1 hμ' h𝓕' h𝓕'1 Φ hΦ hper
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖Φ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hK.image hΦ.norm).bddAbove
    refine ⟨M, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hcov x
    rw [← hper γ hγ x]
    exact hM ⟨_, hx, rfl⟩
  have hint : IntegrableOn Φ 𝓕 μ :=
    Measure.integrableOn_of_bounded (by rw [h𝓕1]; exact ENNReal.one_ne_top)
      hΦ.aestronglyMeasurable (M := M) (Filter.Eventually.of_forall hM)
  refine ⟨hint, ?_⟩
  have hsm := Measure.isAddLeftInvariant_eq_smul μ' μ
  have hc0 : μ'.addHaarScalarFactor μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsm
    rw [hsm] at h𝓕'1
    simp at h𝓕'1
  have hac : μ ≪ μ' := by
    intro s hs
    rw [hsm, Measure.smul_apply] at hs
    simpa [hc0] using hs
  have h𝓕'μ : IsAddFundamentalDomain Γ 𝓕' μ := h𝓕'.mono hac
  have hc1 : μ'.addHaarScalarFactor μ = 1 := by
    have e := h𝓕'1
    rw [hsm, Measure.smul_apply, h𝓕'μ.measure_eq h𝓕, h𝓕1] at e
    simpa using e
  have hμμ' : μ' = μ := by rw [hsm, hc1, one_smul]
  rw [hμμ']
  exact h𝓕.setIntegral_eq h𝓕'μ (fun g x => hper g g.2 x)

end GlobalTheory
