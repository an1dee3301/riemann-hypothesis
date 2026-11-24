module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Order.Real

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory

open scoped Pointwise

theorem lintegral_fundamentalDomain_le_of_meets_orbits
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 ν) (_hS : MeasurableSet S)
    (hmeet : ∀ g, ∃ γ ∈ Γ, γ * g ∈ S) {f : G → ℝ≥0∞} (_hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • S ∩ 𝓕 := by
    intro g hg
    obtain ⟨γ, hγ, hγS⟩ := hmeet g
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩
    refine Set.mem_smul_set.2 ⟨γ * g, hγS, ?_⟩
    show (γ⁻¹ : G) * (γ * g) = g
    group
  calc ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in ⋃ γ : Γ, γ • S ∩ 𝓕, f g ∂ν := lintegral_mono_set hsub
    _ ≤ ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f g ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f (γ⁻¹ • g) ∂ν := by
        refine tsum_congr fun γ => ?_
        congr 1
        funext g
        show f g = f ((γ⁻¹ : Γ) * g)
        exact (hinv _ (γ⁻¹ : Γ).2 g).symm
    _ = ∫⁻ g in S, f g ∂ν := (h𝓕.setLIntegral_eq_tsum' f S).symm

end GlobalTheory
