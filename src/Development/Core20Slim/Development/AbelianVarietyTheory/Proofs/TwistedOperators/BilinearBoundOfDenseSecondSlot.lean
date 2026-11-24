module

public import Mathlib
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Order.Hom.GroupNorm
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Bases
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.UniformEmbedding

@[expose] public section

open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem bilinear_bound_of_dense_right : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by
  intro E _ _ _ _ _ _ p hp X₁ X₂ _ _ _ _ j₁ j₂ hinj hcl D₂ hdense F h₁ h₂ b i
  haveI : ContinuousSMul ℂ E := hp.continuousSMul
  haveI : FirstCountableTopology E := hp.firstCountableTopology
  haveI : PolynormableSpace ℂ E := hp.toPolynormableSpace
  haveI : IsTopologicalAddGroup E := inferInstance
  set Y : Submodule ℂ E := LinearMap.range j₁ with hYdef
  have hYc : IsClosed (Y : Set E) := by simpa [Y, LinearMap.coe_range] using hcl
  haveI : IsUniformAddGroup Y := Y.toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace Y := hYc.completeSpace_coe
  haveI : FirstCountableTopology Y := Topology.IsInducing.subtypeVal.firstCountableTopology
  haveI : (𝓤 Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : BarrelledSpace ℂ Y := inferInstance
  let e : X₁ ≃ₗ[ℂ] Y := LinearEquiv.ofInjective j₁ hinj
  have he : ∀ w, ((e w : Y) : E) = j₁ w := fun w => rfl

  let gl : D₂ → Y →ₗ[ℂ] E := fun a => (F.flip (a : X₂)).comp e.symm.toLinearMap
  have hgl : ∀ a y, gl a y = F (e.symm y) a := fun a y => rfl
  have hgc : ∀ a, Continuous (gl a) := by
    intro a
    refine hp.continuous_of_continuous_comp (gl a) fun k => ?_
    obtain ⟨q, hq, hle⟩ := h₂ a a.2 k
    refine Seminorm.continuous_of_le (q := q.comp Y.subtype) (hq.comp continuous_subtype_val) ?_
    intro y
    have := hle (e.symm y)
    rw [← he, e.apply_symm_apply] at this
    simpa [Seminorm.comp_apply, hgl] using this
  let g : D₂ → Y →L[ℂ] E := fun a => ⟨gl a, hgc a⟩
  let l : Filter D₂ := Filter.comap (fun a : D₂ => j₂ a) (𝓝 (j₂ b))
  haveI : l.NeBot := by
    rw [Filter.comap_neBot_iff]
    intro t ht
    obtain ⟨_, htx, ⟨a, ha, rfl⟩⟩ := mem_closure_iff_nhds.mp (hdense b) t ht
    exact ⟨⟨a, ha⟩, htx⟩
  have hT : Tendsto (fun a y => g a y) l (𝓝 fun y => F (e.symm y) b) := by
    rw [tendsto_pi_nhds]
    intro y
    rw [hp.tendsto_nhds]
    intro k ε hε
    obtain ⟨q, hq, hle⟩ := h₁ (e.symm y) k
    have ht : Tendsto (fun a : D₂ => q (j₂ a - j₂ b)) l (𝓝 0) := by
      have h0 : Tendsto (fun a : D₂ => j₂ a - j₂ b) l (𝓝 (j₂ b - j₂ b)) :=
        tendsto_comap.sub tendsto_const_nhds
      have := (hq.tendsto _).comp h0
      simpa [Function.comp_def] using this
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with a ha
    calc p k (g a y - F (e.symm y) b) = p k (F (e.symm y) ((a : X₂) - b)) := by
          simp [g, hgl, map_sub]
      _ ≤ q (j₂ ((a : X₂) - b)) := hle _
      _ < ε := by simpa [map_sub] using ha
  let G : Y →L[ℂ] E := continuousLinearMapOfTendsto g hT
  have hG : ∀ y, G y = F (e.symm y) b := fun y => rfl
  have hr : Continuous ((p i).comp G.toLinearMap) := (hp.continuous_seminorm i).comp G.continuous
  obtain ⟨q, hq, hle⟩ := Seminorm.exists_le_comp_of_isInducing hr (f := Y.subtype) .subtypeVal
  refine ⟨q, hq, fun w => ?_⟩
  have := hle (e w)
  simpa [Seminorm.comp_apply, hG, he] using this

end GlobalTheory
