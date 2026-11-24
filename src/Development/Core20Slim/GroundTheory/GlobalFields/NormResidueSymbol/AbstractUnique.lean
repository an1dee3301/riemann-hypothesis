module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.Abstract
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.IdeleBasis
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.InductiveDimension.Classes
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

noncomputable section

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

def localEmbeddingSubgroup : Subgroup (IdeleGroup K) :=
  (⨆ v : HeightOneSpectrum (𝓞 K), (finiteEmbedding v).range) ⊔
    ⨆ w : InfinitePlace K, (infiniteEmbedding w).range

variable {K}

theorem finiteEmbedding_mem_localEmbeddingSubgroup (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : finiteEmbedding v a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem v ⟨a, rfl⟩)

theorem infiniteEmbedding_mem_localEmbeddingSubgroup (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem w ⟨a, rfl⟩)

theorem exists_mem_localEmbeddingSubgroup_inv_mul_mem {N : Set (IdeleGroup K)} (hN : N ∈ 𝓝 1)
    (x : IdeleGroup K) : ∃ h ∈ localEmbeddingSubgroup K, h⁻¹ * x ∈ N := by
  classical
  obtain ⟨_, ⟨U, V, -, -, hVO, rfl⟩, h1, htN⟩ := (isTopologicalBasis K).mem_nhds_iff.1 hN
  have hU1 : ∀ w, (1 : (w.Completion)ˣ) ∈ U w := fun w ↦ by simpa using h1.1 w
  have hV1 : ∀ v, (1 : (v.adicCompletion K)ˣ) ∈ V v := fun v ↦ by simpa using h1.2 v
  have hS : {v : HeightOneSpectrum (𝓞 K) | ¬ (V v =
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∧
        finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units)}.Finite :=
    eventually_cofinite.1 (hVO.and (eventually_finiteProj_mem_units x))
  set S := hS.toFinset with hSdef
  set h : IdeleGroup K := (∏ w, infiniteEmbedding w (infiniteProj w x)) *
    ∏ v ∈ S, finiteEmbedding v (finiteProj v x) with hhdef
  refine ⟨h, ?_, htN ⟨fun w ↦ ?_, fun v ↦ ?_⟩⟩
  · exact Subgroup.mul_mem _
      (Subgroup.prod_mem _ fun w _ ↦ infiniteEmbedding_mem_localEmbeddingSubgroup _ _)
      (Subgroup.prod_mem _ fun v _ ↦ finiteEmbedding_mem_localEmbeddingSubgroup _ _)
  · have hfi : ∀ (u : HeightOneSpectrum (𝓞 K)) (a : (u.adicCompletion K)ˣ),
        infiniteProj w (finiteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    have hw : infiniteProj w h = infiniteProj w x := by
      simp only [h, map_mul, map_prod, hfi, Finset.prod_const_one, mul_one]
      rw [Finset.prod_eq_single w
          (fun u _ hu ↦ infiniteProj_infiniteEmbedding_of_ne (Ne.symm hu) _)
          (fun hw ↦ (hw (Finset.mem_univ w)).elim)]
      simp
    rw [map_mul, map_inv, hw, inv_mul_cancel]
    exact hU1 w
  · have hif : ∀ (u : InfinitePlace K) (a : (u.Completion)ˣ),
        finiteProj v (infiniteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    by_cases hv : v ∈ S
    · have hv' : finiteProj v h = finiteProj v x := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_single_of_mem v hv
            (fun u _ hu ↦ finiteProj_finiteEmbedding_of_ne (Ne.symm hu) _)]
        simp
      rw [map_mul, map_inv, hv', inv_mul_cancel]
      exact hV1 v
    · have hv' : finiteProj v h = 1 := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_one (fun u hu ↦ finiteProj_finiteEmbedding_of_ne
            (by rintro rfl; exact hv hu) _)]
      have hvS := hv
      rw [hSdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hvS
      rw [map_mul, map_inv, hv', inv_one, one_mul, hvS.1]
      exact hvS.2

theorem dense_localEmbeddingSubgroup : Dense (localEmbeddingSubgroup K : Set (IdeleGroup K)) := by
  refine fun x ↦ mem_closure_iff_nhds.2 fun t ht ↦ ?_
  have hN : {y : IdeleGroup K | x * y⁻¹ ∈ t} ∈ 𝓝 (1 : IdeleGroup K) := by
    have hc : Continuous fun y : IdeleGroup K ↦ x * y⁻¹ := continuous_const.mul continuous_inv
    exact hc.continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨h, hh, hhN⟩ := exists_mem_localEmbeddingSubgroup_inv_mul_mem hN x
  exact ⟨h, by simpa using hhN, hh⟩

theorem continuous_monoidHom_ext {M : Type*} [Monoid M] [TopologicalSpace M] [T2Space M]
    {ψ ψ' : IdeleGroup K →* M} (hψ : Continuous ψ) (hψ' : Continuous ψ')
    (hfin : ∀ v a, ψ (finiteEmbedding v a) = ψ' (finiteEmbedding v a))
    (hinf : ∀ w a, ψ (infiniteEmbedding w a) = ψ' (infiniteEmbedding w a)) : ψ = ψ' := by
  have hle : localEmbeddingSubgroup K ≤ ψ.eqLocus ψ' :=
    sup_le (iSup_le fun v ↦ by rintro _ ⟨a, rfl⟩; exact hfin v a)
      (iSup_le fun w ↦ by rintro _ ⟨a, rfl⟩; exact hinf w a)
  exact MonoidHom.ext (congrFun (Continuous.ext_on dense_localEmbeddingSubgroup hψ hψ' fun x hx ↦ hle hx))

end IdeleGroup

namespace IdeleMap

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  [TopologicalSpace G] [DiscreteTopology G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
  (hφ : ∀ᶠ v in cofinite,
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)

theorem eq_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w))
    {ψ : IdeleGroup K →* G} (hψ : Continuous ψ)
    (hfin : ∀ v, ψ.comp (finiteEmbedding v) = φ v)
    (hinf : ∀ w, ψ.comp (infiniteEmbedding w) = φinf w) :
    ψ = ideleMap φ φinf hφ :=
  continuous_monoidHom_ext hψ (continuous_ideleMap φ φinf hφ hφc hφinfc)
    (fun v a ↦ by rw [ideleMap_finiteEmbedding, ← hfin v, MonoidHom.comp_apply])
    (fun w a ↦ by rw [ideleMap_infiniteEmbedding, ← hinf w, MonoidHom.comp_apply])


end IdeleMap

end

end GroundTheory.Global
