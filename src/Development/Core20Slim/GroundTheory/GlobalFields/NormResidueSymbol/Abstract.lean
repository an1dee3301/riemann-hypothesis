module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.IdeleBasis
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.Restricted
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Prod
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
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

noncomputable section

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

theorem eventually_finiteProj_mem_units (x : IdeleGroup K) :
    ∀ᶠ v in cofinite, finiteProj v x ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  filter_upwards [(prodRestrictedEquiv K x).2.2] with v hv
  rw [finiteProj_eq]
  exact hv

end IdeleGroup

namespace IdeleMap

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)

theorem hasFiniteMulSupport
    (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
    (x : IdeleGroup K) :
    Function.HasFiniteMulSupport fun v ↦ φ v (finiteProj v x) := by
  have h : ∀ᶠ v in cofinite, φ v (finiteProj v x) = 1 := by
    filter_upwards [hφ, eventually_finiteProj_mem_units x] with v hv hx
    exact hv hx
  exact eventually_cofinite.1 h

def ideleMap
    (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker) :
    IdeleGroup K →* G where
  toFun x := (∏ᶠ v, φ v (finiteProj v x)) * ∏ w, φinf w (infiniteProj w x)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    rw [finprod_mul_distrib (hasFiniteMulSupport φ hφ x) (hasFiniteMulSupport φ hφ y),
      Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _

variable (hφ : ∀ᶠ v in cofinite,
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)

theorem ideleMap_apply (x : IdeleGroup K) :
    ideleMap φ φinf hφ x = (∏ᶠ v, φ v (finiteProj v x)) * ∏ w, φinf w (infiniteProj w x) :=
  rfl

@[simp]
theorem ideleMap_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ideleMap φ φinf hφ (finiteEmbedding v a) = φ v a := by
  rw [ideleMap_apply, finprod_eq_single _ v fun u hu ↦ by
    rw [finiteProj_finiteEmbedding_of_ne hu, map_one]]
  have h : ∀ w, infiniteProj w (finiteEmbedding v a) = 1 := fun w ↦ Units.ext rfl
  simp [h]

@[simp]
theorem ideleMap_infiniteEmbedding (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleMap φ φinf hφ (infiniteEmbedding w a) = φinf w a := by
  rw [ideleMap_apply, Finset.prod_eq_single w (fun u _ hu ↦ by
    rw [infiniteProj_infiniteEmbedding_of_ne hu, map_one]) (fun h ↦ (h (Finset.mem_univ w)).elim)]
  have h : ∀ v, finiteProj v (infiniteEmbedding w a) = 1 := fun v ↦ Units.ext rfl
  simp [h]

theorem ideleMap_eq_one_of_forall_mem
    (N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (Ninf : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
    (hN : ∀ v, N v ≤ (φ v).ker) (hNinf : ∀ w, Ninf w ≤ (φinf w).ker) {x : IdeleGroup K}
    (hx : ∀ v, finiteProj v x ∈ N v) (hxinf : ∀ w, infiniteProj w x ∈ Ninf w) :
    ideleMap φ φinf hφ x = 1 := by
  rw [ideleMap_apply, finprod_eq_one_of_forall_eq_one fun v ↦ hN v (hx v),
    Finset.prod_eq_one fun w _ ↦ hNinf w (hxinf w), mul_one]

variable [TopologicalSpace G] [DiscreteTopology G]

theorem continuous_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) :
    Continuous (ideleMap φ φinf hφ) := by
  have hker : ∀ {X : Type _} [TopologicalSpace X] [Group X] (f : X →* G), Continuous f →
      IsOpen (f.ker : Set X) := fun f hf ↦ by
    rw [MonoidHom.coe_ker]
    exact (isOpen_discrete ({1} : Set G)).preimage hf
  set V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ := fun v ↦
    ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∩
      ((φ v).ker : Set (v.adicCompletion K)ˣ) with hVdef
  set W : Set (IdeleGroup K) :=
    {x | (∀ w, infiniteProj w x ∈ ((φinf w).ker : Set (w.Completion)ˣ)) ∧
      ∀ v, finiteProj v x ∈ V v} with hWdef
  have hWo : IsOpen W := (isTopologicalBasis K).isOpen
    ⟨fun w ↦ ((φinf w).ker : Set (w.Completion)ˣ), V, fun w ↦ hker _ (hφinfc w),
      fun v ↦ (isOpen_units_adicCompletionIntegers K v).inter (hker _ (hφc v)),
      hφ.mono fun v hv ↦ Set.inter_eq_left.2 (SetLike.coe_subset_coe.2 hv), rfl⟩
  have h1W : (1 : IdeleGroup K) ∈ W :=
    ⟨fun w ↦ by simp, fun v ↦ by simp [V]⟩
  have hψW : ∀ x ∈ W, ideleMap φ φinf hφ x = 1 := fun x hx ↦
    ideleMap_eq_one_of_forall_mem φ φinf hφ (fun v ↦ (φ v).ker) (fun w ↦ (φinf w).ker)
      (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) (fun v ↦ (hx.2 v).2) hx.1
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one, nhds_discrete G, tendsto_pure]
  exact eventually_of_mem (hWo.mem_nhds h1W) hψW

end IdeleMap

end

end GroundTheory.Global
