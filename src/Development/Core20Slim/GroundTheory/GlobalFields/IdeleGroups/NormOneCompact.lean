module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.UnitBound
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

namespace IdeleGroup

theorem exists_finset_mul_mem_standardOpenSubgroup :
    ∃ R : Finset (IdeleGroup K), ∀ x : IdeleGroup K, ∃ k : Kˣ, ∃ r ∈ R,
      diagonal K k * x * r⁻¹ ∈ standardOpenSubgroup K := by
  classical
  let s : ClassGroup (𝓞 K) → IdeleGroup K := Function.invFun toClassGroup
  refine ⟨Finset.univ.image s, fun x ↦ ?_⟩
  have hs : toClassGroup (s (toClassGroup x)) = toClassGroup x :=
    Function.invFun_eq (toClassGroup_surjective _)
  have hmem : x * (s (toClassGroup x))⁻¹ ∈ (diagonal K).range ⊔ standardOpenSubgroup K := by
    rw [← ker_toClassGroup, MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
  obtain ⟨_, ⟨k, rfl⟩, u, hu, hku⟩ := Subgroup.mem_sup.1 hmem
  refine ⟨k⁻¹, s (toClassGroup x), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  rw [map_inv, mul_assoc, ← hku, inv_mul_cancel_left]
  exact hu

theorem exists_isCompact_of_finset (R : Finset (IdeleGroup K))
    (hR : ∀ x : IdeleGroup K, ∃ k : Kˣ, ∃ r ∈ R,
      diagonal K k * x * r⁻¹ ∈ standardOpenSubgroup K) :
    ∃ D : Set (IdeleGroup K), IsCompact D ∧
      ∀ x ∈ normOneSubgroup K, ∃ k : Kˣ, diagonal K k * x ∈ D := by
  obtain ⟨M, hM⟩ := exists_unit_forall_abs_log_le (K := K)
    (∑ r ∈ R, |Real.log (ideleModule K r : ℝ)|)
  let S := {x : IdeleGroup K | (∀ w : InfinitePlace K, |Real.log ‖(x : 𝔸[K]).1 w‖| ≤ M) ∧
    x ∈ standardOpenSubgroup K}
  refine ⟨⋃ r ∈ R, (fun s ↦ s * r) '' S, R.isCompact_biUnion fun r _ ↦
    (isCompact_abs_log_le_inter_standardOpenSubgroup K M).image
      (continuous_id.mul continuous_const), fun x hx ↦ ?_⟩
  obtain ⟨k, r, hr, hy⟩ := hR x
  set y := diagonal K k * x * r⁻¹ with hydef
  have hmod : ideleModule K y = (ideleModule K r)⁻¹ := by
    rw [hydef, map_mul, map_mul, map_inv, ideleModule_diagonal, MonoidHom.mem_ker.1 hx, one_mul,
      one_mul]
  have hinf : |Real.log (infiniteModule y)| ≤ ∑ r ∈ R, |Real.log (ideleModule K r : ℝ)| := by
    have h1 : infiniteModule y = ((ideleModule K r : ℝ))⁻¹ := by
      have := congrArg Subtype.val hmod
      rw [ideleModule_apply, finiteModule_eq_one_of_mem hy, mul_one] at this
      exact this
    rw [h1, Real.log_inv, abs_neg]
    exact Finset.single_le_sum (f := fun r ↦ |Real.log (ideleModule K r : ℝ)|)
      (fun r _ ↦ abs_nonneg _) hr
  obtain ⟨u, hu⟩ := hM y hinf
  refine ⟨unitsToUnits K u * k, Set.mem_biUnion hr
    ⟨diagonal K (unitsToUnits K u) * y, ⟨hu, mul_mem (diagonal_unitsToUnits_mem K u) hy⟩, ?_⟩⟩
  simp only [hydef, map_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem exists_isCompact_normOneSubgroup :
    ∃ D : Set (IdeleGroup K), IsCompact D ∧ D ⊆ normOneSubgroup K ∧
      ∀ x ∈ normOneSubgroup K, ∃ k : Kˣ, diagonal K k * x ∈ D := by
  obtain ⟨R, hR⟩ := exists_finset_mul_mem_standardOpenSubgroup K
  obtain ⟨D, hD, hxD⟩ := exists_isCompact_of_finset K R hR
  refine ⟨D ∩ normOneSubgroup K, hD.inter_right (isClosed_normOneSubgroup K),
    Set.inter_subset_right, fun x hx ↦ ?_⟩
  obtain ⟨k, hk⟩ := hxD x hx
  exact ⟨k, hk, mul_mem (range_diagonal_le_normOneSubgroup K ⟨k, rfl⟩) hx⟩

end IdeleGroup

namespace IdeleClassGroup

theorem isCompact_normOneSubgroup :
    IsCompact (normOneSubgroup K : Set (IdeleClassGroup K)) := by
  obtain ⟨D, hD, hDJ, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup K
  have h : (normOneSubgroup K : Set (IdeleClassGroup K)) = mk K '' D := by
    rw [normOneSubgroup_eq_map, Subgroup.coe_map]
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hxD x hx
      refine ⟨IdeleGroup.diagonal K k * x, hk, ?_⟩
      rw [map_mul, mk_diagonal]
      exact one_mul (mk K x)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hDJ hx, rfl⟩
  rw [h]
  exact hD.image (continuous_mk K)

instance compactSpace_normOneSubgroup : CompactSpace (normOneSubgroup K) :=
  isCompact_iff_compactSpace.1 (isCompact_normOneSubgroup K)

end IdeleClassGroup

end

end GroundTheory.Global
