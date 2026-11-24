module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.LocalReciprocityFinite
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.NormGroups
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Development.Core20Slim.GroundTheory.LocalFields.LocalAxiom
public import Development.Core20Slim.GroundTheory.LocalFields.LocalAxiomDictionary
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Defs.Basic

@[expose] public section

namespace GroundTheory.LocalField

open Abstract

section Dictionary

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem normal_subgroupOf_top_fixingOpenSubgroup_iff (L : IntermediateField K Ω)
    [FiniteDimensional K L] :
    ((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal ↔ IsGalois K L := by
  rw [← InfiniteGalois.normal_iff_isGalois, coe_fixingOpenSubgroup]
  constructor
  · intro h
    refine ⟨fun n hn g => ?_⟩
    have := h.conj_mem ⟨n, Subgroup.mem_top n⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨g, Subgroup.mem_top g⟩
    exact Subgroup.mem_subgroupOf.1 this
  · intro h
    exact h.subgroupOf _

theorem isAbelianExtension_fixingOpenSubgroup_iff (L : IntermediateField K Ω) [FiniteDimensional K L] :
    IsAbelianExtension ⊤ (fixingOpenSubgroup L) ↔
      IsGalois K L ∧ ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ := by
  constructor
  · intro h
    have hn := h.normal
    have hG : IsGalois K L := (normal_subgroupOf_top_fixingOpenSubgroup_iff L).1 hn
    refine ⟨hG, fun σ τ => ?_⟩
    have hc := h.isMulCommutative
    obtain ⟨p, rfl⟩ := (baseQuotientEquiv L).surjective σ
    obtain ⟨q, rfl⟩ := (baseQuotientEquiv L).surjective τ
    rw [← map_mul, ← map_mul, hc.is_comm.comm]
  · rintro ⟨hG, hc⟩
    have hn := (normal_subgroupOf_top_fixingOpenSubgroup_iff L).2 hG
    have : IsMulCommutative (((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⧸
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
          ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :=
      ⟨⟨fun p q => (baseQuotientEquiv L).injective (by rw [map_mul, map_mul, hc])⟩⟩
    exact isAbelianExtension_of_isMulCommutative le_top


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem map_baseUnitsEquiv_normGroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    (normGroup Ωˣ ⊤ (fixingOpenSubgroup L)).map
      (baseUnitsEquiv (K := K) (Ω := Ω) : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ) =
      (normUnits K L).range := by
  have : (L.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (baseUnitsEquiv_norm L a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨(fixedModuleUnitsEquiv L).symm b, rfl⟩, ?_⟩
    change baseUnitsEquiv (Abstract.norm Ωˣ ⊤ L.fixingSubgroup _) = _
    rw [baseUnitsEquiv_norm, MulEquiv.apply_symm_apply]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem mem_normGroup_iff_mem_range_normUnits (L : IntermediateField K Ω) [FiniteDimensional K L]
    (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    a ∈ normGroup Ωˣ ⊤ (fixingOpenSubgroup L) ↔ baseUnitsEquiv a ∈ (normUnits K L).range := by
  rw [← map_baseUnitsEquiv_normGroup L]
  constructor
  · intro ha
    exact ⟨a, ha, rfl⟩
  · rintro ⟨b, hb, hba⟩
    rwa [← baseUnitsEquiv.injective hba]



variable (L : IntermediateField K Ω) [FiniteDimensional K L]

end Dictionary

section Correspondence

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units

theorem range_normUnits_le_range_normUnits_iff {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K L'] [IsGalois K L] [IsGalois K L']
    (hL : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (hL' : ∀ σ τ : L' ≃ₐ[K] L', σ * τ = τ * σ) :
    (normUnits K L).range ≤ (normUnits K L').range ↔ L' ≤ L := by
  rw [← map_baseUnitsEquiv_normGroup, ← map_baseUnitsEquiv_normGroup,
    Subgroup.map_le_map_iff_of_injective baseUnitsEquiv.injective,
    (localClassFieldTheory K Ω).normGroup_le_normGroup_iff (localClassFieldTheory K Ω).classFieldAxiom
      ((isAbelianExtension_fixingOpenSubgroup_iff L).2 ⟨inferInstance, hL⟩)
      ((isAbelianExtension_fixingOpenSubgroup_iff L').2 ⟨inferInstance, hL'⟩)]
  exact fixingSubgroup_le_fixingSubgroup_iff

end Correspondence

end GroundTheory.LocalField
