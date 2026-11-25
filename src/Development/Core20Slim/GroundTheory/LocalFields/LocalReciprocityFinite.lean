module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.LocalAxiom
public import Development.Core20Slim.GroundTheory.LocalFields.LocalReciprocityLimitAbstract
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Isomorphism
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.UniqueQuotientSubgroupOfSelf
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Valuation
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Development.Core20Slim.GroundTheory.LocalFields.LocalAxiomDictionary
public import Development.Core20Slim.GroundTheory.LocalFields.MaximalUnramified
public import GroundTheory.LocalFields.UnitsBasic
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
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
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.PNat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.LocalField

open Abstract ValuativeRel

section Transport

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def transportReciprocity {K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω)} (hLK : L' ≤ K')
    [((L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K').Normal] {Γ M : Type*} [Group Γ] [CommGroup M]
    (e : (K' : Subgroup (Ω ≃ₐ[K] Ω)) ⧸ (L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K' ≃* Γ)
    (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) ≃* M) (N : Subgroup M)
    (hN : (norm Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) (L' : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) →* M) = N) :
    Group.Abelianization Γ ≃* M ⧸ N :=
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  e.abelianizationCongr.symm.trans
    (((localClassFieldData K Ω).reciprocityAbEquiv hLK (classFieldAxiom_units K Ω)).trans
      (QuotientGroup.congr _ _ u hN))

theorem transportReciprocity_symm_mk {K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω)} (hLK : L' ≤ K')
    [((L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K').Normal] {Γ M : Type*} [Group Γ] [CommGroup M]
    (e : (K' : Subgroup (Ω ≃ₐ[K] Ω)) ⧸ (L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K' ≃* Γ)
    (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) ≃* M) (N : Subgroup M)
    (hN : (norm Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) (L' : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) →* M) = N) (a : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω))) :
    haveI := isDiscreteModule_units (K := K) (Ω := Ω)
    (transportReciprocity hLK e u N hN).symm (u a : M ⧸ N) =
      e.abelianizationCongr (((localClassFieldData K Ω).reciprocityAbEquiv hLK
        (classFieldAxiom_units K Ω)).symm (a : tateZero Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω))
          (L' : Subgroup (Ω ≃ₐ[K] Ω)))) := by
  simp only [transportReciprocity, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  congr 2
  rw [QuotientGroup.congr_symm, QuotientGroup.congr_mk, MulEquiv.symm_apply_apply]

end Transport

section Base

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

noncomputable def restrictTop :
    ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) →* (L ≃ₐ[K] L) :=
  (AlgEquiv.restrictNormalHom L).comp (⊤ : Subgroup (Ω ≃ₐ[K] Ω)).subtype

@[simp]
theorem restrictTop_apply (σ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    restrictTop L σ = (σ : Ω ≃ₐ[K] Ω).restrictNormal L :=
  rfl

theorem restrictTop_surjective : Function.Surjective (restrictTop L) := fun τ => by
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω) τ
  exact ⟨⟨σ, Subgroup.mem_top σ⟩, hσ⟩

theorem ker_restrictTop :
    (restrictTop L).ker = (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := by
  ext σ
  have hc : ∀ y : L, ((((σ : Ω ≃ₐ[K] Ω).restrictNormal L) y : L) : Ω) = (σ : Ω ≃ₐ[K] Ω) y :=
    fun y => AlgEquiv.restrictNormal_commutes _ _ y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, coe_fixingOpenSubgroup,
    IntermediateField.mem_fixingSubgroup_iff, restrictTop_apply]
  constructor
  · intro h x hx
    have := congrArg (fun τ : L ≃ₐ[K] L => ((τ ⟨x, hx⟩ : L) : Ω)) h
    simp only [hc, AlgEquiv.one_apply] at this
    exact this
  · intro h
    ext x
    rw [hc, AlgEquiv.one_apply]
    exact h x x.2

instance normal_fixingOpenSubgroup_top :
    ((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal := by
  rw [← ker_restrictTop]
  exact MonoidHom.normal_ker _

noncomputable def baseQuotientEquiv :
    ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⧸
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
          ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_restrictTop L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (restrictTop_surjective L))

@[simp]
theorem baseQuotientEquiv_mk (σ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    baseQuotientEquiv L (σ : _ ⧸ _) = (σ : Ω ≃ₐ[K] Ω).restrictNormal L :=
  rfl

theorem map_baseUnitsEquiv_range_norm :
    (norm Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (baseUnitsEquiv (K := K) (Ω := Ω) : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ) =
      (normUnits K L).range := by
  haveI : (L.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
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

noncomputable def localReciprocity : Group.Abelianization (L ≃ₐ[K] L) ≃* Kˣ ⧸ (normUnits K L).range :=
  transportReciprocity (K' := ⊤) (L' := fixingOpenSubgroup L) le_top (baseQuotientEquiv L)
    baseUnitsEquiv (normUnits K L).range (map_baseUnitsEquiv_range_norm L)

theorem localReciprocity_symm_mk_baseUnitsEquiv
    (a : fixedModule Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    haveI := isDiscreteModule_units (K := K) (Ω := Ω)
    (localReciprocity L).symm (baseUnitsEquiv a : Kˣ ⧸ (normUnits K L).range) =
      (baseQuotientEquiv L).abelianizationCongr
        (((localClassFieldData K Ω).reciprocityAbEquiv (le_top : fixingOpenSubgroup L ≤ ⊤)
          (classFieldAxiom_units K Ω)).symm (a : tateZero Ωˣ _ _)) :=
  transportReciprocity_symm_mk _ _ _ _ _ a

end Base

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem inertiaDegree_top_unramifiedDegree :
    inertiaDegree (unramifiedDegree K Ω)
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) = 1 := by
  rw [inertiaDegree]
  change ((⊤ : Subgroup (Ω ≃ₐ[K] Ω)).map (unramifiedDegree K Ω)).index = 1
  rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top_of_surjective _ unramifiedDegree_surjective,
    Subgroup.index_top]

theorem valuation_top_localClassFieldData
    (a : fixedModule Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    (localClassFieldData K Ω).valuation ⊤ a =
      Multiplicative.ofAdd ((ord ((baseUnitsEquiv a : Kˣ) : K) : ℤ) : ℤ̂) := by
  have h := (localClassFieldData K Ω).valuation_pow ⊤ a
  rw [localClassFieldData_deg, inertiaDegree_top_unramifiedDegree, pow_one] at h
  rw [h]
  erw [norm_self]
  rfl



variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]


end Frobenius

section Relative

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]



omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in
theorem fixingOpenSubgroup_anti {L F : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K F] (h : L ≤ F) : fixingOpenSubgroup F ≤ fixingOpenSubgroup L :=
  fun _ hx => IntermediateField.fixingSubgroup_antitone h hx

variable {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F]
  [IsGalois E (IntermediateField.extendScalars h)]

theorem map_unitsEquivOfForall_range_norm (K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω))
    (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L') :
    (norm Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) (L' : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (unitsEquivOfForall (K' : Subgroup (Ω ≃ₐ[K] Ω)) E (mem_iff_forall_of_fixingSubgroup_eq _ hK) :
        fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) →* Eˣ) =
      (normUnits E (IntermediateField.extendScalars h)).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (unitsEquivOfForall_norm (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨(unitsEquivOfForall (L' : Subgroup (Ω ≃ₐ[K] Ω)) (IntermediateField.extendScalars h)
      (mem_extendScalars_iff_forall _ h hL)).symm b, rfl⟩, ?_⟩
    change unitsEquivOfForall _ E _ (norm Ωˣ _ _ _) = _
    rw [unitsEquivOfForall_norm (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL, MulEquiv.apply_symm_apply]

end Relative

section NormSquare

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F]
  [IsGalois E (IntermediateField.extendScalars h)]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

end NormSquare

section ConjSquare

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]




variable {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F]
  [IsGalois E (IntermediateField.extendScalars h)] (σ : Ω ≃ₐ[K] Ω)
  {E₂ F₂ : IntermediateField K Ω} (h₂ : E₂ ≤ F₂) [FiniteDimensional K F₂]
  [IsGalois E₂ (IntermediateField.extendScalars h₂)]
  (hE : E.map (σ : Ω →ₐ[K] Ω) = E₂) (hF : F.map (σ : Ω →ₐ[K] Ω) = F₂)




end ConjSquare

end GroundTheory.LocalField
