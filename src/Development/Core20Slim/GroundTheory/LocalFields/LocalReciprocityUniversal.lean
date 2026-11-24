module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.LocalReciprocityFinite
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Frobenius
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Isomorphism
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.NormGroups
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityAbelianizationRestrictReciprocityLimi
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityMap
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Valuation
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Development.Core20Slim.GroundTheory.LocalFields.LocalAxiom
public import Development.Core20Slim.GroundTheory.LocalFields.LocalAxiomDictionary
public import Development.Core20Slim.GroundTheory.LocalFields.LocalReciprocityLimitAbstract
public import Development.Core20Slim.GroundTheory.LocalFields.MaximalUnramified
public import GroundTheory.LocalFields.UnitsBasic
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Bracket
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.PNat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.ZMod

@[expose] public section

namespace GroundTheory.LocalField

open Abstract ValuativeRel

section Group

variable {G : Type*} [Group G] {M : Type*} [Group M] [IsMulCommutative M]

theorem commutator_le_ker_of_isMulCommutative (f : G →* M) : commutator G ≤ f.ker := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm' _ _

end Group

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Top


variable (K Ω) in
def topSubtype : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) →* (Ω ≃ₐ[K] Ω) :=
  Subgroup.subtype _

theorem continuous_topSubtype : Continuous (topSubtype K Ω) :=
  continuous_subtype_val


variable (K Ω) in
def topSubtypeInv : (Ω ≃ₐ[K] Ω) →* ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) where
  toFun g := ⟨g, Subgroup.mem_top g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_topSubtypeInv : Continuous (topSubtypeInv K Ω) :=
  continuous_id.subtype_mk _


variable (K Ω) in
noncomputable def topAbelianizationEquiv :
    TopologicalAbelianization ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ≃*
      TopologicalAbelianization (Ω ≃ₐ[K] Ω) where
  toFun := topologicalAbelianizationMap (topSubtype K Ω) continuous_topSubtype
  invFun := topologicalAbelianizationMap (topSubtypeInv K Ω) continuous_topSubtypeInv
  left_inv y := by
    induction y using QuotientGroup.induction_on with
    | H g => rfl
  right_inv y := by
    induction y using QuotientGroup.induction_on with
    | H g => rfl
  map_mul' := map_mul _

@[simp]
theorem topAbelianizationEquiv_mk (g : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    topAbelianizationEquiv K Ω (g : TopologicalAbelianization _) =
      ((g : Ω ≃ₐ[K] Ω) : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :=
  rfl

theorem continuous_topAbelianizationEquiv : Continuous (topAbelianizationEquiv K Ω) :=
  continuous_topologicalAbelianizationMap (topSubtype K Ω) continuous_topSubtype

end Top

section Restrict

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem ker_restrictNormalHom :
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker = L.fixingSubgroup := by
  ext σ
  have hc : ∀ y : L, (((σ.restrictNormal L) y : L) : Ω) = σ y :=
    fun y => AlgEquiv.restrictNormal_commutes _ _ y
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := congrArg (fun τ : L ≃ₐ[K] L => ((τ ⟨x, hx⟩ : L) : Ω)) h
    simp only [AlgEquiv.restrictNormalHom_apply, hc, AlgEquiv.one_apply] at this
    exact this
  · intro h
    ext x
    simp only [AlgEquiv.restrictNormalHom_apply, hc, AlgEquiv.one_apply]
    exact h x x.2

variable [IsMulCommutative (L ≃ₐ[K] L)]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem topologicalClosure_commutator_le_ker_restrictNormalHom :
    (commutator (Ω ≃ₐ[K] Ω)).topologicalClosure ≤
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker := by
  refine Subgroup.topologicalClosure_minimal _ (commutator_le_ker_of_isMulCommutative _) ?_
  rw [ker_restrictNormalHom]
  exact Subgroup.isClosed_of_isOpen _ (L.fixingSubgroup_isOpen)

noncomputable def abelianRestrict : TopologicalAbelianization (Ω ≃ₐ[K] Ω) →* (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L)
    (topologicalClosure_commutator_le_ker_restrictNormalHom L)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp]
theorem abelianRestrict_mk (σ : Ω ≃ₐ[K] Ω) :
    abelianRestrict L (σ : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = σ.restrictNormal L :=
  rfl

theorem isAbelianExtension_fixingOpenSubgroup : IsAbelianExtension ⊤ (fixingOpenSubgroup L) := by
  refine ⟨le_top, ?_⟩
  rw [← ker_restrictTop]
  exact commutator_le_ker_of_isMulCommutative _

theorem abelianRestrict_topAbelianizationEquiv
    (y : TopologicalAbelianization ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    abelianRestrict L (topAbelianizationEquiv K Ω y) =
      baseQuotientEquiv L (abelianizationRestrict (isAbelianExtension_fixingOpenSubgroup L) y) := by
  induction y using QuotientGroup.induction_on with
  | H g => rfl

end Restrict

section Universal


variable (K Ω) in
noncomputable def localReciprocityLimit : Kˣ →* TopologicalAbelianization (Ω ≃ₐ[K] Ω) :=
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  (topAbelianizationEquiv K Ω).toMonoidHom.comp
    (((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) ⊤).comp
      (baseUnitsEquiv (K := K) (Ω := Ω)).symm.toMonoidHom)

theorem localReciprocityLimit_baseUnitsEquiv
    (a : fixedModule Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    haveI := isDiscreteModule_units (K := K) (Ω := Ω)
    localReciprocityLimit K Ω (baseUnitsEquiv a) = topAbelianizationEquiv K Ω
      ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) ⊤ a) := by
  simp only [localReciprocityLimit, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulEquiv.symm_apply_apply]

theorem of_abelianRestrict_localReciprocityLimit (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (x : Kˣ) :
    Group.Abelianization.of (abelianRestrict L (localReciprocityLimit K Ω x)) =
      (localReciprocity L).symm (x : Kˣ ⧸ (normUnits K L).range) := by
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  obtain ⟨a, rfl⟩ := (baseUnitsEquiv (K := K) (Ω := Ω)).surjective x
  have hM := isAbelianExtension_fixingOpenSubgroup L
  rw [localReciprocityLimit_baseUnitsEquiv, abelianRestrict_topAbelianizationEquiv,
    (localClassFieldData K Ω).abelianizationRestrict_reciprocityLimit _ hM,
    localReciprocity_symm_mk_baseUnitsEquiv]
  set q := ((localClassFieldData K Ω).reciprocityAbelianEquiv (classFieldAxiom_units K Ω) hM).symm
    (a : tateZero Ωˣ _ _) with hq
  have e : ((localClassFieldData K Ω).reciprocityAbEquiv (le_top : fixingOpenSubgroup L ≤ ⊤)
      (classFieldAxiom_units K Ω)).symm (a : tateZero Ωˣ _ _) = Group.Abelianization.of q := by
    rw [MulEquiv.symm_apply_eq, ClassFieldData.reciprocityAbEquiv_of, hq,
      ← (localClassFieldData K Ω).reciprocityAbelianEquiv_apply (classFieldAxiom_units K Ω) hM,
      MulEquiv.apply_symm_apply]
  rw [e]
  rfl

omit [IsSepClosure K Ω] in
theorem mem_range_norm_top_iff (L : IntermediateField K Ω) [IsGalois K Ω] [FiniteDimensional K L]
    (a : fixedModule Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    a ∈ (norm Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω))).range ↔
      baseUnitsEquiv a ∈ (normUnits K L).range := by
  haveI : (L.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, (baseUnitsEquiv_norm L b).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨(fixedModuleUnitsEquiv L).symm b, baseUnitsEquiv.injective ?_⟩
    change baseUnitsEquiv (Abstract.norm Ωˣ ⊤ L.fixingSubgroup _) = _
    rw [baseUnitsEquiv_norm, MulEquiv.apply_symm_apply, hb]

theorem ker_localReciprocityLimit :
    (localReciprocityLimit K Ω).ker =
      ⨅ L : {L : IntermediateField K Ω // FiniteDimensional K L},
        haveI := L.2
        (normUnits K L.1).range := by
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  ext x
  obtain ⟨a, rfl⟩ := (baseUnitsEquiv (K := K) (Ω := Ω)).surjective x
  rw [MonoidHom.mem_ker, localReciprocityLimit_baseUnitsEquiv, map_eq_one_iff _
    (topAbelianizationEquiv K Ω).injective, ← MonoidHom.mem_ker,
    ClassFieldData.ker_reciprocityLimit_eq_iInf, Subgroup.mem_iInf, Subgroup.mem_iInf]
  constructor
  · intro h L
    haveI := L.2
    have := h ⟨fixingOpenSubgroup L.1, le_top⟩
    exact (mem_range_norm_top_iff L.1 a).1 this
  · intro h M
    have hM := fixingOpenSubgroup_fixedField M.1
    have h' := (mem_range_norm_top_iff _ a).2
      (h ⟨IntermediateField.fixedField (M.1 : Subgroup (Ω ≃ₐ[K] Ω)), inferInstance⟩)
    rw [hM] at h'
    exact h'

theorem denseRange_localReciprocityLimit : DenseRange (localReciprocityLimit K Ω) := by
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  have hd := (localClassFieldData K Ω).denseRange_reciprocityLimit (classFieldAxiom_units K Ω)
    (K := (⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)))
  have hd' : DenseRange (((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) ⊤) ∘
      (baseUnitsEquiv (K := K) (Ω := Ω)).symm) := by
    unfold DenseRange
    rw [Function.Surjective.range_comp (MulEquiv.surjective _)]
    exact hd
  have := DenseRange.comp (topAbelianizationEquiv K Ω).surjective.denseRange hd'
    continuous_topAbelianizationEquiv
  exact this

end Universal

section Degree

open ProfiniteInteger


variable (K Ω) in
noncomputable def unramifiedOpenSubgroup (n : ℕ+) : OpenSubgroup (Ω ≃ₐ[K] Ω) where
  toSubgroup := (AddSubgroup.toSubgroup (multiples n)).comap (unramifiedDegree K Ω)
  isOpen' := (isOpen_multiples n).preimage (continuous_toAdd.comp continuous_unramifiedDegree)

theorem mem_unramifiedOpenSubgroup {n : ℕ+} {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ (unramifiedOpenSubgroup K Ω n : Subgroup (Ω ≃ₐ[K] Ω)) ↔
      Multiplicative.toAdd (unramifiedDegree K Ω σ) ∈ multiples n :=
  Iff.rfl

theorem unramifiedDegree_of_mk_eq_localReciprocityLimit {x : Kˣ} {g : Ω ≃ₐ[K] Ω}
    (hg : (g : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = localReciprocityLimit K Ω x) :
    unramifiedDegree K Ω g = Multiplicative.ofAdd ((ord (x : K) : ℤ) : ℤ̂) := by
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  obtain ⟨a, rfl⟩ := (baseUnitsEquiv (K := K) (Ω := Ω)).surjective x
  rw [localReciprocityLimit_baseUnitsEquiv] at hg
  have hg' : ((⟨g, Subgroup.mem_top g⟩ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
      TopologicalAbelianization _) =
      (localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) ⊤ a :=
    (topAbelianizationEquiv K Ω).injective (by rw [← hg]; rfl)
  obtain ⟨φ, hφ⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) (Multiplicative.ofAdd 1)
  set φ' : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := ⟨φ, Subgroup.mem_top φ⟩
  have hφ' : (localClassFieldData K Ω).relDeg ⊤ φ' = Multiplicative.ofAdd 1 := by
    rw [ClassFieldData.relDeg_eq_iff, localClassFieldData_deg, inertiaDegree_top_unramifiedDegree,
      pow_one]
    exact hφ
  have hv := valuation_top_localClassFieldData a
  refine multiplicative_ext fun n => ?_
  have hu : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⊓
      (localClassFieldData K Ω).deg.ker ≤ (unramifiedOpenSubgroup K Ω n : Subgroup (Ω ≃ₐ[K] Ω)) := by
    intro σ hσ
    rw [mem_unramifiedOpenSubgroup, (MonoidHom.mem_ker.1 hσ.2 : unramifiedDegree K Ω σ = 1),
      toAdd_one]
    exact (multiples n).zero_mem
  have hL : IsAbelianExtension ⊤ (unramifiedOpenSubgroup K Ω n) := by
    refine ⟨le_top, fun y hy => ?_⟩
    have h := commutator_le_ker_of_isMulCommutative
      ((unramifiedDegree K Ω).comp (Subgroup.subtype _)) hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at h
    rw [Subgroup.mem_subgroupOf, mem_unramifiedOpenSubgroup, h, toAdd_one]
    exact (multiples n).zero_mem
  haveI := hL.normal
  have h1 := (localClassFieldData K Ω).reciprocity_abelianizationRestrict_reciprocityLimit
    (classFieldAxiom_units K Ω) hL a
  rw [← hg', abelianizationRestrict_mk] at h1
  have h2 := (localClassFieldData K Ω).reciprocityAbEquiv_symm_of_unramified_of_valuation hL.le
    (classFieldAxiom_units K Ω) hu hφ' a _ hv
  rw [MulEquiv.symm_apply_eq, ← map_zpow, ClassFieldData.reciprocityAbEquiv_of,
    ← QuotientGroup.mk_zpow] at h2
  have h3 := (localClassFieldData K Ω).reciprocity_injective (classFieldAxiom_units K Ω) hL
    (h1.trans h2)
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_unramifiedOpenSubgroup] at h3
  rw [← proj_eq_zero_iff] at h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, map_mul, map_inv, map_zpow,
    toAdd_mul, toAdd_inv, toAdd_zpow, map_add, map_neg, map_zsmul] at h3
  rw [show (φ' : Ω ≃ₐ[K] Ω) = φ from rfl, hφ, toAdd_ofAdd, map_one, zsmul_one,
    neg_add_eq_zero] at h3
  rw [toAdd_ofAdd, map_intCast]
  exact h3

theorem restrictNormal_eq_frobenius_of_mk_eq_localReciprocityLimit {π : Kˣ}
    (hπ : ord (π : K) = 1) {g : Ω ≃ₐ[K] Ω}
    (hg : (g : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = localReciprocityLimit K Ω π) :
    g.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω := by
  rw [restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff,
    unramifiedDegree_of_mk_eq_localReciprocityLimit hg, hπ, Int.cast_one]

end Degree

section Abelian

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω]
  [FiniteDimensional K L] [IsGalois K L] in
theorem bijective_abelianizationOf :
    Function.Bijective (Group.Abelianization.of : (L ≃ₐ[K] L) →* Group.Abelianization (L ≃ₐ[K] L)) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun σ hσ => ?_, QuotientGroup.mk_surjective⟩
  rw [← MonoidHom.mem_ker, Group.Abelianization.ker_of, commutator,
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun x _ y _ => mul_comm' y x)] at hσ
  exact hσ

noncomputable def localReciprocityAbelian : (L ≃ₐ[K] L) ≃* Kˣ ⧸ (normUnits K L).range :=
  (MulEquiv.ofBijective _ (bijective_abelianizationOf L)).trans (localReciprocity L)

theorem of_localReciprocityAbelian_symm (x : Kˣ ⧸ (normUnits K L).range) :
    Group.Abelianization.of ((localReciprocityAbelian L).symm x) = (localReciprocity L).symm x := by
  rw [MulEquiv.eq_symm_apply]
  exact (localReciprocityAbelian L).apply_symm_apply x

theorem abelianRestrict_localReciprocityLimit (x : Kˣ) :
    abelianRestrict L (localReciprocityLimit K Ω x) =
      (localReciprocityAbelian L).symm (x : Kˣ ⧸ (normUnits K L).range) := by
  apply (bijective_abelianizationOf L).1
  rw [of_abelianRestrict_localReciprocityLimit, of_localReciprocityAbelian_symm]

end Abelian

section Absolute

end Absolute

end GroundTheory.LocalField
