module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.Basic

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Topology
open scoped NumberField.AdeleRing

noncomputable section

namespace AdeleBaseChange

section Ext

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem adeleRingHom_ext {R : Type*} [Semiring R] {f g : 𝔸[L] →+* R}
    (hL : ∀ l : L, f (algebraMap L 𝔸[L] l) = g (algebraMap L 𝔸[L] l))
    (hK : ∀ a : 𝔸[K], f (adeleMap K L a) = g (adeleMap K L a)) : f = g := by
  ext y
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv K L).surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [adeleTensorEquiv_tmul, map_mul, map_mul, hL, hK]
  | add s t hs ht => rw [map_add (f := _), map_add (f := _), map_add (f := _), hs, ht]

theorem adeleTensorEquiv_symm_algebraMap (l : L) :
    (adeleTensorEquiv K L).symm (algebraMap L 𝔸[L] l) = l ⊗ₜ 1 := by
  rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, mul_one]

theorem adeleTensorEquiv_symm_adeleMap (a : 𝔸[K]) :
    (adeleTensorEquiv K L).symm (adeleMap K L a) = 1 ⊗ₜ a := by
  rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, one_mul]

end Ext

section Transport

variable {L L' L'' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field L'']
  [NumberField L'']

def adeleRingEquiv (τ : L ≃+* L') : 𝔸[L] ≃+* 𝔸[L'] :=
  ((adeleTensorEquiv ℚ L).symm.toRingEquiv.trans
    (Algebra.TensorProduct.congr τ.toRatAlgEquiv (AlgEquiv.refl : 𝔸[ℚ] ≃ₐ[ℚ] 𝔸[ℚ])).toRingEquiv).trans
    (adeleTensorEquiv ℚ L').toRingEquiv

@[simp]
theorem adeleRingEquiv_algebraMap (τ : L ≃+* L') (l : L) :
    adeleRingEquiv τ (algebraMap L 𝔸[L] l) = algebraMap L' 𝔸[L'] (τ l) := by
  change adeleTensorEquiv ℚ L' (Algebra.TensorProduct.congr τ.toRatAlgEquiv AlgEquiv.refl
    ((adeleTensorEquiv ℚ L).symm (algebraMap L 𝔸[L] l))) = _
  rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    adeleTensorEquiv_tmul]
  simp

@[simp]
theorem adeleRingEquiv_adeleMap_rat (τ : L ≃+* L') (a : 𝔸[ℚ]) :
    adeleRingEquiv τ (adeleMap ℚ L a) = adeleMap ℚ L' a := by
  change adeleTensorEquiv ℚ L' (Algebra.TensorProduct.congr τ.toRatAlgEquiv AlgEquiv.refl
    ((adeleTensorEquiv ℚ L).symm (adeleMap ℚ L a))) = _
  rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul]
  simp

theorem adeleRingHom_ext_rat {R : Type*} [Semiring R] {f g : 𝔸[L] →+* R}
    (hL : ∀ l : L, f (algebraMap L 𝔸[L] l) = g (algebraMap L 𝔸[L] l))
    (hQ : ∀ a : 𝔸[ℚ], f (adeleMap ℚ L a) = g (adeleMap ℚ L a)) : f = g :=
  adeleRingHom_ext hL hQ

@[simp]
theorem adeleRingEquiv_refl : adeleRingEquiv (RingEquiv.refl L) = RingEquiv.refl 𝔸[L] := by
  apply RingEquiv.toRingHom_injective
  refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
  · exact adeleRingEquiv_algebraMap _ l
  · exact adeleRingEquiv_adeleMap_rat _ a

theorem adeleRingEquiv_trans (τ : L ≃+* L') (τ' : L' ≃+* L'') :
    adeleRingEquiv (τ.trans τ') = (adeleRingEquiv τ).trans (adeleRingEquiv τ') := by
  apply RingEquiv.toRingHom_injective
  refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
  · change adeleRingEquiv (τ.trans τ') _ = adeleRingEquiv τ' (adeleRingEquiv τ _)
    rw [adeleRingEquiv_algebraMap, adeleRingEquiv_algebraMap, adeleRingEquiv_algebraMap]
    rfl
  · change adeleRingEquiv (τ.trans τ') _ = adeleRingEquiv τ' (adeleRingEquiv τ _)
    rw [adeleRingEquiv_adeleMap_rat, adeleRingEquiv_adeleMap_rat, adeleRingEquiv_adeleMap_rat]

theorem adeleRingEquiv_symm (τ : L ≃+* L') :
    adeleRingEquiv τ.symm = (adeleRingEquiv τ).symm := by
  ext x
  apply (adeleRingEquiv τ).injective
  rw [RingEquiv.apply_symm_apply, ← RingEquiv.trans_apply, ← adeleRingEquiv_trans,
    RingEquiv.symm_trans_self, adeleRingEquiv_refl, RingEquiv.refl_apply]

theorem continuous_adeleRingEquiv (τ : L ≃+* L') : Continuous (adeleRingEquiv τ) := by
  have : IsModuleTopology 𝔸[ℚ] 𝔸[L] := isModuleTopology_adeleRing
  let f : 𝔸[L] →ₗ[𝔸[ℚ]] 𝔸[L'] :=
    { toFun := adeleRingEquiv τ
      map_add' := map_add _
      map_smul' := fun c x ↦ by
        simp only [Algebra.smul_def, algebraMap_adeleRing, map_mul, adeleRingEquiv_adeleMap_rat,
          RingHom.id_apply] }
  exact IsModuleTopology.continuous_of_linearMap f

end Transport

section Relative

variable {K L L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L']

@[simp]
theorem adeleRingEquiv_adeleMap (τ : L ≃ₐ[K] L') (a : 𝔸[K]) :
    adeleRingEquiv (τ : L ≃+* L') (adeleMap K L a) = adeleMap K L' a := by
  have h : ((adeleRingEquiv (τ : L ≃+* L')).toRingHom.comp (adeleMap K L) : 𝔸[K] →+* 𝔸[L']) =
      adeleMap K L' := by
    refine adeleRingHom_ext_rat (fun k ↦ ?_) (fun a ↦ ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, adeleMap_algebraMap, adeleRingEquiv_algebraMap]
      simp
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, adeleMap_adeleMap, adeleRingEquiv_adeleMap_rat]
  exact congrArg (fun f : 𝔸[K] →+* 𝔸[L'] ↦ f a) h


variable (K) in
def adeleAlgEquiv (τ : L ≃ₐ[K] L') : 𝔸[L] ≃ₐ[𝔸[K]] 𝔸[L'] :=
  AlgEquiv.ofRingEquiv (f := adeleRingEquiv (τ : L ≃+* L')) fun a ↦ adeleRingEquiv_adeleMap τ a

theorem norm_adeleRingEquiv (τ : L ≃ₐ[K] L') (x : 𝔸[L]) :
    Algebra.norm 𝔸[K] (adeleRingEquiv (τ : L ≃+* L') x) = Algebra.norm 𝔸[K] x :=
  Algebra.norm_eq_of_algEquiv (adeleAlgEquiv K τ) x

end Relative

end AdeleBaseChange

open AdeleBaseChange

section Idele

variable {L L' L'' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field L'']
  [NumberField L'']

def ideleEquiv (τ : L ≃+* L') : IdeleGroup L ≃ₜ* IdeleGroup L' where
  toMulEquiv := Units.mapEquiv (adeleRingEquiv τ).toMulEquiv
  continuous_toFun := Continuous.units_map (adeleRingEquiv τ).toMonoidHom (continuous_adeleRingEquiv τ)
  continuous_invFun := by
    have h := Continuous.units_map (adeleRingEquiv τ.symm).toMonoidHom
      (continuous_adeleRingEquiv τ.symm)
    rw [adeleRingEquiv_symm] at h
    exact h

@[simp]
theorem coe_ideleEquiv (τ : L ≃+* L') (x : IdeleGroup L) :
    ((ideleEquiv τ x : IdeleGroup L') : 𝔸[L']) = adeleRingEquiv τ (x : 𝔸[L]) :=
  rfl

@[simp]
theorem ideleEquiv_refl (x : IdeleGroup L) : ideleEquiv (RingEquiv.refl L) x = x :=
  Units.ext (by rw [coe_ideleEquiv, adeleRingEquiv_refl, RingEquiv.refl_apply])

theorem ideleEquiv_trans (τ : L ≃+* L') (τ' : L' ≃+* L'') (x : IdeleGroup L) :
    ideleEquiv (τ.trans τ') x = ideleEquiv τ' (ideleEquiv τ x) :=
  Units.ext (by rw [coe_ideleEquiv, coe_ideleEquiv, coe_ideleEquiv, adeleRingEquiv_trans,
    RingEquiv.trans_apply])

@[simp]
theorem ideleEquiv_diagonal (τ : L ≃+* L') (l : Lˣ) :
    ideleEquiv τ (IdeleGroup.diagonal L l) =
      IdeleGroup.diagonal L' (Units.map (τ : L →* L') l) :=
  Units.ext (adeleRingEquiv_algebraMap τ (l : L))

theorem map_range_diagonal (τ : L ≃+* L') :
    (IdeleGroup.diagonal L).range.map (ideleEquiv τ).toMulEquiv.toMonoidHom =
      (IdeleGroup.diagonal L').range := by
  ext y
  constructor
  · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
    exact ⟨_, (ideleEquiv_diagonal τ l).symm⟩
  · rintro ⟨l', rfl⟩
    refine ⟨IdeleGroup.diagonal L (Units.map (τ.symm : L' →* L) l'), ⟨_, rfl⟩, ?_⟩
    change ideleEquiv τ _ = _
    rw [ideleEquiv_diagonal]
    congr 1
    ext
    simp

def ideleClassEquiv (τ : L ≃+* L') : IdeleClassGroup L ≃ₜ* IdeleClassGroup L' where
  toMulEquiv := QuotientGroup.congr _ _ (ideleEquiv τ).toMulEquiv (map_range_diagonal τ)
  continuous_toFun := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact (IdeleClassGroup.continuous_mk L').comp (ideleEquiv τ).continuous
  continuous_invFun := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact (IdeleClassGroup.continuous_mk L).comp (ideleEquiv τ).symm.continuous

@[simp]
theorem ideleClassEquiv_mk (τ : L ≃+* L') (x : IdeleGroup L) :
    ideleClassEquiv τ (IdeleClassGroup.mk L x) = IdeleClassGroup.mk L' (ideleEquiv τ x) :=
  rfl

@[simp]
theorem ideleClassEquiv_refl (c : IdeleClassGroup L) : ideleClassEquiv (RingEquiv.refl L) c = c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassEquiv_mk, ideleEquiv_refl]

theorem ideleClassEquiv_trans (τ : L ≃+* L') (τ' : L' ≃+* L'') (c : IdeleClassGroup L) :
    ideleClassEquiv (τ.trans τ') c = ideleClassEquiv τ' (ideleClassEquiv τ c) := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassEquiv_mk, ideleClassEquiv_mk, ideleClassEquiv_mk, ideleEquiv_trans]

end Idele

section Relative

variable {K L L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L']

@[simp]
theorem ideleNorm_ideleEquiv (τ : L ≃ₐ[K] L') (x : IdeleGroup L) :
    ideleNorm K L' (ideleEquiv (τ : L ≃+* L') x) = ideleNorm K L x :=
  Units.ext (norm_adeleRingEquiv τ (x : 𝔸[L]))

@[simp]
theorem ideleClassNorm_ideleClassEquiv (τ : L ≃ₐ[K] L') (c : IdeleClassGroup L) :
    ideleClassNorm K L' (ideleClassEquiv (τ : L ≃+* L') c) = ideleClassNorm K L c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassEquiv_mk, ideleClassNorm_mk, ideleClassNorm_mk, ideleNorm_ideleEquiv]

end Relative

end

end GroundTheory.Global
