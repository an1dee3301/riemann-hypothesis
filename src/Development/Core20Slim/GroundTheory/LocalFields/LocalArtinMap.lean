module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.MaximalAbelianExtension
public import Development.Core20Slim.GroundTheory.LocalFields.LocalReciprocityUniversal
public import Development.Core20Slim.GroundTheory.LocalFields.Existence
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
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
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
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
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.ZMod

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel GroundTheory.LocalField.FormalGroup


variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Def


variable (K Ω) in
def localArtinMap :
    Kˣ →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  (topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom.comp (localReciprocityLimit K Ω)

theorem localArtinMap_apply (x : Kˣ) :
    localArtinMap K Ω x = topologicalAbelianizationEquiv K Ω (localReciprocityLimit K Ω x) :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem restrictAb_topologicalAbelianizationEquiv_eq_abelianRestrict (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsAbelianGalois K L] (g : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :
    restrictAb L (le_maximalAbelianExtension L) (topologicalAbelianizationEquiv K Ω g) =
      abelianRestrict L g := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  rw [restrictAb_topologicalAbelianizationEquiv]
  rfl

theorem restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] (x : Kˣ) :
    restrictAb L (le_maximalAbelianExtension L) (localArtinMap K Ω x) =
      (localReciprocityAbelian L).symm (x : Kˣ ⧸ (normUnits K L).range) := by
  rw [localArtinMap_apply, restrictAb_topologicalAbelianizationEquiv_eq_abelianRestrict,
    abelianRestrict_localReciprocityLimit]

theorem ker_restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)).ker =
      (normUnits K L).range := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, restrictAb_localArtinMap, MulEquiv.map_eq_one_iff,
    QuotientGroup.eq_one_iff]

theorem surjective_restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    Function.Surjective ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)) := by
  intro σ
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (localReciprocityAbelian L σ)
  refine ⟨x, ?_⟩
  rw [MonoidHom.comp_apply, restrictAb_localArtinMap, hx, MulEquiv.symm_apply_apply]

end Def

section Unramified

instance isAbelianGalois_maximalUnramifiedExtension :
    IsAbelianGalois K (maximalUnramifiedExtension K Ω) :=
  { toIsMulCommutative := ⟨⟨fun σ τ => (maximalUnramifiedExtensionGaloisEquiv K Ω).injective (by
      rw [map_mul, map_mul, mul_comm])⟩⟩ }

theorem maximalUnramifiedExtension_le_maximalAbelianExtension :
    maximalUnramifiedExtension K Ω ≤ maximalAbelianExtension K Ω :=
  le_maximalAbelianExtension _

theorem restrictAb_localArtinMap_uniformizer {π : Kˣ} (hπ : ord (π : K) = 1) :
    restrictAb (maximalUnramifiedExtension K Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
      (localArtinMap K Ω π) = maximalUnramifiedExtensionFrobenius K Ω := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (localReciprocityLimit K Ω π)
  rw [localArtinMap_apply, ← hg, restrictAb_topologicalAbelianizationEquiv]
  exact restrictNormal_eq_frobenius_of_mk_eq_localReciprocityLimit hπ hg


theorem localArtinMap_uniformizer_apply {π : Kˣ} (hπ : ord (π : K) = 1) {y : Ω}
    (hy : y ∈ maximalUnramifiedExtension K Ω) :
    ((localArtinMap K Ω π ⟨y, maximalUnramifiedExtension_le_maximalAbelianExtension hy⟩ :
      maximalAbelianExtension K Ω) : Ω) =
      (maximalUnramifiedExtensionFrobenius K Ω ⟨y, hy⟩ : Ω) := by
  rw [← restrictAb_localArtinMap_uniformizer hπ, restrictAb_apply]

end Unramified

section Topology


end Topology

section Injective



end Injective

end GroundTheory.LocalField
