module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.Theory
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.Cyclotomic
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Isomorphism
public import Development.Core20Slim.GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import Development.Core20Slim.GroundTheory.GlobalFields.CyclotomicCharacters.Degree
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassEquivIdeleClassMapOfComm
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassMapIdeleClassMap
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.Invariants
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Unramified
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Subtype.Order
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
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
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.PNat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract
open scoped GroundTheory.LocalField.Abstract

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace FiniteSubfield

abbrev openSubgroup (F : FiniteSubfield) : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄) :=
  ⟨F.1.fixingSubgroup, F.1.fixingSubgroup_isOpen⟩

theorem openSubgroup_le {F E : FiniteSubfield} (h : F ≤ E) : E.openSubgroup ≤ F.openSubgroup :=
  fun _ hx ↦ IntermediateField.fixingSubgroup_le (show F.1 ≤ E.1 from h) hx

variable (F E : FiniteSubfield) [Fact (F ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal]

def quotientGaloisEquiv :
    ((F.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ⧸
        (E.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf F.openSubgroup) ≃*
      (E.1 ≃ₐ[F.1] E.1) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_restrictHom (F := F) (E := E)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (restrictHom_surjective (F := F) (E := E)))

@[simp]
theorem quotientGaloisEquiv_mk (g : F.1.fixingSubgroup) :
    quotientGaloisEquiv F E
        (QuotientGroup.mk (s := (E.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf F.openSubgroup) g) =
      restrictHom g :=
  rfl

end FiniteSubfield

namespace IdeleClassLimit

open FiniteSubfield RationalSymbol CyclotomicSymbol _root_.GroundTheory.Global.Cyclotomic

section Map

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

abbrev reciprocityEquiv :
    Group.Abelianization ((K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ⧸
        (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf K.openSubgroup) ≃*
      tateZero IdeleClassLimit (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) L.openSubgroup :=
  classFieldTheory.toClassFieldData.reciprocityAbEquiv (openSubgroup_le hKL.out)
    classFieldTheory.classFieldAxiom

abbrev normClass : IdeleClassGroup K.1 →*
    tateZero IdeleClassLimit (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) L.openSubgroup :=
  (QuotientGroup.mk' (norm IdeleClassLimit (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
    (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))).range).comp (fixedEquiv K).toMonoidHom

def abstractSymbol : IdeleClassGroup K.1 →* Group.Abelianization (L.1 ≃ₐ[K.1] L.1) :=
  (Group.Abelianization.map (quotientGaloisEquiv K L).toMonoidHom).comp
    ((reciprocityEquiv K L).symm.toMonoidHom.comp (normClass K L))

theorem abstractSymbol_apply (c : IdeleClassGroup K.1) :
    abstractSymbol K L c = Group.Abelianization.map (quotientGaloisEquiv K L).toMonoidHom
      ((reciprocityEquiv K L).symm (normClass K L c)) :=
  rfl

end Map

section Layers

variable (K L : FiniteSubfield)

theorem inf_ker_degree_le_of_le_sup_zhatField (hL : L.1 ≤ K.1 ⊔ zhatField) :
    K.1.fixingSubgroup ⊓ degree.ker ≤ L.1.fixingSubgroup := by
  rw [← fixingSubgroup_zhatField, ← IntermediateField.fixingSubgroup_sup]
  exact IntermediateField.fixingSubgroup_le hL

theorem normal_of_le_sup_zhatField (hKL : K ≤ L) (hL : L.1 ≤ K.1 ⊔ zhatField) :
    (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal :=
  normal_of_unramified (d := degree)
    (IntermediateField.fixingSubgroup_le (show K.1 ≤ L.1 from hKL))
    (inf_ker_degree_le_of_le_sup_zhatField K L hL)

variable [Fact (K ≤ L)] [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem isMulCommutative_of_le_sup_zhatField (hL : L.1 ≤ K.1 ⊔ zhatField) :
    IsMulCommutative (L.1 ≃ₐ[K.1] L.1) := by
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  obtain ⟨g, rfl⟩ := restrictHom_surjective (F := K) (E := L) σ
  obtain ⟨h, rfl⟩ := restrictHom_surjective (F := K) (E := L) τ
  have hk : (h * g)⁻¹ * (g * h) ∈ (restrictHom (F := K) (E := L)).ker := by
    rw [ker_restrictHom, Subgroup.mem_subgroupOf]
    refine inf_ker_degree_le_of_le_sup_zhatField K L hL ⟨((h * g)⁻¹ * (g * h)).2, MonoidHom.mem_ker.2 ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [mul_comm (degree (h : ℚ̄ ≃ₐ[ℚ] ℚ̄)) (degree (g : ℚ̄ ≃ₐ[ℚ] ℚ̄))]
    exact inv_mul_cancel _
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
  rw [← map_mul, ← map_mul]
  exact hk.symm

end Layers

end IdeleClassLimit

end

end GroundTheory.Global
