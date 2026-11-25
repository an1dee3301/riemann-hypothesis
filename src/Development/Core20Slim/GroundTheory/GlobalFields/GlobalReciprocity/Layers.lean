module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.GlobalReciprocity.InfKerDegreeLeOfLeSupZhatField
public import Development.Core20Slim.GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import Development.Core20Slim.GroundTheory.GlobalFields.CyclotomicCharacters.Degree
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassEquivIdeleClassMapOfComm
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassMapIdeleClassMap
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.Invariants
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleClassGroup.Theory
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.Cyclotomic
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicImage
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RationalCyclotomic
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Isomorphism
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Unramified
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Valuation
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Subtype.Order
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.IntermediateField
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
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.PNat.Notation
public import Mathlib.Data.ZMod.Basic
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
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract IdeleGroup
open scoped GroundTheory.LocalField.Abstract

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace IdeleClassLimit

open FiniteSubfield RationalSymbol CyclotomicSymbol _root_.GroundTheory.Global.Cyclotomic ProfiniteInteger

theorem val_norm_fixedEquiv (K : FiniteSubfield) (a : IdeleClassGroup K.1) :
    val (norm IdeleClassLimit ⊤ K.1.fixingSubgroup (fixedEquiv K a)) = cycDegree (cycSymbol K a) := by
  have h := val_norm_of (U := K.1.fixingSubgroup) rfl a (fixedEquiv K a).2
  convert h using 3
  exact Subtype.ext (coe_fixedEquiv K a)

theorem degree_eq_valuation_pow (K : FiniteSubfield) (a : IdeleClassGroup K.1) {g : ℚ̄ ≃ₐ[ℚ] ℚ̄}
    (hg : cycRestrict g = cycSymbol K a) :
    classFieldTheory.deg g =
      classFieldTheory.valuation K.openSubgroup (fixedEquiv K a) ^
        inertiaDegree classFieldTheory.deg (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
  have h3 : degree g = cycDegree (cycSymbol K a) := by
    rw [← hg, ← MonoidHom.comp_apply, cycDegree_comp_cycRestrict]
  rw [classFieldTheory.valuation_pow K.openSubgroup (fixedEquiv K a)]
  convert h3.trans (val_norm_fixedEquiv K a).symm using 2
  · exact classFieldTheory_deg
  · rfl

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem abstractSymbol_eq_of_cycRestrict_eq (hL : L.1 ≤ K.1 ⊔ zhatField) (a : IdeleClassGroup K.1)
    (g : K.1.fixingSubgroup) (hg : cycRestrict (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) = cycSymbol K a) :
    abstractSymbol K L a = Group.Abelianization.of (restrictHom g) := by
  set D := classFieldTheory.toClassFieldData
  have hLK : L.openSubgroup ≤ K.openSubgroup := openSubgroup_le hKL.out
  have hu : (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ⊓ D.deg.ker ≤ L.openSubgroup :=
    inf_ker_degree_le_of_le_sup_zhatField K L hL
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K.openSubgroup (Multiplicative.ofAdd 1)
  have hr := D.reciprocityAbEquiv_symm_of_unramified hLK classFieldTheory.classFieldAxiom hu hφ
    (fixedEquiv K a)
  set f := D.relInertiaDegreePNat hLK with hf
  set z := Multiplicative.toAdd (D.valuation K.openSubgroup (fixedEquiv K a)) with hz
  set n := (proj f z).val with hn

  obtain ⟨y, hy⟩ : ∃ y : ℤ̂, z - (n : ℤ̂) = (f : ℕ) • y := by
    refine exists_eq_nsmul_of_proj_eq_zero ?_
    rw [map_sub, map_natCast, hn, ZMod.natCast_zmod_val, sub_self]

  have hmem : ((φ ^ n)⁻¹ * g : (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))) ∈
      (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf K.openSubgroup := by
    rw [Subgroup.mem_subgroupOf, mem_iff_map_mem_of_unramified (d := D.deg) hLK hu
      ((φ ^ n)⁻¹ * g : (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))).2,
      D.mem_map_deg_iff L.openSubgroup]
    refine ⟨Multiplicative.ofAdd y, ?_⟩
    have hφd : D.deg φ = Multiplicative.ofAdd 1 ^ inertiaDegree D.deg
        (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
      rw [← D.relDeg_pow K.openSubgroup φ, hφ]
    have hgd : D.deg g = D.valuation K.openSubgroup (fixedEquiv K a) ^
        inertiaDegree D.deg (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
      degree_eq_valuation_pow K a hg
    rw [inertiaDegree_eq_mul D.surjective_deg hLK]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow, map_mul, map_inv, map_pow]
    rw [hφd, show D.deg (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) = _ from hgd]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_mul, toAdd_inv, toAdd_ofAdd]
    change _ = _ + _ • z
    rw [sub_eq_iff_eq_add'.1 hy, hf, ClassFieldData.coe_relInertiaDegreePNat]
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  have e : (reciprocityEquiv K L).symm (normClass K L a) =
      Group.Abelianization.of (QuotientGroup.mk (s := (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)).subgroupOf
        K.openSubgroup) g) := by
    refine hr.trans ?_
    rw [← map_pow, ← QuotientGroup.mk_pow]
    exact congrArg _ (QuotientGroup.eq.2 hmem)
  rw [abstractSymbol_apply, e, Group.Abelianization.map_of]
  rfl

theorem abstractSymbol_mk_of_le_sup_zhatField [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]
    (hL : L.1 ≤ K.1 ⊔ zhatField) (x : IdeleGroup K.1) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 x) =
      Group.Abelianization.of (ideleSymbol K.1 L.1 x) := by
  obtain ⟨g, hgK, hg⟩ := exists_mem_fixingSubgroup_cycRestrict_eq K (IdeleClassGroup.mk K.1 x)
  rw [abstractSymbol_eq_of_cycRestrict_eq K L hL _ ⟨g, hgK⟩ hg,
    restrictHom_eq_ideleSymbol_of_le_sup K L (hL.trans (sup_le_sup_left zhatField_le_maxCyclotomic _))
      ⟨g, hgK⟩ x hg]

end IdeleClassLimit

end

end GroundTheory.Global
