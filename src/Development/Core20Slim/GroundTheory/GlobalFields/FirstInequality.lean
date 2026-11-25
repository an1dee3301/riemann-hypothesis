module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.FirstInequality.HerbrandClass
public import Development.Core20Slim.GroundTheory.GlobalFields.FirstInequalityStatement
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.TateCohomology.HerbrandAbstract
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
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
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Congruence.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open NumberField GroundTheory.GroupCoh Module

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (K L) in
def ideleClassToCycTateZero (σ : Gal(L/K)) :
    Additive (IdeleClassGroup K) →+
      CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ :=
  (QuotientAddGroup.mk' _).comp ((ideleClassMap K L).toAdditive.codRestrict _ fun c ↦ by
    rw [AddMonoidHom.mem_ker, cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply,
      sub_eq_zero]
    exact congrArg Additive.ofMul (smul_ideleClassMap σ _))

theorem ideleClassToCycTateZero_apply (σ : Gal(L/K)) (c : Additive (IdeleClassGroup K)) :
    ideleClassToCycTateZero K L σ c = QuotientAddGroup.mk ⟨Additive.ofMul (ideleClassMap K L c.toMul),
      by
        rw [AddMonoidHom.mem_ker, cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply,
          sub_eq_zero]
        exact congrArg Additive.ofMul (smul_ideleClassMap σ _)⟩ :=
  rfl

section Galois

variable [IsGalois K L]

theorem cycNorm_ideleClassGroup (c : Additive (IdeleClassGroup L)) :
    cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) c =
      Additive.ofMul (ideleClassMap K L (ideleClassNorm K L c.toMul)) := by
  rw [cycNorm_apply, ideleClassMap_ideleClassNorm]
  simp only [Representation.ofMulDistribMulAction_apply_apply]
  rfl

theorem ideleClassToCycTateZero_surjective (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : Function.Surjective (ideleClassToCycTateZero K L σ) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H y =>
  obtain ⟨y, hy⟩ := y
  have hfix := (mem_ker_cycSubOne_iff _ hσ y).1 hy
  obtain ⟨c, hc⟩ := (forall_smul_eq_iff_mem_range_ideleClassMap (K := K) y.toMul).1 fun g ↦
    congrArg Additive.toMul (hfix g)
  refine ⟨Additive.ofMul c, ?_⟩
  rw [ideleClassToCycTateZero_apply]
  congr 1
  exact Subtype.ext (by simp [hc])

theorem ker_ideleClassToCycTateZero (σ : Gal(L/K)) :
    (ideleClassToCycTateZero K L σ).ker = Subgroup.toAddSubgroup (ideleClassNorm K L).range := by
  ext c
  rw [AddMonoidHom.mem_ker, ideleClassToCycTateZero_apply, KerModRange.mk_eq_zero_iff]
  change _ ↔ c.toMul ∈ (ideleClassNorm K L).range
  rw [AddMonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨d, hd⟩
    rw [cycNorm_ideleClassGroup] at hd
    exact ⟨d.toMul, ideleClassMap_injective (congrArg Additive.toMul hd)⟩
  · rintro ⟨d, hd⟩
    refine ⟨Additive.ofMul d, ?_⟩
    rw [cycNorm_ideleClassGroup]
    simp [hd]

theorem natCard_cycTateZero_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ) =
      (ideleClassNorm K L).range.index := by
  rw [← Subgroup.index_toAddSubgroup, ← ker_ideleClassToCycTateZero σ, AddSubgroup.index]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
    (ideleClassToCycTateZero_surjective σ hσ)).toEquiv).symm

theorem index_range_ideleClassNorm (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (ideleClassNorm K L).range.index = finrank K L *
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ) ∧
    Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      ≠ 0 := by
  obtain ⟨hH, hval⟩ := IdeleGroup.cycHerbrand_ideleClassGroup (K := K) (L := L) σ hσ
  have := hH.2
  have hpos : Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      (IdeleClassGroup L)) σ) ≠ 0 := Nat.card_pos.ne'
  refine ⟨?_, hpos⟩
  rw [cycHerbrand_eq, natCard_cycTateZero_ideleClassGroup σ hσ,
    div_eq_iff (Nat.cast_ne_zero.2 hpos)] at hval
  exact_mod_cast hval

theorem finrank_le_index_range_ideleClassNorm [IsCyclic Gal(L/K)] :
    finrank K L ≤ (ideleClassNorm K L).range.index ∧ (ideleClassNorm K L).range.index ≠ 0 := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨h, hpos⟩ := index_range_ideleClassNorm σ hσ
  rw [h]
  exact ⟨Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hpos),
    mul_ne_zero Module.finrank_pos.ne' hpos⟩

end Galois

theorem firstInequality.{u} : FirstInequality.{u} := by
  intro K L _ _ _ _ _ _ _
  obtain ⟨hle, hne⟩ := finrank_le_index_range_ideleClassNorm (K := K) (L := L)
  have : (ideleClassNorm K L).range.FiniteIndex := ⟨hne⟩
  have : Finite (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) :=
    Subgroup.finite_quotient_of_finiteIndex
  let := Fintype.ofFinite (IdeleClassGroup K ⧸ (ideleClassNorm K L).range)
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_eq_nat_card]
  exact_mod_cast hle

end

end GroundTheory.Global
