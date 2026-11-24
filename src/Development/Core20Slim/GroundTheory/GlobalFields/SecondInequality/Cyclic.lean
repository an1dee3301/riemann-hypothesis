module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.FirstInequality
public import Development.Core20Slim.GroundTheory.GlobalFields.SecondInequality.PowFinrankMemRangeInfiniteLocalNorm
public import Development.Core20Slim.GroundTheory.GlobalFields.SecondInequality.Reduction
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.SecondInequality.Statement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace GroundTheory.Global

open NumberField GroundTheory.GroupCoh Module

universe u

theorem secondInequality : SecondInequality.{u} :=
  (firstInequality.{u}.secondInequalityRoots).secondInequality

section

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem index_range_ideleClassNorm_eq_finrank [IsCyclic Gal(L/K)] :
    (ideleClassNorm K L).range.index = finrank K L := by
  obtain ⟨hge, hne⟩ := finrank_le_index_range_ideleClassNorm (K := K) (L := L)
  have hle := ((enatCard_quotient_le_iff _ _).1 (secondInequality.{u} K L)).2
  exact le_antisymm hle hge

theorem natCard_cycTateNegOne_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      = 1 := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨h, hpos⟩ := index_range_ideleClassNorm σ hσ
  rw [index_range_ideleClassNorm_eq_finrank] at h
  have hn : 0 < finrank K L := finrank_pos
  have h' : finrank K L * 1 = finrank K L * _ := (mul_one _).trans h
  exact (Nat.eq_of_mul_eq_mul_left hn h').symm

theorem natCard_cycTateZero_ideleClassGroup_eq_finrank (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      = finrank K L := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  rw [natCard_cycTateZero_ideleClassGroup σ hσ, index_range_ideleClassNorm_eq_finrank]

theorem classFieldAxiom_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        = finrank K L ∧
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        = 1 :=
  ⟨natCard_cycTateZero_ideleClassGroup_eq_finrank σ hσ, natCard_cycTateNegOne_ideleClassGroup σ hσ⟩

end

end GroundTheory.Global
