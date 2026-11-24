module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
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

open NumberField

def FirstInequality.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    (Module.finrank K L : ℕ∞) ≤ ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range)

section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem ideleClassNorm_range_eq_top_iff :
    (ideleClassNorm K L).range = ⊤ ↔
      (ideleNorm K L).range ⊔ (IdeleGroup.diagonal K).range = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc⟩ := (MonoidHom.mem_range).1 (h ▸ Subgroup.mem_top (IdeleClassGroup.mk K x))
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L c
    rw [ideleClassNorm_mk] at hc
    have hd : (ideleNorm K L y)⁻¹ * x ∈ (IdeleGroup.diagonal K).range :=
      QuotientGroup.eq.1 hc
    have : x = ideleNorm K L y * ((ideleNorm K L y)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ⟨y, rfl⟩ hd
  · intro h
    rw [eq_top_iff]
    intro c _
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
    obtain ⟨_, ⟨y, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 (h ▸ Subgroup.mem_top x)
    refine ⟨IdeleClassGroup.mk L y, ?_⟩
    rw [ideleClassNorm_mk, ← hyz]
    refine QuotientGroup.eq.2 ?_
    simpa using hz

end

section

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

theorem FirstInequality.finrank_eq_one_of_range_eq_top (hFI : FirstInequality.{u})
    (h : (ideleClassNorm K L).range = ⊤) : Module.finrank K L = 1 := by
  have hle := hFI K L
  rw [h] at hle
  have := QuotientGroup.subsingleton_quotient_top (G := IdeleClassGroup K)
  have h1 : ENat.card (IdeleClassGroup K ⧸ (⊤ : Subgroup (IdeleClassGroup K))) ≤ 1 :=
    (ENat.card_le_one_iff_subsingleton _).2 inferInstance
  have h2 : (Module.finrank K L : ℕ∞) ≤ 1 := hle.trans h1
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  have h3 : Module.finrank K L ≤ 1 := by exact_mod_cast h2
  omega

theorem FirstInequality.finrank_eq_one_of_sup_eq_top (hFI : FirstInequality.{u})
    (h : (ideleNorm K L).range ⊔ (IdeleGroup.diagonal K).range = ⊤) :
    Module.finrank K L = 1 :=
  hFI.finrank_eq_one_of_range_eq_top (ideleClassNorm_range_eq_top_iff.2 h)

end

end GroundTheory.Global
