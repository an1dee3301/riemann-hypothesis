module

public import Mathlib
public import Init.Core
public import Init.Data.Function
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace GroundTheory.Variant₂.N1

open Subgroup

theorem relIndex_sup_of_le_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) : H.relIndex (H ⊔ N) = H.relIndex N := by
  symm
  let f : N →* (H ⊔ N : Subgroup G) := Subgroup.inclusion le_sup_right
  let g : N ⧸ H.subgroupOf N → (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N) :=
    fun q => Quotient.liftOn' q (fun n => ((f n : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N))) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab
      rw [QuotientGroup.eq, mem_subgroupOf]
      simpa [f] using hab)
  have hinj : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    have h1 : ((f a : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) =
        ((f b : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) := hxy
    rw [QuotientGroup.eq, mem_subgroupOf] at h1
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using h1
  have hsurj : Function.Surjective g := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
    obtain ⟨y, hy⟩ := k
    have hy' : y ∈ ((N ⊔ H : Subgroup G) : Set G) := by
      rw [sup_comm]; exact hy
    rw [coe_mul_of_right_le_normalizer_left N H hLE] at hy'
    obtain ⟨n, hn, h, hh, rfl⟩ := hy'
    refine ⟨((⟨n, hn⟩ : N) : N ⧸ H.subgroupOf N), ?_⟩
    change ((f ⟨n, hn⟩ : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) = _
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using hh
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  exact Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)

end GroundTheory.Variant₂.N1
