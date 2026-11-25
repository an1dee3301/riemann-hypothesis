module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.CompleteTrivial
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.LocalField

open Finset

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

section Partial

variable (σ : L ≃ₐ[K] L) (x : Lˣ)

noncomputable def partialNorm (m : ℕ) : Lˣ :=
  ∏ j ∈ range m, (σ ^ j) • x

omit [FiniteDimensional K L] in
theorem partialNorm_add (a b : ℕ) :
    partialNorm σ x (a + b) = partialNorm σ x a * (σ ^ a) • partialNorm σ x b := by
  rw [partialNorm, prod_range_add, partialNorm, partialNorm, smul_prod']
  simp_rw [pow_add, mul_smul]

omit [FiniteDimensional K L] in
theorem partialNorm_one : partialNorm σ x 1 = x := by
  rw [partialNorm, prod_range_one, pow_zero, one_smul]

variable {σ}

theorem partialNorm_orderOf (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    partialNorm σ x (orderOf σ) = tateNorm (L ≃ₐ[K] L) Lˣ x := by
  rw [partialNorm, ← Fin.prod_univ_eq_prod_range, tateNorm_apply]
  refine Fintype.prod_bijective (fun j : Fin (orderOf σ) => σ ^ (j : ℕ)) ⟨?_, ?_⟩ _ _
    (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij)
  · intro g
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)
    refine ⟨⟨k % orderOf σ, Nat.mod_lt _ (orderOf_pos σ)⟩, ?_⟩
    change σ ^ (k % orderOf σ) = g
    rw [pow_mod_orderOf]
    exact hk

variable (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1)
include hσ hx

theorem partialNorm_add_orderOf (m : ℕ) :
    partialNorm σ x (m + orderOf σ) = partialNorm σ x m := by
  rw [add_comm, partialNorm_add, partialNorm_orderOf x hσ, hx, pow_orderOf_eq_one, one_smul, one_mul]

theorem partialNorm_mod (m : ℕ) : partialNorm σ x (m % orderOf σ) = partialNorm σ x m := by
  conv_rhs => rw [← Nat.mod_add_div m (orderOf σ)]
  induction m / orderOf σ with
  | zero => simp
  | succ q ih => rw [mul_add, mul_one, ← add_assoc, partialNorm_add_orderOf hσ hx, ih]

theorem partialNorm_eq_of_pow_eq {a b : ℕ} (h : σ ^ a = σ ^ b) :
    partialNorm σ x a = partialNorm σ x b := by
  rw [← partialNorm_mod hσ hx a, ← partialNorm_mod hσ hx b, (pow_eq_pow_iff_modEq.mp h)]

end Partial

theorem exists_smul_div_eq_of_tateNorm_eq_one {σ : L ≃ₐ[K] L}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : Lˣ} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1) :
    ∃ y : Lˣ, σ • y / y = x := by
  have hk : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g := fun g => by
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)
    exact ⟨k, hk⟩
  choose k hk using hk
  let f : (L ≃ₐ[K] L) → Lˣ := fun g => partialNorm σ x (k g)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    have e : σ ^ k (g * h) = σ ^ (k g + k h) := by rw [hk, pow_add, hk, hk]
    change partialNorm σ x (k (g * h)) = g • partialNorm σ x (k h) * partialNorm σ x (k g)
    rw [partialNorm_eq_of_pow_eq hσ hx e, partialNorm_add, hk, mul_comm]
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨β, ?_⟩
  rw [hβ σ]
  change partialNorm σ x (k σ) = x
  rw [partialNorm_eq_of_pow_eq hσ hx (show σ ^ k σ = σ ^ 1 by rw [hk, pow_one]), partialNorm_one]

theorem subsingleton_tateNegOne_units [IsCyclic (L ≃ₐ[K] L)] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) Lˣ) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  rw [subsingleton_tateNegOne_iff]
  intro x hx
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_tateNorm_eq_one hσ hx
  exact Subgroup.subset_closure ⟨σ, y, hy⟩

end GroundTheory.LocalField
