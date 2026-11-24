module

public import Mathlib
public import GroundTheory.LocalFields.Interface
public import GroundTheory.LocalFields.Uniqueness
public import GroundTheory.LocalFields.Integers
public import GroundTheory.LocalFields.UnitsPowers
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Subtype
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

section RootsOfUnity

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem exists_pow_eq_one_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {a : 𝓀[L]} (ha : a ^ m = 1) :
    ∃ x : 𝒪[L], x ^ m = 1 ∧ IsLocalRing.residue 𝒪[L] x = a := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hmon : (X ^ m - C (1 : 𝒪[L])).Monic := monic_X_pow_sub_C 1 hm0
  have hev : (X ^ m - C (1 : 𝒪[L])).eval a₀ ∈ 𝓂[L] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp [ha]
  have hder : IsUnit (Ideal.Quotient.mk 𝓂[L] ((X ^ m - C (1 : 𝒪[L])).derivative.eval a₀)) := by
    have ha0 : IsLocalRing.residue 𝒪[L] a₀ ≠ 0 := by
      rintro h
      rw [h, zero_pow hm0] at ha
      exact zero_ne_one ha
    change IsUnit (IsLocalRing.residue 𝒪[L] _)
    rw [isUnit_iff_ne_zero]
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_pow,
      eval_X, eval_natCast, map_mul, map_pow, map_natCast]
    exact mul_ne_zero hm (pow_ne_zero _ ha0)
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian _ hmon a₀ hev hder
  refine ⟨x, ?_, ?_⟩
  · simpa [sub_eq_zero] using hx
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hxa

theorem eq_of_pow_eq_one_of_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {x y : 𝒪[L]}
    (hx : x ^ m = 1) (hy : y ^ m = 1)
    (h : IsLocalRing.residue 𝒪[L] x = IsLocalRing.residue 𝒪[L] y) : x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hxu : IsUnit x := (isUnit_pow_iff hm0).mp (hx ▸ isUnit_one)
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := X ^ m - C 1)
    (by simp [hx]) (by simp [hy]) ?_ ?_
  · rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, h, sub_self]
  · simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
      eval_pow, eval_X]
    refine IsUnit.mul ?_ (hxu.pow _)
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simpa using hm


omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
theorem mem_integer_of_pow_eq_one {m : ℕ} (hm : m ≠ 0) {x : L} (hx : x ^ m = 1) : x ∈ 𝒪[L] := by
  rw [Valuation.mem_integer_iff]
  have h : valuation L x ^ m = 1 := by rw [← map_pow, hx, map_one]
  refine le_of_not_gt fun h1 ↦ ?_
  have := one_lt_pow₀ h1 hm
  rw [h] at this
  exact this.false

theorem exists_isPrimitiveRoot_card_residueField_sub_one :
    ∃ ζ : 𝒪[L], IsPrimitiveRoot ζ (Nat.card 𝓀[L] - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := 𝓀[L]ˣ)
  have hpg : IsPrimitiveRoot (g : 𝓀[L]) (Nat.card 𝓀[L] - 1) := by
    rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg, ← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  obtain ⟨x, hx, hxg⟩ :=
    exists_pow_eq_one_residue_eq (natCast_card_residueField_sub_one_ne_zero L) hpg.pow_eq_one
  refine ⟨x, hx, fun l hl ↦ hpg.dvd_of_pow_eq_one l ?_⟩
  rw [← hxg, ← map_pow, hl, map_one]

end RootsOfUnity

section Degree

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem natDegree_minpoly_residue_le (x : 𝒪[L]) :
    (minpoly 𝓀[K] (IsLocalRing.residue 𝒪[L] x)).natDegree ≤ (minpoly K (x : L)).natDegree := by
  have hx : IsIntegral 𝒪[K] (x : L) := (isIntegral_iff K L x).mpr x.2
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, (minpoly.monic hx).natDegree_map]
  set g := minpoly 𝒪[K] (x : L)
  have hg0 : aeval x g = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero, ← minpoly.aeval 𝒪[K] (x : L)]
    exact (aeval_algebraMap_apply L x g).symm
  have hmon : (g.map (algebraMap 𝒪[K] 𝓀[K])).Monic := (minpoly.monic hx).map _
  refine (natDegree_le_natDegree (minpoly.min 𝓀[K] _ hmon ?_)).trans
    ((minpoly.monic hx).natDegree_map _).le
  rw [aeval_map_algebraMap, ← IsLocalRing.ResidueField.algebraMap_eq, aeval_algebraMap_apply, hg0,
    map_zero]

end Degree

end GroundTheory.LocalField
