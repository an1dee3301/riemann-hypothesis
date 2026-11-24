module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Unramified.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped nonZeroDivisors

namespace GlobalTheory.UnrTraceDual

theorem traceDual_ringOfIntegers_iff_of_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔ ∀ d ∈ differentIdeal ℤ (𝓞 F), IsIntegral ℤ (algebraMap F E (d : F) * e) := by
  intro F E _ _ _ _ _ hU e
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := inferInstance
  have hEq : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
      (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu, Ideal.top_mul]
  have hint : ∀ x : E, IsIntegral ℤ x ↔ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro x
    rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]
  have h1 : (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔
      e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
    constructor
    · intro h a ha
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 ha
      rw [Algebra.traceForm_apply, mul_comm]
      exact RingHom.mem_range.2 (IsIntegrallyClosed.isIntegral_iff.1 (h o))
    · intro h o
      have := h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).2 ⟨o, rfl⟩)
      rw [Algebra.traceForm_apply, mul_comm] at this
      exact IsIntegrallyClosed.isIntegral_iff.2 (RingHom.mem_range.1 this)
  have h2 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  have hne : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [h1, h2, FractionalIdeal.mem_inv_iff hne, hEq]
  let J : Ideal (𝓞 E) :=
    { carrier := {x | IsIntegral ℤ (algebraMap (𝓞 E) E x * e)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _), add_mul] at *
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, zero_mul]
        exact isIntegral_zero
      smul_mem' := by
        intro c x hx
        have hx' : IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := hx
        have hc : IsIntegral ℤ (algebraMap (𝓞 E) E c) := RingOfIntegers.isIntegral_coe c
        show IsIntegral ℤ (algebraMap (𝓞 E) E (c * x) * e)
        rw [map_mul, mul_assoc]
        exact IsIntegral.mul hc hx' }
  have hJ : ∀ x : 𝓞 E, x ∈ J ↔ IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := fun _ => Iff.rfl
  have hL : (∀ y ∈ (((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) : Ideal (𝓞 E)) :
      FractionalIdeal (𝓞 E)⁰ E), e * y ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔
      (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) ≤ J := by
    constructor
    · intro h x hx
      rw [hJ, hint, mul_comm]
      exact h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hx)
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      rw [mul_comm, ← hint]
      exact (hJ x).1 (h hx)
  rw [hL, Ideal.map_le_iff_le_comap]
  constructor
  · intro h d hd
    have := (hJ _).1 (h hd)
    rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
  · intro h d hd
    show algebraMap (𝓞 F) (𝓞 E) d ∈ J
    rw [hJ, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    exact h d hd

end GlobalTheory.UnrTraceDual
