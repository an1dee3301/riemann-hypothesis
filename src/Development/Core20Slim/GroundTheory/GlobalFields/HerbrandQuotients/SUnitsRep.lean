module

public import Mathlib
public import GroundTheory.GlobalFields.SUnits
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm
public import GroundTheory.GlobalFields.SUnitsKernel
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain NumberField.Units
open scoped Pointwise

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

section Units

variable [NumberField L]

def unitsMap (g : L ≃ₐ[K] L) : (𝓞 L)ˣ →* (𝓞 L)ˣ :=
  Units.map (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) g : 𝓞 L →* 𝓞 L)

variable (K L) in
def unitsRep : Representation ℤ (L ≃ₐ[K] L) (Additive (𝓞 L)ˣ) where
  toFun g := (unitsMap g).toAdditive.toIntLinearMap
  map_one' := by
    refine LinearMap.ext fun u => ?_
    apply Additive.toMul.injective
    apply Units.ext
    apply RingOfIntegers.ext
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun u => ?_
    apply Additive.toMul.injective
    apply Units.ext
    apply RingOfIntegers.ext
    rfl

omit [NumberField L] in
theorem unitsRep_apply (g : L ≃ₐ[K] L) (u : Additive (𝓞 L)ˣ) :
    unitsRep K L g u = Additive.ofMul (unitsMap g u.toMul) :=
  rfl

end Units

section SUnits

variable [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L)))

theorem map_mem_unit (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) {x : Lˣ}
    (hx : x ∈ S.unit L) : Units.map (g : L →+* L).toMonoidHom x ∈ S.unit L := by
  intro w hw
  have hw' : g⁻¹ • w ∉ S := fun h => hw (by simpa using hS g _ h)
  have h1 := SemiLocal.valuation_smul g (g⁻¹ • w) (x : L)
  rw [smul_inv_smul] at h1
  change w.valuation L (g (x : L)) = 1
  rw [h1]
  exact hx _ hw'

def sUnitMap (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) :
    S.unit L →* S.unit L :=
  ((Units.map (g : L →+* L).toMonoidHom).comp (S.unit L).subtype).codRestrict (S.unit L)
    fun x => map_mem_unit S hS g x.2

theorem coe_sUnitMap (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L)
    (x : S.unit L) : (((sUnitMap S hS g x : S.unit L) : Lˣ) : L) = g ((x : Lˣ) : L) :=
  rfl

def sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    Representation ℤ (L ≃ₐ[K] L) (Additive (S.unit L)) where
  toFun g := (sUnitMap S hS g).toAdditive.toIntLinearMap
  map_one' := by
    refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl

theorem sUnitRep_apply (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L)
    (x : Additive (S.unit L)) :
    sUnitRep S hS g x = Additive.ofMul (sUnitMap S hS g x.toMul) :=
  rfl

theorem ofUnits_unitsRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L)
    (u : Additive (𝓞 L)ˣ) :
    (SUnit.ofUnits S).toAdditive (unitsRep K L g u) =
      sUnitRep S hS g ((SUnit.ofUnits S).toAdditive u) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rfl

theorem valuationVector_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S)
    (g : L ≃ₐ[K] L) (x : Additive (S.unit L)) :
    letI _ := stableMulAction S hS
    SUnit.valuationVector S (sUnitRep S hS g x) =
      funPermRep ℤ (L ≃ₐ[K] L) S g (SUnit.valuationVector S x) := by
  let _ := stableMulAction S hS
  funext w
  rw [funPermRep_apply, ← ofMul_toMul x, sUnitRep_apply, toMul_ofMul,
    SUnit.valuationVector_apply, SUnit.valuationVector_apply]
  congr 1
  rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq,
    HeightOneSpectrum.valuationOfNeZero_eq, coe_sUnitMap]
  have h1 := SemiLocal.valuation_smul g (g⁻¹ • w.1) ((x.toMul : Lˣ) : L)
  rw [smul_inv_smul] at h1
  exact h1

end SUnits

end

end GroundTheory.Global
