module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.HerbrandCyclic
public import Development.Core20Slim.GroundTheory.LocalFields.HilbertCyclic
public import Development.Core20Slim.GroundTheory.LocalFields.UnitsGalois
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.Cyclic
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Development.Core20Slim.GroundTheory.LocalFields.CompleteTrivial
public import GroundTheory.LocalFields.Uniqueness
public import GroundTheory.LocalFields.UnitsBasic
public import Development.Core20Slim.GroundTheory.TateCohomology.HerbrandAbstract
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Fixed
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]






end Galois

section Ord

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]


variable (L) in
def unitsOrd : Additive Lˣ →+ ℤ where
  toFun x := ord ((x.toMul : Lˣ) : L)
  map_zero' := by
    have := ord_unit (K := L) 1
    simpa using this
  map_add' x y := by
    change ord (((x.toMul * y.toMul : Lˣ)) : L) = _
    rw [Units.val_mul, ord_mul x.toMul.ne_zero y.toMul.ne_zero]

theorem unitsOrd_ofMul (x : Lˣ) : unitsOrd (L := L) (Additive.ofMul x) = ord (x : L) :=
  rfl

theorem unitsOrd_surjective : Function.Surjective (unitsOrd (L := L)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  intro n
  refine ⟨n • Additive.ofMul (uniformizerUnit hϖ), ?_⟩
  rw [map_zsmul, unitsOrd_ofMul, coe_uniformizerUnit, ord_uniformizer hϖ, smul_eq_mul, mul_one]

theorem ord_eq_zero_iff_mem_range_unitsIncl (x : Lˣ) :
    ord (x : L) = 0 ↔ x ∈ (unitsIncl L).range := by
  rw [ord_eq_zero_iff_mem, unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map]

theorem exact_unitsIncl_unitsOrd :
    Function.Exact (MonoidHom.toAdditive (unitsIncl L)) (unitsOrd (L := L)) := by
  intro y
  change ord ((y.toMul : Lˣ) : L) = 0 ↔ _
  rw [ord_eq_zero_iff_mem_range_unitsIncl]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, Additive.toMul.injective hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.toMul, rfl⟩

end Ord

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem ord_algEquiv (σ : L ≃ₐ[K] L) (x : L) : ord (σ x) = ord x := by
  rw [ord, ord, normalizedValuation_apply, normalizedValuation_apply,
    valuation_algEquiv_apply K L σ x]

theorem unitsOrd_smul (σ : L ≃ₐ[K] L) (x : Lˣ) :
    unitsOrd (L := L) (Additive.ofMul (σ • x)) = unitsOrd (L := L) (Additive.ofMul x) := by
  rw [unitsOrd_ofMul, unitsOrd_ofMul, AlgEquiv.smul_units_def, Units.coe_map]
  exact ord_algEquiv σ x

theorem unitsOrd_cycSubOne (τ : L ≃ₐ[K] L) (x : Additive Lˣ) :
    unitsOrd (L := L) (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) τ x) =
      cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) τ (unitsOrd (L := L) x) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, Representation.ofMulDistribMulAction_apply_apply,
    unitsOrd_smul, Representation.trivial_apply]
  rfl

theorem unitsOrd_cycNorm (x : Additive Lˣ) :
    unitsOrd (L := L) (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) x) =
      cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) (unitsOrd (L := L) x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cycNorm_apply, cycNorm_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Representation.ofMulDistribMulAction_apply_apply, unitsOrd_smul, Representation.trivial_apply]
  rfl

variable {σ : L ≃ₐ[K] L}

theorem cycHerbrand_units_eq_mul (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (hA : HasHerbrandQuotient
      (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
      (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ))) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ *
          Fintype.card (L ≃ₐ[K] L) := by
  have hi : Function.Injective (MonoidHom.toAdditive (unitsIncl L)) := unitsIncl_injective
  have hC : HasHerbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) :=
    hasCyclicHerbrand_of_finite (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) hσ
  have hCv : herbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) = Fintype.card (L ≃ₐ[K] L) :=
    cyclicHerbrand_trivial_int σ
  refine ⟨HasHerbrandQuotient.of_shortExact_left_right hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, ?_⟩
  rw [cycHerbrand, herbrandQuotient_eq_mul_of_shortExact hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, hCv]
  rfl

theorem cycHerbrand_integerUnits_eq_one_of_subgroup (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (V : Subgroup 𝒪[L]ˣ) [V.FiniteIndex] [MulDistribMulAction (L ≃ₐ[K] L) V]
    (hV : ∀ (g : L ≃ₐ[K] L) (v : V), ((g • v : V) : 𝒪[L]ˣ) = g • (v : 𝒪[L]ˣ))
    [Subsingleton (TateZero (L ≃ₐ[K] L) V)] [Subsingleton (TateNegOne (L ≃ₐ[K] L) V)] :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  have : V.subtype.range.FiniteIndex := by rw [Subgroup.range_subtype]; infer_instance
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_injective V.subtype V.subtype_injective hV σ
  obtain ⟨h3, h4⟩ := cycHerbrand_eq_one_of_subsingleton (G := L ≃ₐ[K] L) (M := V) hσ
  exact ⟨h1.mp h3, h2.symm.trans h4⟩

end GroundTheory.LocalField
