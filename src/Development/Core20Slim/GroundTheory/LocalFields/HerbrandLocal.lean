module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.HerbrandLocalBase
public import Development.Core20Slim.GroundTheory.LocalFields.CompleteTrivialLocal
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Development.Core20Slim.GroundTheory.LocalFields.CompleteTrivial
public import Development.Core20Slim.GroundTheory.LocalFields.HerbrandCyclic
public import Development.Core20Slim.GroundTheory.LocalFields.HilbertCyclic
public import GroundTheory.LocalFields.Integers
public import Development.Core20Slim.GroundTheory.LocalFields.UnitsGalois
public import Development.Core20Slim.GroundTheory.TateCohomology.HerbrandAbstract
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] in
theorem finiteIndex_of_isOpen_integerUnits {V : Subgroup 𝒪[L]ˣ} (h : IsOpen (V : Set 𝒪[L]ˣ)) :
    V.FiniteIndex := by
  have : Finite (𝒪[L]ˣ ⧸ V) := Subgroup.quotient_finite_of_isOpen V h
  exact Subgroup.finiteIndex_of_finite_quotient

variable [IsGalois K L] {σ : L ≃ₐ[K] L}

theorem cycHerbrand_integerUnits_eq_one (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  obtain ⟨-, -, -, -, -, -, -, V, hV, -, hopen, hT⟩ :=
    exists_openSubgroup_units_tateTrivial (K := K) (L := L)
  let := stableUnitsAction V hV
  have := finiteIndex_of_isOpen_integerUnits hopen
  have := hT.1
  have := hT.2
  exact cycHerbrand_integerUnits_eq_one_of_subgroup hσ V
    fun g v => Units.ext (Subtype.ext (unitVal_smul V hV g v))

theorem cycHerbrand_units_eq_finrank (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        Module.finrank K L := by
  obtain ⟨hA, h1⟩ := cycHerbrand_integerUnits_eq_one hσ
  obtain ⟨hB, h2⟩ := cycHerbrand_units_eq_mul hσ hA
  refine ⟨hB, ?_⟩
  rw [h2, h1, one_mul, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

variable [IsCyclic (L ≃ₐ[K] L)]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L] in
theorem natCard_tateNegOne_units : Nat.card (TateNegOne (L ≃ₐ[K] L) Lˣ) = 1 := by
  have := subsingleton_tateNegOne_units (K := K) (L := L)
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

theorem natCard_tateZero_units :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Module.finrank K L := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have h := (cycHerbrand_units_eq_finrank hτ).2
  rw [cycHerbrand_ofMulDistribMulAction hτ, natCard_tateNegOne_units, Nat.cast_one, div_one] at h
  exact_mod_cast h


end GroundTheory.LocalField
