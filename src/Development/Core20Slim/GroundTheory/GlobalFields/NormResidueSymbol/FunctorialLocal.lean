module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import Development.Core20Slim.GroundTheory.LocalFields.LocalArtinAbstractField
public import Development.Core20Slim.GroundTheory.LocalFields.MainTheorem
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Development.Core20Slim.GroundTheory.LocalFields.LocalArtinFunctoriality
public import Development.Core20Slim.GroundTheory.LocalFields.LocalArtinMap
public import Development.Core20Slim.GroundTheory.LocalFields.LocalReciprocityUniversal
public import Development.Core20Slim.GroundTheory.LocalFields.MaximalAbelianExtension
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import Mathlib.Topology.Defs.Basic

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open LocalField

noncomputable section

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] {M : Type*} [Field M] [Algebra k M] [FiniteDimensional k M] [IsGalois k M]
  [IsMulCommutative (M ≃ₐ[k] M)]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  [FiniteDimensional k M] in
theorem isAbelianGalois_of_isGalois : IsAbelianGalois k M :=
  { toIsGalois := inferInstance, toIsMulCommutative := inferInstance }


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  [FiniteDimensional k M] in
theorem apply_mem_maximalAbelianExtension {Ω : Type*} [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (ι : M →ₐ[k] Ω) (z : M) : ι z ∈ maximalAbelianExtension k Ω :=
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  have := isAbelianGalois_fieldRange ι
  le_maximalAbelianExtension ι.fieldRange ⟨z, rfl⟩

theorem normResidueSymbol_eq_localArtinMapOfField :
    have := isAbelianGalois_of_isGalois (k := k) (M := M)
    normResidueSymbol k M = localArtinMapOfField k M := by
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  ext x z
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := k) x
  apply (residueEmbedding k M).injective
  change residueEmbedding k M _ = residueEmbedding k M _
  rw [residueEmbedding_normResidueSymbol hτ,
    localArtinMapOfField_eq_artinOfEmbedding (residueEmbedding k M), apply_artinOfEmbedding,
    localArtinMap_apply, ← hτ, topologicalAbelianizationEquiv_mk_apply]

theorem normResidueSymbol_apply_eq_localArtinMap {Ω : Type*} [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (ι : M →ₐ[k] Ω) (x : kˣ) (z : M) :
    ι (normResidueSymbol k M x z) =
      ((localArtinMap k Ω x ⟨ι z, apply_mem_maximalAbelianExtension ι z⟩ :
        maximalAbelianExtension k Ω) : Ω) := by
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  rw [normResidueSymbol_eq_localArtinMapOfField, localArtinMapOfField_eq_artinOfEmbedding ι,
    apply_artinOfEmbedding]

variable {k' : Type*} [Field k'] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] [CharZero k'] [Algebra k k'] [ValuativeExtension k k']
  [FiniteDimensional k k']
  {M' : Type*} [Field M'] [Algebra k' M'] [Algebra k M'] [IsScalarTower k k' M']
  [FiniteDimensional k' M'] [IsGalois k' M'] [IsMulCommutative (M' ≃ₐ[k'] M')]

theorem normResidueSymbol_norm (j : M →ₐ[k] M') (x : k'ˣ) (z : M) :
    normResidueSymbol k' M' x (j z) = j (normResidueSymbol k M (normUnits k k' x) z) := by
  have : IsSepClosure k (AlgebraicClosure k') :=
    isSepClosure_of_isSeparable k k' (AlgebraicClosure k')
  set ι' : M' →ₐ[k'] AlgebraicClosure k' := IsAlgClosed.lift
  set ι : M →ₐ[k] AlgebraicClosure k' := (ι'.restrictScalars k).comp j
  apply ι'.injective
  have h1 := normResidueSymbol_apply_eq_localArtinMap ι' x (j z)
  have h2 := normResidueSymbol_apply_eq_localArtinMap ι (normUnits k k' x) z
  have h3 := localArtinMap_apply_of_algebra (Ω := AlgebraicClosure k') x
    (apply_mem_maximalAbelianExtension ι z)
  exact h1.trans (h3.trans h2.symm)

end Local

end

end GroundTheory.Global
