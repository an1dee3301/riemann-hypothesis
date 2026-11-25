module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Galois
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.FunctorialLocal
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Development.Core20Slim.GroundTheory.LocalFields.LocalArtinAbstractField
public import Init.Core
public import Init.Data.Function
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField SemiLocal AdeleBaseChange IdeleGroup
open scoped Pointwise

noncomputable section

section NormResidue

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] {M : Type*} [Field M] [Algebra k M] [FiniteDimensional k M] [IsGalois k M]
  [IsMulCommutative (M ≃ₐ[k] M)]

theorem normResidueSymbol_surjective : Function.Surjective (normResidueSymbol k M) := by
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  intro τ
  obtain ⟨x, hx⟩ := LocalField.surjective_localArtinMapOfField (K := k) (L := M) τ
  refine ⟨x, ?_⟩
  rw [← hx]
  exact congrArg (fun f : kˣ →* (M ≃ₐ[k] M) ↦ f x) normResidueSymbol_eq_localArtinMapOfField

end NormResidue

section Place

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (v : HeightOneSpectrum (𝓞 K))

theorem exists_localSymbol_eq (w : PlacesOver L v) {τ : L ≃ₐ[K] L}
    (hτ : τ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal) :
    ∃ x : (v.adicCompletion K)ˣ, localSymbol L v x = τ := by
  obtain ⟨x, hx⟩ := normResidueSymbol_surjective (decompositionMulEquiv v w.1 ⟨τ, hτ⟩)
  refine ⟨x, ?_⟩
  rw [localSymbol_eq_symbolAt L v w]
  change (((decompositionMulEquiv v w.1).symm
    (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x)) : L ≃ₐ[K] L) = τ
  rw [hx, MulEquiv.symm_apply_apply]


omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
theorem mk_finiteEmbedding_normUnits (w : PlacesOver L v) (z : (w.1.adicCompletion L)ˣ) :
    IdeleClassGroup.mk K (finiteEmbedding v
        (LocalField.normUnits (v.adicCompletion K) (w.1.adicCompletion L) z)) =
      ideleClassNorm K L (IdeleClassGroup.mk L (finiteEmbedding w.1 z)) := by
  rw [ideleClassNorm_mk, ideleNorm_finiteEmbedding]
  obtain ⟨w, hw⟩ := w
  have h := (below_eq_iff w v).2 hw
  subst h
  rfl

end Place

end

end GroundTheory.Global
