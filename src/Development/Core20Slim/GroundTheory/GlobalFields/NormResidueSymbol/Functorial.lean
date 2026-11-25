module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.FunctorialInfinite
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.AbstractUnique
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.Infinite
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdele
public import Development.Core20Slim.GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Order

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField AdeleBaseChange IdeleGroup

noncomputable section

variable {K K' L L' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L]
  [NumberField L] [Field L'] [NumberField L'] [Algebra K K'] [Algebra K L] [Algebra K L']
  [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']


variable (K) in
def restrictScalarsHom : (L' ≃ₐ[K'] L') →* (L' ≃ₐ[K] L') where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField K] [NumberField K'] [NumberField L'] in
@[simp]
theorem restrictScalarsHom_apply (σ : L' ≃ₐ[K'] L') : restrictScalarsHom K σ = σ.restrictScalars K :=
  rfl

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem restrictNormal_restrictScalars_ideleSymbol (x : IdeleGroup K') :
    ((ideleSymbol K' L' x).restrictScalars K).restrictNormal L =
      ideleSymbol K L (ideleNorm K K' x) := by
  have h := IdeleGroup.continuous_monoidHom_ext
    (ψ := (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).comp
      ((restrictScalarsHom K).comp (ideleSymbol K' L')))
    (ψ' := (ideleSymbol K L).comp (ideleNorm K K'))
    ((continuous_of_discreteTopology : Continuous ((AlgEquiv.restrictNormalHom (F := K)
      (K₁ := L') L).comp (restrictScalarsHom (L' := L') K))).comp (continuous_ideleSymbol L'))
    ((continuous_ideleSymbol L).comp (continuous_ideleNorm (K := K) (L := K')))
    (fun v' a ↦ by
      change ((ideleSymbol K' L' (finiteEmbedding v' a)).restrictScalars K).restrictNormal L =
        ideleSymbol K L (ideleNorm K K' (finiteEmbedding v' a))
      rw [ideleSymbol_finiteEmbedding, ideleNorm_finiteEmbedding, ideleSymbol_finiteEmbedding]
      exact restrictNormal_localSymbol_norm (below K v') v' a)
    (fun w' a ↦ by
      change ((ideleSymbol K' L' (infiniteEmbedding w' a)).restrictScalars K).restrictNormal L =
        ideleSymbol K L (ideleNorm K K' (infiniteEmbedding w' a))
      rw [ideleSymbol_infiniteEmbedding, ideleNorm_infiniteEmbedding, ideleSymbol_infiniteEmbedding]
      exact restrictNormal_infiniteLocalSymbol_norm w' a)
  exact congrArg (fun f : IdeleGroup K' →* (L ≃ₐ[K] L) ↦ f x) h

end

end GroundTheory.Global
